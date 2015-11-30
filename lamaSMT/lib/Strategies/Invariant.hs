{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module Strategies.Invariant where

import Debug.Trace

import Lang.LAMA.Types

import Data.Natural
import NatInstance
import Data.List (stripPrefix, partition)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.State (MonadState(..), StateT, evalStateT, modify)
import Control.Monad.Writer (MonadWriter(..), WriterT, runWriterT)
import Control.Monad.IO.Class
import Control.Monad (when, filterM)
import Control.Arrow ((&&&))

import Language.SMTLib2

import Strategy
import LamaSMTTypes
import Definition
import TransformEnv
import Model (Model, getModel)
import Strategies.BMC
import Internal.Monads

data GenerateHints =
     NoHints
     | LastInductionStep
     | AllInductionSteps
data Invar = Invar
               { depth :: Maybe Natural
               , printProgress :: Bool
               , printInvStats :: Bool
               , generateHints :: GenerateHints }

instance StrategyClass Invar where
  defaultStrategyOpts = Invar Nothing False False NoHints

  readOption (stripPrefix "depth=" -> Just d) indOpts =
    case d of
      "inf" -> indOpts { depth = Nothing }
      _     -> indOpts { depth = Just $ read d }
  readOption "progress" indOpts =
    indOpts { printProgress = True }
  readOption "invariant-stats" indOpts =
    indOpts { printInvStats = True }
  readOption (stripPrefix "hints" -> Just r) indOpts =
    case (stripPrefix "=" r) of
         Nothing    -> indOpts { generateHints = LastInductionStep }
         Just which -> case which of
              "all"  -> indOpts { generateHints = AllInductionSteps }
              "last" -> indOpts { generateHints = LastInductionStep }
              _      -> error $ "Invalid hint option: " ++ which
  readOption o _ = error $ "Invalid k-induction option: " ++ o

  check indOpts env defs =
    let baseK = 0
        vars  = varList env
    in do k1  <- freshVars vars
          n0  <- freshVars vars
          n1  <- freshVars vars
          assumeTrace defs (n0, n1)
          let s0 = InductState baseK (vars, k1) (n0, n1) $ PosetGraph [map fst . filter (\(x,y) -> (mod y 1) == 0) $ zip (instSetBool env) [1..]] []
          (r, hints) <- runWriterT
                $ (flip evalStateT s0)
                $ check' indOpts (getModel $ varEnv env) defs (Map.singleton baseK vars)
          case r of
               Unknown what h -> return $ Unknown what (h ++ hints)
               _ -> return r

-- | Checks the induction step and returns true if the invariant could be
-- proven
checkStep :: ProgDefs -> ([TypedExpr], [TypedExpr]) -> SMT Bool
checkStep defs vars =
  do assumeTrace defs vars
     let invs = invariantDef defs
     checkInvariant vars invs

-- | Holds current depth k and definitions of last k and n
data InductState = InductState
                   { kVal     :: Natural
                   , kDefs    :: ([TypedExpr], [TypedExpr])
                   , nDefs    :: ([TypedExpr], [TypedExpr])
                   , binPoset :: PosetGraph }
type KInductM i = StateT InductState (WriterT (Hints i) SMTErr)

-- | Checks the program against its invariant. If the invariant
-- does not hold in the base case, then a model is returned.
-- If the base case is fine, but the induction step is not, we
-- call next, which increases k. Finally, if also the induction
-- step can be proven, Nothing is returned.
check' :: Invar
       -> (Map Natural [TypedExpr] -> SMT (Model i))
       -> ProgDefs
       -> Map Natural [TypedExpr]
       -> KInductM i (StrategyResult i)
check' indOpts getModel defs pastVars =
  do InductState{..} <- get
     liftIO $ when (printProgress indOpts) (putStrLn $ "Depth " ++ show kVal)
     liftIO $ when (printInvStats indOpts) (putStrLn $ "Boolean Invariants:\n" ++ (show $ length $ vertices binPoset) ++ " Node(s) with\n" ++ (show $ length $ concat $ vertices binPoset) ++ " Element(s) and\n" ++ (show $ length $ edges binPoset) ++ " Edge(s)\n")
     rBMC <- bmcStep getModel defs pastVars kDefs
     case rBMC of
       Just m -> return $ Failure kVal m
       Nothing ->
         do binPoset' <- filterC binPoset kDefs
            modify $ \indSt -> indSt { binPoset = binPoset' }
            let n0 = fst nDefs
                n1 = snd nDefs
            n2 <- freshVars n1
            assertPrecond (n0, n1) $ invariantDef defs
            modify $ \indSt -> indSt { nDefs = (n1, n2) }
            (indSuccess, hints) <- liftSMT . stack $
              do r <- checkStep defs (n1, n2)
                 h <- retrieveHints (getModel pastVars) indOpts kVal r
                 return (r, h)
            tell hints
            let k' = succ kVal
            --if indSuccess
               --then return Success
               --else case depth indOpts of
            case depth indOpts of
              Nothing -> cont k' pastVars
              Just l  ->
                if k' > l
                  then return $ Unknown ("Cancelled induction. Found no"
                                           ++" proof within given depth")
                                 []
                  else cont k' pastVars
  where
    cont k' pastVars =
      do indState@InductState{..} <- get
         let k1 = snd kDefs
             pastVars' = Map.insert k' k1 pastVars
         k2 <- freshVars k1
         put $ indState { kVal = k', kDefs = (k1, k2) }
         check' indOpts getModel defs pastVars'

filterC :: MonadSMT m => PosetGraph -> ([TypedExpr], [TypedExpr]) -> m PosetGraph
filterC g@(PosetGraph v e) args = liftSMT $ do push
                                               assertPosetGraph args g
                                               r  <- checkSat
                                               trace (show r) $ if r
                                                 then do v0' <- mapM (filterM (\a -> evalTerm args a >>= return . not)) v
                                                         v1' <- mapM (filterM $ evalTerm args) v
                                                         pop
                                                         return ${- trace (show v0') $ trace (show v1') $-} buildNextGraph (v0', v1') e
                                                  else pop >> return g
-- | If requested, gets a model for the induction step
retrieveHints :: SMT (Model i)
              -> Invar
              -> Natural
              -> Bool
              -> SMT [(Hint i)]
retrieveHints getModel indOpts k success =
  case (generateHints  &&& depth) indOpts of
       (NoHints          , _      ) -> return []
       (LastInductionStep, Nothing) -> return []
       (LastInductionStep, Just l ) ->
         if not success && succ k > l
         then getModel >>= \m -> return [Hint (show k) m]
         else return []
       (AllInductionSteps, _      ) ->
         getModel >>= \m -> return [Hint (show k) m]
