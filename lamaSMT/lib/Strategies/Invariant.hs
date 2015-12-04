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
import Data.Maybe (fromMaybe, isJust, fromJust)

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
          let s0 = InductState baseK (vars, k1) (n0, n1) (Just $ PosetGraph [map fst . filter (\(x,y) -> (mod y 1) == 0) $ zip (instSetBool env) [1..]] []) Nothing
          (r, hints) <- runWriterT
                $ (flip evalStateT s0)
                $ check' indOpts (getModel $ varEnv env) defs (Map.singleton baseK vars) [n0]
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
                   , binPoset :: Maybe PosetGraph
                   , binInv   :: Maybe PosetGraph }
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
       -> [[TypedExpr]]
       -> KInductM i (StrategyResult i)
check' indOpts getModel defs pastVars pastNs =
  do InductState{..} <- get
     liftIO $ when (printProgress indOpts) (putStrLn $ "Depth " ++ show kVal)
     let statGraph = fromMaybe (fromMaybe (PosetGraph [] []) binInv) binPoset
     let statMessage = if (isJust binPoset) then "Possible " else "Actual "
     liftIO $ when (printInvStats indOpts) (putStrLn $ statMessage ++ "Boolean Invariants:\n" ++ (show $ length $ vertices statGraph) ++ " Node(s) with\n" ++ (show $ length $ concat $ vertices statGraph) ++ " Element(s) and\n" ++ (show $ length $ edges statGraph) ++ " Edge(s)\n")
     rBMC <- bmcStep getModel defs pastVars kDefs
     case rBMC of
       Just m -> return $ Failure kVal m
       Nothing ->
         do let n0 = fst nDefs
                n1 = snd nDefs
                pastNs' = pastNs ++ [n1]
            n2 <- freshVars n1
            when (isJust binPoset) $
              do binPoset' <- filterC (fromJust binPoset) kDefs
                 case binPoset' of
                   Just b  -> modify $ \indSt -> indSt { binPoset = Just b }
                   Nothing -> do binInv' <- checkInvariantStep (fromJust binPoset) (n1,n2) pastNs defs
                                 assertPosetGraph id (n1, n2) binInv'
                                 modify $ \indSt -> indSt { binPoset = Nothing, binInv = Just binInv' }
            assertPrecond (n0, n1) $ invariantDef defs
            when (isJust binInv) $ assertPosetGraph id (n1, n2) $ fromJust binInv
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
              Nothing -> cont k' pastVars pastNs'
              Just l  ->
                if k' > l
                  then return $ Unknown ("Cancelled induction. Found no"
                                           ++" proof within given depth")
                                 []
                  else cont k' pastVars pastNs'
  where
    cont k' pastVars pNs =
      do indState@InductState{..} <- get
         let k1 = snd kDefs
             pastVars' = Map.insert k' k1 pastVars
         k2 <- freshVars k1
         put $ indState { kVal = k', kDefs = (k1, k2) }
         check' indOpts getModel defs pastVars' pNs

filterC :: MonadSMT m => PosetGraph -> ([TypedExpr], [TypedExpr]) -> m (Maybe PosetGraph)
filterC g@(PosetGraph v e) args =
  liftSMT $ do push
               assertPosetGraph not' args g
               r  <- checkSat
               trace (show r) $ if r
                 then do v0' <- mapM (filterM (\a -> evalTerm args a >>= return . not)) v
                         v1' <- mapM (filterM $ evalTerm args) v
                         pop
                         return $ Just $ buildNextGraph (v0', v1') e
                  else pop >> return Nothing

checkInvariantStep :: MonadSMT m => PosetGraph -> ([TypedExpr], [TypedExpr]) -> [[TypedExpr]] -> ProgDefs -> m PosetGraph
checkInvariantStep g args pastVars defs = liftSMT $ do
  push
  mapM (\a -> assertPosetGraph id (a,a) g) $ pastVars
  assumeTrace defs args
  g' <- checkInvariantStep' g
  pop
  return g'
  where
    checkInvariantStep' graph@(PosetGraph v e) = do
      push
      assertPosetGraph not' args graph
      r <- checkSat
      trace (show r) $ if r
        then do v0' <- mapM (filterM (\a -> evalTerm args a >>= return . not)) v
                v1' <- mapM (filterM $ evalTerm args) v
                pop
                graph' <- checkInvariantStep' $ buildNextGraph (v0', v1') e
                return graph'
         else pop >> return graph

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
