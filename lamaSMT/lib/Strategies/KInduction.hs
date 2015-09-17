{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module Strategies.KInduction where

import Data.Natural
import NatInstance
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.State (MonadState(..), StateT, evalStateT, modify)
import Control.Monad.Writer (MonadWriter(..), WriterT, runWriterT)
import Control.Monad.IO.Class
import Control.Monad (when)
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
data KInduct = KInduct
               { depth :: Maybe Natural
               , printProgress :: Bool
               , generateHints :: GenerateHints }

instance StrategyClass KInduct where
  defaultStrategyOpts = KInduct Nothing False NoHints

  readOption (stripPrefix "depth=" -> Just d) indOpts =
    case d of
      "inf" -> indOpts { depth = Nothing }
      _     -> indOpts { depth = Just $ read d }
  readOption "progress" indOpts =
    indOpts { printProgress = True }
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
          let s0 = InductState baseK (vars, k1) (n0, n1)
          (r, hints) <- runWriterT
                $ (flip evalStateT s0)
                $ check' indOpts (getModel $ varEnv env) defs
          case r of
               Unknown what h -> return $ Unknown what (h ++ hints)
               _ -> return r

-- | Checks the induction step and returns true if the invariant could be
-- proven
checkStep :: ProgDefs -> ([SMTExpr Bool], [SMTExpr Bool]) -> SMT Bool
checkStep defs vars =
  do assumeTrace defs vars
     let invs = invariantDef defs
     checkInvariant vars invs

-- | Holds current depth k and definitions of last k and n
data InductState = InductState
                   { kVal  :: Natural
                   , kDefs :: ([SMTExpr Bool], [SMTExpr Bool])
                   , nDefs :: ([SMTExpr Bool], [SMTExpr Bool]) }
type KInductM i = StateT InductState (WriterT (Hints i) SMTErr)

-- | Checks the program against its invariant. If the invariant
-- does not hold in the base case, then a model is returned.
-- If the base case is fine, but the induction step is not, we
-- call next, which increases k. Finally, if also the induction
-- step can be proven, Nothing is returned.
check' :: KInduct
       -> (Map Natural StreamPos -> SMT (Model i))
       -> ProgDefs
       -> KInductM i (StrategyResult i)
check' indOpts getModel defs =
  do InductState{..} <- get
     liftIO $ when (printProgress indOpts) (putStrLn $ "Depth " ++ show kVal)
     rBMC <- bmcStep getModel defs kDefs
     case rBMC of
       False -> return $ Failure kVal
       True ->
         do let n0 = fst nDefs
                n1 = snd nDefs
            n2 <- freshVars n1
            assertPrecond (n0, n1) $ invariantDef defs
            modify $ \indSt -> indSt { nDefs = (n1, n2) }
            indSuccess <- liftSMT . stack $
              do r <- checkStep defs (n1, n2)
                 --h <- retrieveHints (getModel pastKs) indOpts kVal r
                 --return (r, h)
                 return r
            --tell hints
            let k' = succ kVal
            if indSuccess
               then return Success
               else case depth indOpts of
                    Nothing -> cont k'
                    Just l  ->
                      if k' > l
                      then return $ Unknown ("Cancelled induction. Found no"
                                              ++" proof within given depth")
                                    []
                      else cont k'
  where
    cont k' =
      do indState@InductState{..} <- get
         let k1 = snd kDefs
         k2 <- freshVars k1
         put $ indState { kVal = k', kDefs = (k1, k2) }
         check' indOpts getModel defs

-- | If requested, gets a model for the induction step
retrieveHints :: SMT (Model i)
              -> KInduct
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
