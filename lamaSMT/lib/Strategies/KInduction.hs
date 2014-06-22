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
import Model (Model)
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

  check natAnn indOpts getModel defs =
    let baseK = 0
    in do baseKDef <- liftSMT . defConst $ constantAnn baseK natAnn
          baseNDef <- liftSMT $ varAnn natAnn
          assumeTrace defs baseNDef
          let s0 = InductState baseK baseKDef
                               baseNDef (Map.singleton baseK baseKDef)
          (r, hints) <- runWriterT
                $ (flip evalStateT s0)
                $ check' natAnn indOpts getModel defs
          case r of
               Unknown what h -> return $ Unknown what (h ++ hints)
               _ -> return r

-- | Checks the induction step and returns true if the invariant could be
-- proven
checkStep :: ProgDefs -> StreamPos -> SMT Bool
checkStep defs iDef =
  do assumeTrace defs iDef
     let invs = invariantDef defs
     checkInvariant iDef invs

-- | Holds current depth k and definitions of last k and n
data InductState = InductState
                   { kVal :: Natural
                   , kDef :: StreamPos -- ^ Induction depth k (in solver)
                   , nDef :: StreamPos -- ^ Induction variable n (in solver)
                   , pastKs :: Map Natural StreamPos }
type KInductM i = StateT InductState (WriterT (Hints i) SMTErr)

-- | Checks the program against its invariant. If the invariant
-- does not hold in the base case, then a model is returned.
-- If the base case is fine, but the induction step is not, we
-- call next, which increases k. Finally, if also the induction
-- step can be proven, Nothing is returned.
check' :: SMTAnnotation Natural
       -> KInduct
       -> (Map Natural StreamPos -> SMT (Model i))
       -> ProgDefs
       -> KInductM i (StrategyResult i)
check' natAnn indOpts getModel defs =
  do InductState{..} <- get
     liftIO $ when (printProgress indOpts) (putStrLn $ "Depth " ++ show kVal)
     rBMC <- bmcStep getModel defs pastKs kDef
     case rBMC of
       Just m -> return $ Failure kVal m
       Nothing ->
         do n1 <- liftSMT . defConst $ succ' natAnn nDef
            modify $ \indSt -> indSt { nDef = n1 }
            assertPrecond nDef $ invariantDef defs
            (indSuccess, hints) <- liftSMT . stack $
              do r <- checkStep defs n1
                 h <- retrieveHints (getModel pastKs) indOpts kVal r
                 return (r, h)
            tell hints
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
         kDef' <- liftSMT . defConst $ succ' natAnn kDef
         let pastKs' = Map.insert k' kDef' pastKs
         put $ indState { kVal = k', kDef = kDef', pastKs = pastKs' }
         check' natAnn indOpts getModel defs

--     r <- checkInvariant iDef invs >>=
--          checkGetModel getModel pastIndices
{-
        do getOpt
             m <- getModel
             tell m
             return False
-}

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

-- | Checks whether the induction step could be proven. If not, then it can
-- return Nothing, to indicate that the next induction depth should be tried.
-- If the induction depth attained its bound, we stop with a StrategyResult.
-- In case of failure, the current model might be recorded/returned as hint.
-- If the step could be proven, Success is returned.
-- checkStepResult :: SMTAnnotation Natural
--      -> KInduct
--      -> Natural
--      -> Maybe (Hint i)
--      -> Bool
--      -> SMT (Maybe (StrategyResult i))
-- checkStepResult = undefined
{-

-- | Checks whether the induction step could be proven. If not, then it can
-- return Nothing, to indicate that the next induction depth should be tried.
-- If the induction depth attained its bound, we stop with a StrategyResult.
-- In case of failure, the current model might be recorded/returned as hint.
-- If the step could be proven, Success is returned.
checkStepResult :: (Map Natural StreamPos -> SMT (Model i))
     -> SMTAnnotation Natural
     -> KInduct
     -> Natural
     -> Bool
     -> KInductM i (Maybe (StrategyResult i))
checkStepResult getModel natAnn indOpts k' result =
  if result
  then return $ Just Success
  else
       case (generateHints    &&& depth) indOpts of
            (NoHints          , Nothing) -> return Nothing
            (NoHints          , Just l)  -> checkCont l k' (return [])
            (LastInductionStep, Nothing) -> return Nothing
            (LastInductionStep, Just l)  ->
              checkCont l k' (retrieveModel
                                >>= \m -> return [Hint (show kVal) m])
            (AllInductionSteps, Nothing) ->
              do m <- retrieveModel
                 tell [Hint (show kVal) m]
                 return Nothing
            (AllInductionSteps, Just l)  ->
              do m <- retrieveModel
                 tell $ [Hint (show kVal) m]
                 checkCont l k' (return [Hint (show kVal) m])
  where
    checkCont l k' m =
      if k' < l
      then return Nothing
      else m >>= \r ->
           return $ Just $ Unknown
                    "Cancelled induction. Found no proof within given depth"
                    r
    retrieveModel =
      do InductState{..} <- get
         liftSMT $ getModel pastKs
-}
{-
getModelAndContinue
     :: (Map Natural StreamPos -> SMT (Model i))
     -> KInductM i (StrategyResult i)
     -> SMTAnnotation Natural
     -> KInduct
     -> KInductM i (StrategyResult i)
getModelAndContinue getModel inductCont natAnn indOpts =
  do InductState {..} <- get
     let k' = succ kVal
     case (generateHints    &&& depth) indOpts of
          (NoHints          , Nothing) -> cont k'
          (NoHints          , Just l)  -> checkCont l k' (return [])
          (LastInductionStep, Nothing) -> cont k'
          (LastInductionStep, Just l)  ->
            checkCont l k' (retrieveModel >>= \m -> return [Hint (show kVal) m])
          (AllInductionSteps, Nothing) ->
            do m <- retrieveModel
               tell [Hint (show kVal) m]
               cont k'
          (AllInductionSteps, Just l)  ->
            do m <- retrieveModel
               tell $ [Hint (show kVal) m]
               checkCont l k' (return [Hint (show kVal) m])
  where
    cont k' =
      do indState@InductState {..} <- get
         kDef' <- liftSMT . defConst $ succ' natAnn kDef
         let pastKs' = Map.insert k' kDef' pastKs
         put $ indState { kVal = k', kDef = kDef', pastKs = pastKs' }
         inductCont
    checkCont l k' m =
      if k' < l
      then cont k'
      else m >>= \r ->
           return $ Unknown
                    "Cancelled induction. Found no proof within given depth"
                    r
--    retrieveModel :: (MonadSMT m, MonadState InductState) => m (Model i)
    retrieveModel =
      do InductState{..} <- get
         liftSMT $ getModel pastKs
-}
