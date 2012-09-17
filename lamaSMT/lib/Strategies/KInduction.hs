{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module Strategies.KInduction where

import Data.Natural
import NatInstance
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.State (MonadState(..), StateT, evalStateT, modify)
import Control.Monad.IO.Class
import Control.Monad (when)
import Control.Monad.Error (throwError)

import Language.SMTLib2

import Strategy
import LamaSMTTypes
import Definition
import Model (Model)
import Strategies.BMC

data KInduct = KInduct
               { depth :: Maybe Natural
               , printProgress :: Bool }

instance StrategyClass KInduct where
  defaultStrategyOpts = KInduct Nothing False

  readOption (stripPrefix "depth=" -> Just d) s =
    case d of
      "inf" -> s { depth = Nothing }
      _ -> s { depth = Just $ read d }
  readOption "progress" s =
    s { printProgress = True }
  readOption o _ = error $ "Invalid k-induction option: " ++ o

  check natAnn s getModel defs =
    let baseK = 0
    in do baseKDef <- liftSMT . defConstAnn natAnn $ constantAnn baseK natAnn
          baseNDef <- liftSMT $ natVar natAnn
          assumeTrace defs baseNDef
          let s0 = InductState baseK baseKDef baseNDef (Map.singleton baseK baseKDef)
          (flip evalStateT s0) $ check' natAnn s getModel defs

checkStep :: MonadSMT m => ProgDefs -> StreamPos -> m Bool
checkStep defs iDef =
  do assumeTrace defs iDef
     let invs = invariantDef defs
     liftSMT . stack $ checkInvariant iDef invs

-- | Holds current depth k and definitions of last k and n
data InductState = InductState
                   { kVal :: Natural
                   , kDef :: StreamPos -- ^ SMT expression for k
                   , nDef :: StreamPos -- ^ SMT expression for n
                   , pastKs :: Map Natural StreamPos }
type KInductM = StateT InductState SMTErr

check' :: SMTAnnotation Natural
          -> KInduct -> (Map Natural StreamPos -> SMT (Model i))
          -> ProgDefs -> KInductM (Maybe (Natural, Model i))
check' natAnn s getModel defs =
  do InductState{..} <- get
     liftIO $ when (printProgress s) (putStrLn $ "Depth " ++ show kVal)
     rBMC <- bmcStep getModel defs pastKs kDef
     case rBMC of
       Just m -> return $ Just (kVal, m)
       Nothing ->
         do n1 <- liftSMT . defConstAnn natAnn $ succ' natAnn nDef
            modify $ \indSt -> indSt { nDef = n1 }
            assertPrecond nDef $ invariantDef defs
            r <- checkStep defs n1
            if r then return Nothing else next (check' natAnn s getModel defs) natAnn s

next :: KInductM (Maybe (Natural, Model i)) -> SMTAnnotation Natural -> KInduct -> KInductM (Maybe (Natural, Model i))
next checkCont natAnn s =
  do indState@InductState {..} <- get
     let k' = succ kVal
     kDef' <- liftSMT . defConstAnn natAnn $ succ' natAnn kDef
     let pastKs' = Map.insert k' kDef' pastKs
     put $ indState { kVal = k', kDef = kDef', pastKs = pastKs' }
     case depth s of
       Nothing -> checkCont
       Just l ->
         if k' < l
         then checkCont
         else throwError $ "Cancelled induction. Found no proof within given depth"