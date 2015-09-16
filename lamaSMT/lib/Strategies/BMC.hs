{-# LANGUAGE ViewPatterns #-}
module Strategies.BMC (BMC, assumeTrace, checkInvariant, bmcStep, assertPrecond) where

import Data.Natural
import NatInstance
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.IO.Class
import Control.Monad (when, liftM)

import Language.SMTLib2

import Lang.LAMA.Identifier

import Strategy
import LamaSMTTypes
import Definition
import Model (Model, getModel)
import TransformEnv
import Internal.Monads

data BMC = BMC
           { bmcDepth :: Maybe Natural
           , bmcPrintProgress :: Bool }

instance StrategyClass BMC where
  defaultStrategyOpts = BMC Nothing False

  readOption (stripPrefix "depth=" -> Just d) s =
    case d of
      "inf" -> s { bmcDepth = Nothing }
      _ -> s { bmcDepth = Just $ read d }
  readOption "progress" s =
    s { bmcPrintProgress = True }
  readOption o _ = error $ "Invalid BMC option: " ++ o

  check natAnn s env defs =
    let base = 0
    in do baseDef <- liftSMT . defConst $ constantAnn base natAnn
          check' natAnn s env defs (Map.singleton base baseDef) base baseDef

assumeTrace :: (Ident i, MonadSMT m) => ProgDefs i -> VarEnv i -> m ()
assumeTrace defs env =
  assertDefs env (flowDef defs) >>
  assertPrecond env (precondition defs)

bmcStep :: (Ident i, MonadSMT m) =>
        VarEnv i   
        -> ProgDefs i
        -> Map Natural StreamPos
        -> StreamPos
        -> m (Maybe (Model i))
bmcStep env defs pastIndices iDef =
  do assumeTrace defs env
     let invs = invariantDef defs
     liftSMT . stack
       $ checkInvariant env invs >>=
       checkGetModel (getModel env) pastIndices

check' :: Ident i =>
       SMTAnnotation Natural
       -> BMC
       -> VarEnv i
       -> ProgDefs i
       -> Map Natural StreamPos
       -> Natural
       -> StreamPos
       -> SMTErr (StrategyResult i)
check' natAnn s env defs pastIndices i iDef =
  do liftIO $ when (bmcPrintProgress s) (putStrLn $ "Depth " ++ show i)
     r <- bmcStep env defs pastIndices iDef
     case r of
       Nothing -> next (check' natAnn s env defs) natAnn s pastIndices i iDef
       Just m -> return $ Failure i m

assertDefs :: (Ident i, MonadSMT m) => VarEnv i -> [Definition i] -> m ()
assertDefs i = mapM_ (assertDef i)

assertDef :: (Ident i, MonadSMT m) => VarEnv i -> Definition i -> m ()
assertDef = assertDefinition id

assertPrecond :: (Ident i, MonadSMT m) => VarEnv i -> Definition i -> m ()
assertPrecond = assertDefinition id

-- | Returns true, if the invariant holds
checkInvariant :: (Ident i, MonadSMT m) => VarEnv i -> Definition i -> m Bool
checkInvariant i p = liftSMT $ assertDefinition not' i p >> liftM not checkSat

checkGetModel :: MonadSMT m =>
              (Map Natural StreamPos -> SMT (Model i))
              -> Map Natural StreamPos
              -> Bool
              -> m (Maybe (Model i))
checkGetModel getModel indices r = liftSMT $
  if r then return Nothing else fmap Just $ getModel indices

next :: (Map Natural StreamPos
             -> Natural
             -> SMTExpr Natural
             -> SMTErr (StrategyResult i)
        )
        -> SMTAnnotation Natural
        -> BMC
        -> Map Natural StreamPos
        -> Natural
        -> SMTExpr Natural
        -> SMTErr (StrategyResult i)
next checkCont natAnn s pastIndices i iDef =
  do let i' = succ i
     iDef' <- liftSMT . defConst$ succ' natAnn iDef
     let pastIndices' = Map.insert i' iDef' pastIndices
     case bmcDepth s of
       Nothing -> checkCont pastIndices' i' iDef'
       Just l ->
         if i' < l
         then checkCont pastIndices' i' iDef'
         else return Success
