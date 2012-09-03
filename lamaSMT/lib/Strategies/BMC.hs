{-# LANGUAGE ViewPatterns #-}
module Strategies.BMC where

import Data.Natural
import NatInstance
import Data.List (stripPrefix)
import Data.List.Split (splitWhen)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (foldl')

import Control.Monad.IO.Class
import Control.Monad (when)

import Language.SMTLib2

import Strategy
import LamaSMTTypes
import Definition
import Model (Model)

data BMC = BMC
           { bmcDepth :: Maybe Natural
           , bmcPrintProgress :: Bool }

instance StrategyClass BMC where
  defaultStrategyOpts = BMC Nothing False

  readOptions os bmc = foldl' readOption bmc $ splitWhen (== ',') os
    where
      readOption s (stripPrefix "depth=" -> Just d) =
        case d of
          "inf" -> s { bmcDepth = Nothing }
          _ -> s { bmcDepth = Just $ read d }
      readOption s "progress" =
        s { bmcPrintProgress = True }
      readOption _ o = error $ "Invalid BMC option: " ++ o

  check s getModel defs =
    let base = 0
    in do baseDef <- liftSMT . defConst $ constant base
          check' s getModel defs (Map.singleton base baseDef) base baseDef

check' :: BMC -> (Map Natural StreamPos -> SMT (Model i))
          -> ProgDefs -> Map Natural StreamPos -> Natural -> StreamPos -> SMTErr (Maybe (Model i))
check' s getModel defs pastIndices i iDef =
  do liftIO $ when (bmcPrintProgress s) (putStrLn $ "Depth " ++ show i)
     liftSMT $ assertDefs iDef (flowDef defs)
     liftSMT $ assertPrecond iDef (precondition defs)
     let invs = invariantDef defs
     r <- liftSMT . stack $ (checkGetModel getModel pastIndices =<< checkInvariant iDef invs)
     case r of
       Nothing -> next (check' s getModel defs) s pastIndices i iDef
       Just m -> return $ Just m

assertDefs :: SMTExpr Natural -> [Definition] -> SMT ()
assertDefs i = mapM_ (assertDef i)

assertDef :: SMTExpr Natural -> Definition -> SMT ()
assertDef = assertDefinition id

assertPrecond :: SMTExpr Natural -> Definition -> SMT ()
assertPrecond = assertDefinition id

checkInvariant :: SMTExpr Natural -> Definition -> SMT Bool
checkInvariant i p = assertDefinition not' i p >> checkSat

checkGetModel :: (Map Natural StreamPos -> SMT (Model i)) -> Map Natural StreamPos -> Bool -> SMT (Maybe (Model i))
checkGetModel getModel indices r =
  if r then fmap Just $ getModel indices else return Nothing

next :: (Map Natural StreamPos -> Natural -> SMTExpr Natural -> SMTErr (Maybe (Model i)))
        -> BMC -> Map Natural StreamPos -> Natural -> SMTExpr Natural -> SMTErr (Maybe (Model i))
next checkCont s pastIndices i iDef =
  do let i' = succ i
     iDef' <- liftSMT . defConst $ succ' iDef
     let pastIndices' = Map.insert i iDef' pastIndices
     case bmcDepth s of
       Nothing -> checkCont pastIndices' i' iDef'
       Just l ->
         if i' < l
         then checkCont pastIndices' i' iDef'
         else return Nothing