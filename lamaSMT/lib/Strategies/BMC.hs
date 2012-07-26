{-# LANGUAGE ViewPatterns #-}
module Strategies.BMC where

import Data.Natural
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.Map (Map)

import Language.SMTLib2

import Strategy
import Transform
import Model (Model)

data BMC = BMC { bmcDepth :: Maybe Natural }

instance StrategyClass BMC where
  defaultStrategyOpts = BMC Nothing

  readOptions (stripPrefix "depth=" -> Just d) s =
    case d of
      "inf" -> s { bmcDepth = Nothing }
      _ -> s { bmcDepth = Just $ read d }
  readOptions o _ = error $ "Invalid BMC option: " ++ o

  check s getModel defs =
    let base = 0
    in do baseDef <- liftSMT . defConst $ constant base
          check' s getModel defs (Map.singleton base baseDef) base baseDef

check' :: BMC -> (Map Natural StreamPos -> SMT (Model i))
          -> ProgDefs -> Map Natural StreamPos -> Natural -> StreamPos -> SMTErr (Maybe (Model i))
check' s getModel defs is i iDef =
  do liftSMT $ assertDefs iDef (flowDef defs)
     liftSMT $ assertPrecond iDef (precondition defs)
     let invs = invariantDef defs
     r <- liftSMT . stack $ (checkGetModel getModel is =<< checkInvariant iDef invs)
     case r of
       Nothing -> next (check' s getModel defs) s is i iDef
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
next f s is i iDef =
  do let i' = succ i
     iDef' <- liftSMT . defConst $ succ' iDef
     let is' = Map.insert i iDef' is
     case bmcDepth s of
       Nothing -> f is' i' iDef'
       Just l ->
         if i' < l
         then f is' i' iDef'
         else return Nothing