{-# LANGUAGE ViewPatterns #-}
module Strategies.BMC where

import Data.Natural
import Data.List (stripPrefix)

import Language.SMTLib2

import Strategy
import Transform

data BMC = BMC { bmcDepth :: Maybe Natural }

instance StrategyClass BMC where
  defaultStrategyOpts = BMC Nothing

  readOptions (stripPrefix "depth=" -> Just d) s =
    case d of
      "inf" -> s { bmcDepth = Nothing }
      _ -> s { bmcDepth = Just $ read d }
  readOptions o _ = error $ "Invalid BMC option: " ++ o

  check s defs =
    let base = 0
    in do baseDef <- liftSMT . defConst $ constant base
          check' s defs base baseDef

check' :: BMC -> ProgDefs -> Natural -> SMTExpr Natural -> SMTErr Bool
check' s defs i iDef =
  do liftSMT $ assertDefs iDef (flowDef defs)
     liftSMT $ assertPrecond iDef (precondition defs)
     r <- liftSMT . stack . checkInvariant iDef $ invariantDef defs
     if r
       then return False
       else next (check' s defs) s i iDef

assertDefs :: SMTExpr Natural -> [Definition] -> SMT ()
assertDefs i = mapM_ (assertDef i)

assertDef :: SMTExpr Natural -> Definition -> SMT ()
assertDef i f = assert $ app f i

assertPrecond :: SMTExpr Natural -> Definition -> SMT ()
assertPrecond i f = assert $ app f i

checkInvariant :: SMTExpr Natural -> Definition -> SMT Bool
checkInvariant i p =
  do assert . not' $ app p i
     checkSat

next :: (Natural -> SMTExpr Natural -> SMTErr Bool)
        -> BMC -> Natural -> SMTExpr Natural -> SMTErr Bool
next f s i iDef =
  do let i' = succ i
     iDef' <- liftSMT . defConst $ succ' iDef
     case bmcDepth s of
       Nothing -> f i' iDef'
       Just l ->
         if i' < l
         then f i' iDef'
         else return True