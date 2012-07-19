{-# LANGUAGE ViewPatterns #-}
module Strategies.BMC where

import Data.Natural
import Data.List (stripPrefix)
import Data.Sequence as Seq

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
          check' s getModel defs (Seq.singleton baseDef) base baseDef

check' :: BMC -> (Seq StreamPos -> SMT (Model i))
          -> ProgDefs -> Seq StreamPos -> Natural -> StreamPos -> SMTErr (Maybe (Model i))
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
assertDef i f = assert $ app f i

assertPrecond :: SMTExpr Natural -> Definition -> SMT ()
assertPrecond i f = assert $ app f i

checkInvariant :: SMTExpr Natural -> Definition -> SMT Bool
checkInvariant i p =
  do assert . not' $ app p i
     checkSat

checkGetModel :: (Seq StreamPos -> SMT (Model i)) -> Seq StreamPos -> Bool -> SMT (Maybe (Model i))
checkGetModel getModel indices r =
  if r then fmap Just $ getModel indices else return Nothing

next :: (Seq StreamPos -> Natural -> SMTExpr Natural -> SMTErr (Maybe (Model i)))
        -> BMC -> Seq StreamPos -> Natural -> SMTExpr Natural -> SMTErr (Maybe (Model i))
next f s is i iDef =
  do let i' = succ i
     iDef' <- liftSMT . defConst $ succ' iDef
     let is' = is |> iDef'
     case bmcDepth s of
       Nothing -> f is' i' iDef'
       Just l ->
         if i' < l
         then f is' i' iDef'
         else return Nothing