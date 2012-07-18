module Strategies.BMC where

import Data.Natural

import Language.SMTLib2

import Control.Monad.IO.Class

import Strategy
import Transform

data BMC = BMC { bmcDepth :: Int }

instance Strategy BMC where
  check s defs = liftSMT $
    do i <- defConst $ constant 0 :: SMT (SMTExpr Natural)
       assertDefs i (flowDef defs)
       r <- stack . checkInvariant i $ invariantDef defs
       liftIO $ print r

assertDefs :: SMTExpr Natural -> [Definition] -> SMT ()
assertDefs i = mapM_ (assertDef i)

assertDef :: SMTExpr Natural -> Definition -> SMT ()
assertDef i f = assert $ app f i

checkInvariant :: SMTExpr Natural -> Definition -> SMT Bool
checkInvariant i p =
  do assert . not' $ app p i
     checkSat