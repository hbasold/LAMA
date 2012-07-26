{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Strategy where

import Data.Map (Map)
import Data.Natural
import Control.Monad.Error

import Language.SMTLib2

import Transform
import Model

type SMTErr = ErrorT String SMT

data Strategy = forall s. StrategyClass s => Strategy s

class StrategyClass s where
  defaultStrategyOpts :: s
  readOptions :: String -> s -> s
  check :: s -> (Map Natural StreamPos -> SMT (Model i)) -> ProgDefs -> SMTErr (Maybe (Model i))

checkWithModel :: Strategy -> ProgDefs -> VarEnv i -> SMTErr (Maybe (Model i))
checkWithModel (Strategy s) d env = check s (getModel env) d

readOptions' :: String -> Strategy -> Strategy
readOptions' o (Strategy s) = Strategy $ readOptions o s