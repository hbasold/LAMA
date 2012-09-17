{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Strategy where

import Data.Map (Map)
import Data.Natural
import Control.Monad.Error

import Language.SMTLib2

import LamaSMTTypes
import Definition
import TransformEnv
import Model

type SMTErr = ErrorT String SMT

data Strategy = forall s. StrategyClass s => Strategy s

class StrategyClass s where
  defaultStrategyOpts :: s
  readOption :: String -> s -> s
  check :: SMTAnnotation Natural
           -> s
           -> (Map Natural StreamPos -> SMT (Model i))
           -> ProgDefs -> SMTErr (Maybe (Natural, Model i))

checkWithModel :: SMTAnnotation Natural -> Strategy -> ProgDefs -> VarEnv i -> SMTErr (Maybe (Natural, Model i))
checkWithModel natAnn (Strategy s) d env = check natAnn s (getModel env) d

readOptions' :: String -> Strategy -> Strategy
readOptions' o (Strategy s) = Strategy $ readOption o s