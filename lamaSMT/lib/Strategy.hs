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
data Hint i = Hint { hintDescr :: String, hintModel :: Model i }
type Hints i = [Hint i]
data StrategyResult i =
     Success
     | Failure Natural-- (Model i)
     | Unknown String (Hints i)

data Strategy = forall s. StrategyClass s => Strategy s

class StrategyClass s where
  defaultStrategyOpts :: s
  readOption :: String -> s -> s
  check :: SMTAnnotation Natural
           -> s
           -> Env i
           -> ProgDefs
           -> SMTErr (StrategyResult i)

checkWithModel :: SMTAnnotation Natural
               -> Strategy
               -> ProgDefs
               -> Env i
               -> SMTErr (StrategyResult i)
checkWithModel natAnn (Strategy s) d env = check natAnn s env d

readOptions' :: String -> Strategy -> Strategy
readOptions' o (Strategy s) = Strategy $ readOption o s
