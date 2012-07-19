{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Strategy where

import Control.Monad.Error

import Language.SMTLib2

import Lang.LAMA.Identifier

import Transform
import Model

type SMTErr = ErrorT String SMT

data Strategy = forall s. StrategyClass s => Strategy s

class StrategyClass s where
  defaultStrategyOpts :: s
  readOptions :: String -> s -> s
  check :: s -> ProgDefs -> SMTErr Bool

checkWithModel :: (Ident i) => Strategy -> ProgDefs -> VarEnv i -> SMTErr (Maybe (Model i))
checkWithModel (Strategy s) d env =
  do ok <- check s d
     if ok then return Nothing else liftSMT . fmap Just $ getModel env

readOptions' :: String -> Strategy -> Strategy
readOptions' o (Strategy s) = Strategy $ readOptions o s