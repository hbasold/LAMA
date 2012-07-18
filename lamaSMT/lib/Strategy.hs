{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Strategy where

import Control.Monad.Error

import Language.SMTLib2
import Transform

type SMTErr = ErrorT String SMT

class Strategy s where
  check :: s -> ProgDefs -> SMTErr ()