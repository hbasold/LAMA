-- BNF Converter: Error Monad
-- Copyright (C) 2004  Author:  Aarne Ranta

-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module Lang.LAMA.Parser.ErrM where

-- the Error monad: like Maybe type with error msgs

import Control.Monad
import Control.Applicative

data Err a = Ok a | Bad String
  deriving (Read, Show, Eq, Ord)

instance Applicative Err where
  pure = Ok
  (<*>) = ap

instance Monad Err where
  return      = Ok
  fail        = Bad
  Ok a  >>= f = f a
  Bad s >>= _ = Bad s

instance Functor Err where
  fmap = liftM

instance MonadPlus Err where
  mzero = Bad "Err.mzero"
  mplus (Bad _) y = y
  mplus x       _ = x

instance Alternative Err where
    (<|>) = mplus
    empty = mzero
