{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Wrapping where

import Control.Arrow (Arrow(..), Kleisli(..))

class Unpack p u | p -> u where
  unpack :: p -> u

{-
see: http://www.haskell.org/pipermail/libraries/2008-January/008917.html
ala :: Unpack p' u' =>
       (u -> p) -> ((a -> p) -> (a' -> p')) ->
       (a -> u) -> a' -> u'
ala pack mapper tr =
  unpack . mapper (pack . tr)
-}

ala :: Unpack p' u' =>
       (u -> p) -> (p -> p') -> u -> u'
ala pack mapper = unpack . mapper . pack

instance Unpack (Kleisli m a b) (a -> m b) where
  unpack = runKleisli

firstM :: Monad m => (a -> m b) -> (a, c) -> m (b, c)
firstM = ala Kleisli first

fanoutM :: Monad m => (a -> m b) -> (a -> m b') -> a -> m (b, b')
fanoutM f = ala Kleisli ((Kleisli f) &&&)
