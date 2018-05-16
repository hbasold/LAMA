{-# LANGUAGE ScopedTypeVariables #-}

module Data.Graph.Inductive.MonadSupport where

import Data.Graph.Inductive.Graph

ufoldM :: forall m gr a b c. (Graph gr, Monad m) =>
          (Context a b -> c -> m c) -> c -> gr a b -> m c
ufoldM f z0 = ufold f' (return z0)
  where
    f' :: Context a b -> m c -> m c
    f' c z = z >>= f c

gmapM :: forall m gr a b c d. (DynGraph gr, Monad m) =>
         (Context a b -> m (Context c d)) -> gr a b -> m (gr c d)
gmapM f = ufold f' (return empty)
  where
    f' :: Context a b -> m (gr c d) -> m (gr c d)
    f' c g = do
      c' <- f c
      g' <- g
      return $ c' & g'

nmapM :: (DynGraph gr, Monad m) => (a -> m c) -> gr a b -> m (gr c b)
nmapM f = gmapM f'
  where f' (i, n, l, o) = f l >>= \l' -> return (i, n, l', o)
