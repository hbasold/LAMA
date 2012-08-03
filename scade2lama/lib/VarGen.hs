{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module VarGen (VarGenT, VarGen, evalVarGenT, evalVarGen, MonadVarGen(..)) where

import Control.Monad.State
import Data.Functor.Identity

import Control.Monad.Reader (ReaderT)

newtype VarGenT m a = VarGenT { runVarGenT :: StateT Int m a }
type VarGen = VarGenT Identity

evalVarGenT :: Monad m => VarGenT m a -> Int -> m a
evalVarGenT = evalStateT . runVarGenT

evalVarGen :: VarGen a -> Int -> a
evalVarGen m = runIdentity . (evalVarGenT m)

instance Functor m => Functor (VarGenT m) where
  fmap f = VarGenT . fmap f . runVarGenT

instance Monad m => Monad (VarGenT m) where
  return = VarGenT . return
  m >>= f = VarGenT $ (runVarGenT m) >>= (runVarGenT . f)

instance MonadTrans VarGenT where
  lift = VarGenT . lift

class Monad m => MonadVarGen m where
  newVar :: String -> m String

instance Monad m => MonadVarGen (VarGenT m) where
  newVar x =
    do i <- getNextCnt
       return $ x ++ "_" ++ show i
    where getNextCnt = VarGenT $ state $ \i -> (i, i+1)

instance MonadVarGen m => MonadVarGen (ReaderT r m) where
  newVar = lift . newVar
  
instance MonadVarGen m => MonadVarGen (StateT r m) where
  newVar = lift . newVar