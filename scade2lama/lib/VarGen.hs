{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module VarGen (VarGenT, VarGen, evalVarGenT, evalVarGen, runInVarGenT, MonadVarGen(..)) where

import Control.Monad.State
import Data.Functor.Identity
import Numeric

import Control.Applicative
import Control.Monad.Reader (ReaderT)
import Control.Monad.Writer (WriterT)
import Control.Monad.Error (ErrorT, Error)
import Data.Monoid

newtype VarGenT m a = VarGenT { runVarGenT :: StateT Int m a }
                    deriving (Functor, Monad, MonadTrans, Applicative, MonadIO, MonadPlus)
type VarGen = VarGenT Identity

evalVarGenT :: Monad m => VarGenT m a -> Int -> m a
evalVarGenT = evalStateT . runVarGenT

evalVarGen :: VarGen a -> Int -> a
evalVarGen m = runIdentity . (evalVarGenT m)

runInVarGenT :: Monad m => VarGen a -> VarGenT m a
runInVarGenT a =
  do i <- VarGenT $ get
     let (x, i') = (flip runState i) $ runVarGenT a
     VarGenT $ put i'
     return x

class Monad m => MonadVarGen m where
  newVar :: String -> m String

instance Monad m => MonadVarGen (VarGenT m) where
  newVar x =
    do i <- getNextCnt
       return . (x ++) . ("_" ++) . showHex i $ ""
    where getNextCnt = VarGenT $ state $ \i -> (i, i+1)

instance MonadVarGen m => MonadVarGen (ReaderT r m) where
  newVar = lift . newVar
  
instance MonadVarGen m => MonadVarGen (StateT s m) where
  newVar = lift . newVar

instance (Monoid w, MonadVarGen m) => MonadVarGen (WriterT w m) where
  newVar = lift . newVar

instance (Error e, MonadVarGen m) => MonadVarGen (ErrorT e m) where
  newVar = lift . newVar