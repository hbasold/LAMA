{-# LANGUAGE FlexibleContexts #-}
module UnrollFby (rewrite) where

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad.Error (MonadError(..))
import Control.Applicative (Applicative)

import Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L


import TransformCommon

-- | Unroll fby(a;n;b) to a -> a -> ... -> b.
-- Additionally a and b are declared as list expression
-- if necessary. 
rewrite :: (MonadError String m, Functor m, Applicative m) => [Declaration] -> m [Declaration]
rewrite = everywhereM $ mkM rewriteExpr

rewriteExpr :: (MonadError String m, Functor m, Applicative m) => Expr -> m Expr
rewriteExpr (FBYExpr result n inits) =
  trConstExpr n >>= isInt >>= return . unrollFby (mkListExpr inits) (mkListExpr result)
rewriteExpr e = return e

isInt :: (MonadError String m) => L.ConstExpr -> m Int
isInt (L.Fix (L.Const (L.Fix (L.IntConst n)))) = return $ fromInteger n
isInt e = throwError $ show e ++ " is not an integer"

mkListExpr :: [Expr] -> Expr
mkListExpr [e] = e
mkListExpr es = ListExpr es

unrollFby :: Expr -> Expr -> Int -> Expr
unrollFby _ b 0 = b
unrollFby a b n = S.BinaryExpr S.BinAfter a . S.UnaryExpr S.UnPre $ unrollFby a b (n-1)
