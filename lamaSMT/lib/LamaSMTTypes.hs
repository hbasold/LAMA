{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module LamaSMTTypes where

import Data.Natural
import NatInstance ()
import Data.Array as Arr

import Control.Arrow ((&&&))

import Language.SMTLib2 as SMT
import Language.SMTLib2.Internals as SMT
import SMTEnum

data TypedExpr i
  = BoolExpr { unBool :: SMTExpr Bool }
  | IntExpr { unInt :: SMTExpr Integer }
  | RealExpr { unReal :: SMTExpr Rational }
  | EnumExpr { unEnum :: SMTExpr SMTEnum }
  | ProdExpr { unProd :: Array Int (TypedExpr i) }
  deriving (Eq, Show)

unBool' :: TypedExpr i -> SMTExpr Bool
unBool' (BoolExpr e) = e
unBool' e = error $ "Cannot unBool: " ++ show e

unProd' :: TypedExpr i -> Array Int (TypedExpr i)
unProd' (ProdExpr e) = e
unProd' e = error $ "Cannot unProd: " ++ show e

type StreamPos = SMTExpr Natural
type Stream t = SMTFun StreamPos t
data TypedStream i
  = BoolStream (Stream Bool)
  | IntStream (Stream Integer)
  | RealStream (Stream Rational)
  | EnumStream (Stream SMTEnum)
  | ProdStream (Array Int (TypedStream i))
--  deriving Show

extractStreamAnn :: SMTType t => Stream t -> SMTAnnotation Natural -> SMTAnnotation t
extractStreamAnn = inferResAnnotation

mkProdStream :: [TypedStream i] -> TypedStream i
mkProdStream [] = error "Cannot create empty product stream"
mkProdStream [s] = s
mkProdStream sts = ProdStream . uncurry listArray $ ((0,) . pred . length &&& id) sts

appStream :: TypedStream i -> StreamPos -> TypedExpr i
appStream (BoolStream s) n = BoolExpr $ s `app` n
appStream (IntStream s) n = IntExpr $ s `app` n
appStream (RealStream s) n = RealExpr $ s `app` n
appStream (EnumStream s) n = EnumExpr $ s `app` n
appStream (ProdStream s) n = ProdExpr $ fmap (`appStream` n) s

liftAssert :: TypedExpr i -> SMT ()
liftAssert (BoolExpr e) = assert e
liftAssert (ProdExpr es) = mapM_ liftAssert $ Arr.elems es
liftAssert e = error $ "liftAssert: cannot assert non-boolean expression: " ++ show e

liftRel :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool)
           -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftRel r (BoolExpr e1) (BoolExpr e2) = BoolExpr $ r e1 e2
liftRel r (IntExpr e1) (IntExpr e2) = BoolExpr $ r e1 e2
liftRel r (RealExpr e1) (RealExpr e2) = BoolExpr $ r e1 e2
liftRel r (EnumExpr e1) (EnumExpr e2) = BoolExpr $ r e1 e2
liftRel r (ProdExpr e1) (ProdExpr e2) = ProdExpr $ accum (liftRel r) e1 (Arr.assocs e2)
liftRel _ _ _ = error "liftRel: argument types don't match"

-- | Only for boolean product streams. Ensures that all fields of
-- a product hold simultaniuosly. Useful for elementwise
-- extended relatations.
prodAll :: TypedExpr i -> TypedExpr i
prodAll (BoolExpr e) = BoolExpr e
prodAll (ProdExpr e) = liftBoolL and' $ Arr.elems e
prodAll e = error $ "prodAll: not a product or boolean expr: " ++ show e

liftOrd :: (forall a. (SMTType a, SMTOrd a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool)
           -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftOrd r (IntExpr e1) (IntExpr e2) = BoolExpr $ r e1 e2
liftOrd r (RealExpr e1) (RealExpr e2) = BoolExpr $ r e1 e2
liftOrd _ _ _ = error "liftRel: argument types don't match or are not ordered"


lift1Bool :: (SMTExpr Bool -> SMTExpr Bool) -> TypedExpr i -> TypedExpr i
lift1Bool f (BoolExpr e) = BoolExpr $ f e
lift1Bool _ _ = error "lift1Bool: argument is not boolean"

liftBool2 :: (SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool)
             -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftBool2 f (BoolExpr e1) (BoolExpr e2) = BoolExpr $ f e1 e2
liftBool2 _ e1 e2 = error $ "liftBool2: arguments are not boolean: " ++ show e1 ++ "; " ++ show e2

liftBoolL :: (SMTFunction f, SMTFunArg f ~ [SMTExpr Bool], SMTFunRes f ~ Bool) =>
             f -> [TypedExpr i] -> TypedExpr i
liftBoolL f es@((BoolExpr _):_) = BoolExpr . app f $ map unBool es
liftBoolL _ es = error $ "Cannot lift bool expr for" ++ show es

lift2 :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr a)
         -> TypedExpr i -> TypedExpr i -> TypedExpr i
lift2 f (BoolExpr e1) (BoolExpr e2) = BoolExpr $ f e1 e2
lift2 f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
lift2 f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
lift2 f (EnumExpr e1) (EnumExpr e2) = EnumExpr $ f e1 e2
lift2 f (ProdExpr e1) (ProdExpr e2) = ProdExpr $ accum (lift2 f) e1 (Arr.assocs e2)
lift2 _ _ _ = error "lift2: argument types don't match"

liftIte :: TypedExpr i -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftIte (BoolExpr c) = lift2 (ite c)
liftIte _ = error "liftIte: condition is not boolean"

liftArith :: (forall a. SMTArith a => SMTExpr a -> SMTExpr a -> SMTExpr a)
              -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftArith f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
liftArith f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
liftArith _ _ _ = error "liftArith: argument types don't match or are not aritemetic types"

liftArithL :: (forall a. SMTArith a => [SMTExpr a] -> SMTExpr a)
              -> [TypedExpr i] -> TypedExpr i
liftArithL f es@((IntExpr _):_) = IntExpr . f $ map unInt es
liftArithL f es@((RealExpr _):_) = RealExpr . f $ map unReal es
liftArithL _ _ = error "liftArithL: argument types don't match or are not arithmetic types"

liftInt2 :: (SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer)
              -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftInt2 f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
liftInt2 _ _ _ = error "liftInt2: argument types are not integers"

liftReal2 :: (SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational)
              -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftReal2 f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
liftReal2 _ _ _ = error "liftReal2: argument types are not rational"
