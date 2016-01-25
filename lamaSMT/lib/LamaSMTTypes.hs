{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module LamaSMTTypes where

import Data.Natural
import NatInstance ()
import Data.Array as Arr
import Data.Typeable
import Data.Foldable (foldlM)
import Data.List (mapAccumL)

import Text.Show

import Control.Arrow ((&&&))

import Language.SMTLib2 as SMT
import SMTEnum

data TypedExpr
  = BoolExpr { unBool :: SMTExpr Bool }
  | IntExpr { unInt :: SMTExpr Integer }
  | RealExpr { unReal :: SMTExpr Rational }
  | EnumExpr { unEnum :: SMTExpr SMTEnum }
  | ProdExpr { unProd :: Array Int (TypedExpr) }
  deriving (Ord, Typeable, Eq, Show)

data TypedAnnotation
  = BoolAnnotation { anBool :: ArgAnnotation (SMTExpr Bool) }
  | IntAnnotation { anInt :: ArgAnnotation (SMTExpr Integer) }
  | RealAnnotation { anReal :: ArgAnnotation (SMTExpr Rational) }
  | EnumAnnotation { anEnum :: ArgAnnotation (SMTExpr SMTEnum) }
  | ProdAnnotation { anProd :: Array Int TypedAnnotation }
  deriving (Ord, Typeable, Eq, Show)

unBool' :: TypedExpr -> SMTExpr Bool
unBool' (BoolExpr e) = e
unBool' e = error $ "Cannot unBool: " ++ show e

unProd' :: TypedExpr -> Array Int (TypedExpr)
unProd' (ProdExpr e) = e
unProd' e = error $ "Cannot unProd: " ++ show e

data TypedFunc
  = BoolFunc (SMTFunction [TypedExpr] Bool)
  | IntFunc (SMTFunction [TypedExpr] Integer)
  | RealFunc (SMTFunction [TypedExpr] Rational)
  | EnumFunc EnumAnn (SMTFunction [TypedExpr] SMTEnum)
  | ProdFunc (Array Int (TypedFunc))
  deriving Show

mkProdExpr :: [TypedExpr] -> TypedExpr
mkProdExpr [] = error "Cannot create empty product expression"
mkProdExpr [s] = s
mkProdExpr sts = ProdExpr . uncurry listArray $ ((0,) . pred . length &&& id) sts

appFunc :: TypedFunc -> [TypedExpr] -> TypedExpr
appFunc (BoolFunc f) arg = BoolExpr $ f `app` arg
appFunc (IntFunc f) arg = IntExpr $ f `app` arg
appFunc (RealFunc f) arg = RealExpr $ f `app` arg
appFunc (EnumFunc _ f) arg = EnumExpr $ f `app` arg
appFunc (ProdFunc f) arg = ProdExpr $ fmap (`appFunc` arg) f

instance Args (TypedExpr) where
  type ArgAnnotation TypedExpr = TypedAnnotation
  foldExprs f s ~(BoolExpr x) (BoolAnnotation ann) = do
    (ns, res) <- foldExprs f s x ann
    return (ns, BoolExpr res)
  foldExprs f s ~(IntExpr x) (IntAnnotation ann) = do
    (ns, res) <- foldExprs f s x ann
    return (ns, IntExpr res)
  foldExprs f s ~(RealExpr x) (RealAnnotation ann) = do
    (ns, res) <- foldExprs f s x ann
    return (ns, RealExpr res)
  foldExprs f s ~(EnumExpr x) (EnumAnnotation ann) = do
    (ns, res) <- foldExprs f s x ann
    return (ns, EnumExpr res)
  foldExprs f s ~(ProdExpr x) (ProdAnnotation y) =
    foldlM (\(s',ProdExpr cmp) (k,ann) -> do
      let el = x ! k
      (s'',el') <- foldExprs f s' el ann
      return (s'', ProdExpr $ cmp Arr.// [(k,el')])
      ) (s,ProdExpr $ Arr.array (bounds y) []) (Arr.assocs y)
  foldsExprs f s lst (BoolAnnotation ann) = do
    (ns, ress, res) <- foldsExprs f s (fmap (\(x,p) -> (case x of BoolExpr x' -> x',p)) lst) ann
    return (ns, fmap BoolExpr ress, BoolExpr res)
  foldsExprs f s lst (IntAnnotation ann) = do
    (ns, ress, res) <- foldsExprs f s (fmap (\(x,p) -> (case x of IntExpr x' -> x',p)) lst) ann
    return (ns, fmap IntExpr ress, IntExpr res)
  foldsExprs f s lst (RealAnnotation ann) = do
    (ns, ress, res) <- foldsExprs f s (fmap (\(x,p) -> (case x of RealExpr x' -> x',p)) lst) ann
    return (ns, fmap RealExpr ress, RealExpr res)
  foldsExprs f s lst (EnumAnnotation ann) = do
    (ns, ress, res) <- foldsExprs f s (fmap (\(x,p) -> (case x of EnumExpr x' -> x',p)) lst) ann
    return (ns, fmap EnumExpr ress, EnumExpr res)
  foldsExprs f s args (ProdAnnotation ann) = do
    let lst_ann = Arr.assocs ann
        lst = fmap (\(ProdExpr mp,extra) -> ([ mp ! k | (k,_) <- lst_ann ],extra)
                   ) args
    (ns,lst',lst_merged) <- foldsExprs f s lst (fmap snd lst_ann)
    return (ns,fmap (\lst'' -> ProdExpr $ Arr.array (bounds ann) $ zip (fmap fst lst_ann) lst''
                    ) lst',ProdExpr $ Arr.array (bounds ann)  $ zip (fmap fst lst_ann) lst_merged)
  extractArgAnnotation (BoolExpr x) = BoolAnnotation $ extractArgAnnotation x
  extractArgAnnotation (IntExpr x) = IntAnnotation $ extractArgAnnotation x
  extractArgAnnotation (RealExpr x) = RealAnnotation $ extractArgAnnotation x
  extractArgAnnotation (EnumExpr x) = EnumAnnotation $ extractArgAnnotation x
  extractArgAnnotation (ProdExpr x) = ProdAnnotation $ fmap extractArgAnnotation x
  toArgs (BoolAnnotation ann) exprs = do
    (res, rest) <- toArgs ann exprs
    return (BoolExpr res, rest)
  toArgs (IntAnnotation ann) exprs = do
    (res, rest) <- toArgs ann exprs
    return (IntExpr res, rest)
  toArgs (RealAnnotation ann) exprs = do
    (res, rest) <- toArgs ann exprs
    return (RealExpr res, rest)
  toArgs (EnumAnnotation ann) exprs = do
    (res, rest) <- toArgs ann exprs
    return (EnumExpr res, rest)
  toArgs (ProdAnnotation mp_ann) exprs =
    case mapAccumL (\cst (k,ann) -> case cst of
        Nothing -> (Nothing,undefined)
        Just rest -> case toArgs ann rest of
          Nothing -> (Nothing,undefined)
          Just (res,rest') -> (Just rest', (k,res))
                   ) (Just exprs) (Arr.assocs mp_ann) of
      (Nothing,_) -> Nothing
      (Just rest,mp) -> Just (ProdExpr $ Arr.array (bounds mp_ann) mp,rest)
  fromArgs (BoolExpr xs) = fromArgs xs
  fromArgs (IntExpr  xs) = fromArgs xs
  fromArgs (RealExpr xs) = fromArgs xs
  fromArgs (EnumExpr xs) = fromArgs xs
  fromArgs (ProdExpr xs) = concat $ fmap fromArgs $ Arr.elems xs
  getSorts (_::TypedExpr) (BoolAnnotation _) = error "lamasmt: no getSorts for TypedExpr"--getSorts (undefined::x) $ extractArgAnnotation ann
  getArgAnnotation _ _ = error "lamasmt: getArgAnnotation undefined for TypedExpr"
  showsArgs n p (BoolExpr x) = let (showx,nn) = showsArgs n 11 x
                               in (showParen (p>10) $
                                   showString "BoolExpr " . showx,nn)
  showsArgs n p (IntExpr x) = let (showx,nn) = showsArgs n 11 x
                               in (showParen (p>10) $
                                   showString "IntExpr " . showx,nn)
  showsArgs n p (RealExpr x) = let (showx,nn) = showsArgs n 11 x
                               in (showParen (p>10) $
                                   showString "RealExpr " . showx,nn)
  showsArgs n p (EnumExpr x) = let (showx,nn) = showsArgs n 11 x
                               in (showParen (p>10) $
                                   showString "EnumExpr " . showx,nn)
  showsArgs n p (ProdExpr x) =
    let (ni,lst') = mapAccumL (\ci (key,arg)
                               -> let (str,ci') = showsArgs ci 0 arg
                                  in (ci',(key,str))
                              ) n (Arr.assocs x)
    in (showString "fromList " . showListWith (\(key,str)
                                               -> showChar '(' .
                                                  showsPrec 0 key .
                                                  showChar ',' .
                                                  str . showChar ')') lst',ni)

type StreamPos = SMTExpr Natural
type Stream t = SMTFunction StreamPos t
data TypedStream i
  = BoolStream (Stream Bool)
  | IntStream (Stream Integer)
  | RealStream (Stream Rational)
  | EnumStream EnumAnn (Stream SMTEnum)
  | ProdStream (Array Int (TypedStream i))
  deriving Show

mkProdStream :: [TypedStream i] -> TypedStream i
mkProdStream [] = error "Cannot create empty product stream"
mkProdStream [s] = s
mkProdStream sts = ProdStream . uncurry listArray $ ((0,) . pred . length &&& id) sts

appStream :: TypedStream i -> StreamPos -> TypedExpr
appStream (BoolStream s) n = BoolExpr $ s `app` n
appStream (IntStream s) n = IntExpr $ s `app` n
appStream (RealStream s) n = RealExpr $ s `app` n
appStream (EnumStream _ s) n = EnumExpr $ s `app` n
appStream (ProdStream s) n = ProdExpr $ fmap (`appStream` n) s

liftAssert :: TypedExpr -> SMT ()
liftAssert (BoolExpr e) = assert e
liftAssert (ProdExpr es) = mapM_ liftAssert $ Arr.elems es
liftAssert e = error $ "liftAssert: cannot assert non-boolean expression: " ++ show e

liftRel :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool)
           -> TypedExpr -> TypedExpr -> TypedExpr
liftRel r (BoolExpr e1) (BoolExpr e2) = BoolExpr $ r e1 e2
liftRel r (IntExpr e1) (IntExpr e2) = BoolExpr $ r e1 e2
liftRel r (RealExpr e1) (RealExpr e2) = BoolExpr $ r e1 e2
liftRel r (EnumExpr e1) (EnumExpr e2) = BoolExpr $ r e1 e2
liftRel r (ProdExpr e1) (ProdExpr e2) = ProdExpr $ accum (liftRel r) e1 (Arr.assocs e2)
liftRel _ _ _ = error "liftRel: argument types don't match"

-- | Only for boolean product streams. Ensures that all fields of
-- a product hold simultaniuosly. Useful for elementwise
-- extended relatations.
prodAll :: TypedExpr -> TypedExpr
prodAll (BoolExpr e) = BoolExpr e
prodAll (ProdExpr e) = liftBoolL and' $ Arr.elems e
prodAll e = error $ "prodAll: not a product or boolean expr: " ++ show e

liftOrd :: (forall a. (SMTType a, SMTOrd a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool)
           -> TypedExpr -> TypedExpr -> TypedExpr
liftOrd r (IntExpr e1) (IntExpr e2) = BoolExpr $ r e1 e2
liftOrd r (RealExpr e1) (RealExpr e2) = BoolExpr $ r e1 e2
liftOrd _ _ _ = error "liftRel: argument types don't match or are not ordered"


lift1Bool :: (SMTExpr Bool -> SMTExpr Bool) -> TypedExpr -> TypedExpr
lift1Bool f (BoolExpr e) = BoolExpr $ f e
lift1Bool _ _ = error "lift1Bool: argument is not boolean"

liftBool2 :: (SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool)
             -> TypedExpr -> TypedExpr -> TypedExpr
liftBool2 f (BoolExpr e1) (BoolExpr e2) = BoolExpr $ f e1 e2
liftBool2 _ e1 e2 = error $ "liftBool2: arguments are not boolean: " ++ show e1 ++ "; " ++ show e2

liftBoolL :: SMTFunction [SMTExpr Bool] Bool -> [TypedExpr] -> TypedExpr
liftBoolL f es@((BoolExpr _):_) = BoolExpr . app f $ map unBool es
liftBoolL _ es = error $ "Cannot lift bool expr for" ++ show es

lift2 :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr a)
         -> TypedExpr -> TypedExpr -> TypedExpr
lift2 f (BoolExpr e1) (BoolExpr e2) = BoolExpr $ f e1 e2
lift2 f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
lift2 f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
lift2 f (EnumExpr e1) (EnumExpr e2) = EnumExpr $ f e1 e2
lift2 f (ProdExpr e1) (ProdExpr e2) = ProdExpr $ accum (lift2 f) e1 (Arr.assocs e2)
lift2 _ _ _ = error "lift2: argument types don't match"

liftIte :: TypedExpr -> TypedExpr -> TypedExpr -> TypedExpr
liftIte (BoolExpr c) = lift2 (ite c)
liftIte _ = error "liftIte: condition is not boolean"

liftArith :: (forall a. SMTArith a => SMTFunction (SMTExpr a, SMTExpr a) a)
             -> TypedExpr
             -> TypedExpr
             -> TypedExpr
liftArith f (IntExpr e1)  (IntExpr e2)  = IntExpr  $ app f (e1, e2)
liftArith f (RealExpr e1) (RealExpr e2) = RealExpr $ app f (e1, e2)
liftArith _ _ _
  = error "liftArith: argument types don't match or are not aritemetic types"

liftArithL :: (forall a. SMTArith a => SMTFunction [SMTExpr a] a)
              -> [TypedExpr]
              -> TypedExpr
liftArithL f es@((IntExpr _):_)  = IntExpr  . app f $ map unInt  es
liftArithL f es@((RealExpr _):_) = RealExpr . app f $ map unReal es
liftArithL _ _
  = error "liftArithL: argument types don't match or are not arithmetic types"

liftInt2 :: (SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer)
              -> TypedExpr -> TypedExpr -> TypedExpr
liftInt2 f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
liftInt2 _ _ _ = error "liftInt2: argument types are not integers"

liftReal2 :: (SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational)
              -> TypedExpr -> TypedExpr -> TypedExpr
liftReal2 f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
liftReal2 _ _ _ = error "liftReal2: argument types are not rational"
