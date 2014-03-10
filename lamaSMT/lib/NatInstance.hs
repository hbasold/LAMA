{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}

module NatInstance where

import Data.Natural
import Data.Unit
import Data.Fix
import Language.SMTLib2.Internals
import Language.SMTLib2
import Language.SMTLib2.Internals.Operators

import Data.Typeable

deriving instance Typeable Natural

data NatImplementation =
  NatInt
  | NatType
  deriving (Eq, Ord, Show, Typeable)

zero' :: SMTAnnotation Natural -> SMTExpr Natural
zero' ann = constantAnn 0 ann

succ' :: SMTAnnotation Natural -> SMTExpr Natural -> SMTExpr Natural
succ' NatInt  e = app plus [e, (constantAnn 1 NatInt)]
succ' NatType e =
  (SMTConstructor $ Constructor [] datatypeNat succConstructor) `app` e

zeroConstructor :: Constr
zeroConstructor =
  Constr { conName   = "zero"
         , conFields = []
         , construct =
           \[Just sort] _ f -> f [sort] (0 :: Natural) NatType
         , conTest   = \_ x -> case cast x of
             Just (view -> Zero) -> True
             _                   -> False
         }

succConstructor :: Constr
succConstructor =
  Constr { conName   = "succ"
         , conFields = [predField]
         , construct =
           \_ [predAny] f -> case castAnyValue predAny of
             Just (pred, ann)
               -> f [] (pred + 1 :: Natural) ann
             _ -> error $ "Casting succ argument failed"
         , conTest   = \_ x -> case cast x of
             Just (view -> Succ _) -> True
             _                     -> False
         }
  where
    predField =
      DataField { fieldName = "pred"
                , fieldSort = Fix (NormalSort (NamedSort "Nat" []))
                , fieldGet  =
                  \_ x f -> flip f NatType $ case cast x of
                    Just (view -> Succ n) -> n
                    _                     -> error $ "Casting pred failed"
                }

datatypeNat :: DataType
datatypeNat =
  DataType { dataTypeName = "Nat"
           , dataTypeConstructors = [zeroConstructor, succConstructor]
           , dataTypeGetUndefined =
             \_ f -> f (error "undefined Natural" :: Natural) NatType
           }

instance SMTType Natural where
  type SMTAnnotation Natural = NatImplementation

  -- getSort :: t -> SMTAnnotation t -> Sort
  getSort _ NatInt  = getSort (undefined :: Integer) unit
  getSort _ NatType = Fix $ NamedSort "Nat" []

  -- asDataType :: t -> SMTAnnotation t -> Maybe (String,TypeCollection)
  asDataType _ NatInt  = Nothing
  asDataType _ NatType =
    Just ("Nat",
          TypeCollection { argCount = 0
                         , dataTypes = [datatypeNat] })

  -- asValueType :: t -> SMTAnnotation t -> (forall v. SMTValue v => v -> SMTAnnotation v -> r) -> Maybe r
  asValueType x ann f = Just $ f x ann

  -- getProxyArgs :: t -> SMTAnnotation t -> [ProxyArg]
  getProxyArgs _ _ = []

  -- additionalConstraints :: t -> SMTAnnotation t -> SMTExpr t -> [SMTExpr Bool]
  additionalConstraints _ NatInt x@(Var _ _)  = [x .>=. (zero' NatInt)]
  additionalConstraints _ NatInt _            = []
  additionalConstraints _ NatType _           = []

  -- annotationFromSort :: t -> Sort -> SMTAnnotation t
  annotationFromSort _ (Fix (NamedSort "Nat" [])) = NatType
  annotationFromSort _ _                          = NatInt

instance SMTValue Natural where
  unmangle x NatInt = fmap fromInteger $ unmangle x unit
  unmangle (ConstrValue "zero" [] _)  NatType = Just $ fromInteger 0
  unmangle (ConstrValue "succ" [n] _) NatType = fmap (+1) $ unmangle n NatType
  unmangle _                          _       = Nothing

  mangle x                NatInt  = mangle (toInteger x) unit
  mangle (view -> Zero)   NatType = (ConstrValue "zero" [] Nothing)
  mangle (view -> Succ n) NatType =
    (ConstrValue "succ" [mangle n NatType] Nothing)

-- | only correct with NatInt!!
instance SMTArith Natural
-- | only correct with NatInt!!
instance SMTOrd Natural where
  (.<.)  x y = App (SMTOrd Lt) (x,y)
  (.<=.) x y = App (SMTOrd Le) (x,y)
  (.>.)  x y = App (SMTOrd Gt) (x,y)
  (.>=.) x y = App (SMTOrd Ge) (x,y)


{-
natVar :: MonadSMT m => SMTAnnotation Natural -> m (SMTExpr Natural)
natVar NatType = liftSMT $ varAnn NatType
natVar NatInt = liftSMT $ varAnn NatInt >>=
                \x -> assert (x .>=. (zero' NatInt)) >>
                      return x
-}
