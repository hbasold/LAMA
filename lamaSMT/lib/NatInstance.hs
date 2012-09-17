{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}

module NatInstance where

import Data.Natural
import Data.Unit
import Language.SMTLib2.Internals
import Language.SMTLib2
import qualified Data.AttoLisp as L

import Data.Typeable

import Control.Monad (liftM)

deriving instance Typeable Natural

data NatImplementation =
  NatType
  | NatInt

instance SMTType Natural where
  type SMTAnnotation Natural = NatImplementation

  getSort _ NatType = L.Symbol "Nat"
  getSort _ NatInt = getSort (undefined :: Integer) unit

  getSortBase _ = undefined

  declareType u NatType =
    declareType' (typeOf u) decl
    where
      decl = declareDatatypes [] [
        ("Nat",
         [("zero", []),
          ("succ", [("pred", L.Symbol "Nat")])
         ])]
  declareType _ NatInt = declareType (undefined :: Integer) unit

instance SMTValue Natural where
  unmangle (L.Symbol "zero") NatType = return $ Just $ fromInteger 0
  unmangle (L.List [L.Symbol "succ", r]) NatType = liftM (fmap (+1)) $ unmangle r NatType
  unmangle x NatInt = liftM (fmap fromInteger) $ unmangle x unit
  unmangle _ _ = return Nothing

  mangle (view -> Zero) NatType = L.Symbol "zero"
  mangle (view -> Succ n) NatType = L.List [L.Symbol "succ", mangle n NatType]
  mangle x NatInt = mangle (toInteger x) unit

-- | only correct with NatInt!!
instance SMTArith Natural
-- | only correct with NatInt!!
instance SMTOrd Natural where
  (.<.) = Lt
  (.<=.) = Le
  (.>.) = Gt
  (.>=.) = Ge

zero' :: SMTAnnotation Natural -> SMTExpr Natural
zero' ann = constantAnn 0 ann

succ' :: SMTAnnotation Natural -> SMTExpr Natural -> SMTExpr Natural
succ' NatType e = Fun "succ" (extractAnnotation e) (extractAnnotation e) `app` e
succ' NatInt e = Plus [e, (constantAnn 1 NatInt)]

natVar :: MonadSMT m => SMTAnnotation Natural -> m (SMTExpr Natural)
natVar NatType = liftSMT $ varAnn NatType
natVar NatInt = liftSMT $ varAnn NatInt >>=
                \x -> assert (x .>=. (zero' NatInt)) >>
                      return x