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

deriving instance Typeable Natural

instance SMTType Natural where
  type SMTAnnotation Natural = ()
  getSort _ _ = L.Symbol "Nat"
  declareType u _ =
    declareType' (typeOf u) decl
    where
      decl = declareDatatypes [] [
        ("Nat",
         [("zero", []),
          ("succ", [("pred", L.Symbol "Nat")])
         ])]

instance SMTValue Natural where
  unmangle (L.Symbol "zero") _ = return $ Just $ fromInteger 0
  unmangle (L.List [L.Symbol "succ", r]) a = fmap (fmap (+1)) $ unmangle r a
  unmangle _ _ = return Nothing

  mangle (view -> Zero) _ = L.Symbol "zero"
  mangle (view -> Succ n) a = L.List [L.Symbol "succ", mangle n a]

zero' :: SMTExpr Natural
zero' = Var "zero" unit

succ' :: SMTExpr Natural -> SMTExpr Natural
succ' e = Fun "succ" (extractAnnotation e) (extractAnnotation e) `app` e