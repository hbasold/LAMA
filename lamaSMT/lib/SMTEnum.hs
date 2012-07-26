{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module SMTEnum where

import Language.SMTLib2.Internals
import qualified Data.AttoLisp as L
import Data.Text (Text)

import Data.Typeable

type EnumAlias = Text
type EnumCons = Text

newtype SMTEnum = SMTEnum { getEnumCons :: EnumCons }
                deriving (Eq, Show, Typeable)

instance SMTType SMTEnum where
  type SMTAnnotation SMTEnum = (EnumAlias, [EnumCons])
  getSort _ (a, _) = L.Symbol a
  declareType u ann = [(typeOf u, decl ann)]
    where decl (a, cs) =
            declareDatatypes [] [(a, map (,[]) cs)]

instance SMTValue SMTEnum where
  unmangle (L.Symbol c) _ = return . Just $ SMTEnum c
  unmangle _ _ = return Nothing

  mangle (SMTEnum c) _ = L.Symbol c