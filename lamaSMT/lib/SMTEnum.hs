{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module SMTEnum where

import Language.SMTLib2.Internals
import qualified Data.AttoLisp as L
import Data.Text (Text)

import Data.Typeable
import Data.String (IsString(..))

type EnumAlias = Text
type EnumCons = Text

newtype SMTEnum = SMTEnum { getEnumCons :: EnumCons }
                deriving (Eq, Show, Typeable)

mkSMTEnumAnn :: String -> [String] -> SMTAnnotation SMTEnum
mkSMTEnumAnn e cons =
  let e' = "SMTEnum_" ++ e
      ty = mkTyConApp (mkTyCon3 "" "" e') []
  in (fromString e', map fromString cons, ty)

instance SMTType SMTEnum where
  type SMTAnnotation SMTEnum = (EnumAlias, [EnumCons], TypeRep)
  getSort _ (a, _, _) = L.Symbol a
  declareType u (e, cons, ty) = declareType' ty (decl e cons)
    where decl a cs =
            declareDatatypes [] [(a, map (,[]) cs)]

instance SMTValue SMTEnum where
  unmangle (L.Symbol c) _ = return . Just $ SMTEnum c
  unmangle _ _ = return Nothing

  mangle (SMTEnum c) _ = L.Symbol c