{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module SMTEnum where

import Language.SMTLib2.Internals
import Language.SMTLib2 (BitVector)
import qualified Data.AttoLisp as L
import Data.Text (Text, unpack)
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap)
import Data.Bits.Size
import Data.Typeable
import Data.String (IsString(..))
import Data.Traversable (mapAccumL)

type EnumAlias = Text
type EnumCons = Text

newtype SMTEnum = SMTEnum { getEnumCons :: EnumCons }
                deriving (Eq, Show, Typeable)

data EnumImplementation =
  EnumImplType
  | EnumImplBit

data EnumAnn =
  EnumTypeAnn EnumAlias [EnumCons] TypeRep
  | EnumBitAnn Integer (Bimap EnumCons BitVector)

enumBottom :: EnumAnn -> SMTEnum
enumBottom (EnumTypeAnn _ (c0:_) _) = SMTEnum c0
enumBottom (EnumBitAnn _ cons) = SMTEnum . snd $ Bimap.findMinR cons

mkSMTEnumAnn :: EnumImplementation -> String -> [String] -> SMTAnnotation SMTEnum
mkSMTEnumAnn EnumImplType e cons =
  let e' = "SMTEnum_" ++ e
      ty = mkTyConApp (mkTyCon3 "" "" e') []
  in EnumTypeAnn (fromString e') (map fromString cons) ty
mkSMTEnumAnn EnumImplBit _ cons =
  let cons' = map fromString cons
      (numCons, bvCons) = mapAccumL (\n c -> (n+1,(c, fromInteger n))) 0 cons'
      bits = usedBits numCons
  in EnumBitAnn bits (Bimap.fromList bvCons)

instance SMTType SMTEnum where
  type SMTAnnotation SMTEnum = EnumAnn

  getSort _ (EnumTypeAnn a _ _) = L.Symbol a
  getSort _ (EnumBitAnn size _) = getSort (undefined :: BitVector) size

  getSortBase _ = undefined

  declareType _ (EnumTypeAnn e cons ty) = declareType' ty (decl e cons)
    where decl a cs =
            declareDatatypes [] [(a, map (,[]) cs)]
  declareType _ (EnumBitAnn size _) = declareType (undefined :: BitVector) size

instance SMTValue SMTEnum where
  unmangle (L.Symbol c) (EnumTypeAnn _ _ _) = return . Just $ SMTEnum c
  unmangle x (EnumBitAnn size cons) =
    do r <- unmangle x size
       case r of
         Nothing -> return Nothing
         Just x' -> return . fmap SMTEnum $ Bimap.lookupR x' cons
  unmangle _ _ = return Nothing

  mangle (SMTEnum c) (EnumTypeAnn _ _ _) = L.Symbol c
  mangle (SMTEnum c) (EnumBitAnn size cons) =
    case Bimap.lookup c cons of
         Nothing -> error $ "Unknown enum " ++ unpack c
         Just bv -> mangle bv size