{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module SMTEnum where

import Language.SMTLib2.Internals
import Language.SMTLib2 (BitVector)
import Language.SMTLib2.Functions (SMTFun(..))
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
type BVType = BitVector BVUntyped

newtype SMTEnum = SMTEnum { getEnumCons :: EnumCons }
                deriving (Eq, Show, Typeable)

data EnumImplementation =
  EnumImplType
  | EnumImplBit

data EnumAnn =
  EnumTypeAnn EnumAlias [EnumCons] TypeRep
  | EnumBitAnn Integer (Bimap EnumCons BVType) BVType
    -- ^ Bit vector size, bijective mapping between constructors
    -- and bit vectors and the last constructor i.e. that with
    -- the highest value
  deriving (Eq, Typeable)

enumBottom :: EnumAnn -> SMTEnum
enumBottom (EnumTypeAnn _ (c0:_) _) = SMTEnum c0
enumBottom (EnumBitAnn _ cons _) = SMTEnum . snd $ Bimap.findMinR cons

mkSMTEnumAnn :: EnumImplementation -> String -> [String] -> SMTAnnotation SMTEnum
mkSMTEnumAnn EnumImplType e cons =
  let e' = "SMTEnum_" ++ e
      ty = mkTyConApp (mkTyCon3 "" "" e') []
  in EnumTypeAnn (fromString e') (map fromString cons) ty
mkSMTEnumAnn EnumImplBit _ cons =
  let cons' = map fromString cons
      (numCons, bvCons) = mapAccumL (\n c -> (n+1,(c, BitVector n))) 0 cons'
      biggestCons = numCons - 1
      bits = usedBits biggestCons
  in EnumBitAnn bits (Bimap.fromList bvCons) (BitVector biggestCons)

instance SMTType SMTEnum where
  type SMTAnnotation SMTEnum = EnumAnn

  getSort _ (EnumTypeAnn a _ _) = L.Symbol a
  getSort _ (EnumBitAnn size _ _) = getSort (undefined :: BVType) size

  getSortBase _ = undefined

  declareType u ann@(EnumTypeAnn e cons ty) = declareType' (DeclaredType u ann) (decl e cons)
    where decl a cs =
            declareDatatypes [] [(a, map (,[]) cs)]
  declareType _ (EnumBitAnn size _ _) = declareType (undefined :: BVType) size

instance SMTValue SMTEnum where
  unmangle (L.Symbol c) (EnumTypeAnn _ _ _) = Just $ SMTEnum c
  unmangle x (EnumBitAnn size cons _) =
    do x' <- unmangle x size
       fmap SMTEnum $ Bimap.lookupR x' cons
  unmangle _ _ = Nothing

  mangle (SMTEnum c) (EnumTypeAnn _ _ _) = L.Symbol c
  mangle (SMTEnum c) (EnumBitAnn size cons _) =
    case Bimap.lookup c cons of
         Nothing -> error $ "Unknown enum " ++ unpack c
         Just bv -> mangle bv size

-- | Interpret an expression of type SMTEnum as bitvector expression
toBVExpr :: SMTExpr SMTEnum -> SMTExpr BVType
toBVExpr (Var n (EnumBitAnn size _ _)) = Var n size
toBVExpr e@(App f ') =
  case inferResAnnotation f (argAnn f) of
    EnumBitAnn size _ _ -> App (SMTFun f size) e'
    _ -> error $ "cannot convert enum expr to bit vector expr: " ++ show e
toBVExpr e = error $ "cannot convert enum expr to bit vector expr: " ++ show e
