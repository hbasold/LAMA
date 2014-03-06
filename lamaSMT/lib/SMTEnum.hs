{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module SMTEnum where

import Data.Fix
import Language.SMTLib2 (bvule, constantAnn)
import Language.SMTLib2.Internals hiding (constructors)
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap, (!>))
import Data.Bits.Size
import Data.Typeable
import Data.String (IsString(..))
import Data.Traversable (mapAccumL)

type EnumAlias = String
type EnumCons = String
type BVType = BitVector BVUntyped

newtype SMTEnum = SMTEnum { getEnumCons :: EnumCons }
                deriving (Eq, Ord, Show, Typeable)

data EnumImplementation =
  EnumImplType
  | EnumImplBit
  deriving (Eq, Ord, Show)

data EnumAnn =
  EnumTypeAnn EnumAlias [EnumCons] TypeRep
  | EnumBitAnn Integer (Bimap EnumCons BVType) BVType
    -- ^ Bit vector size, bijective mapping between constructors
    -- and bit vectors and the last constructor i.e. that with
    -- the highest value
  deriving (Eq, Typeable, Show)

instance Ord EnumAnn where
  compare (EnumTypeAnn a1 _ _) (EnumTypeAnn a2 _ _) = compare a1 a2
  compare (EnumBitAnn _ cons1 max1) (EnumBitAnn _ cons2 max2) =
    case compare max1 max2 of
      EQ -> compare (cons1 !> max1) (cons2 !> max2)
      c -> c
  compare (EnumTypeAnn _ _ _) (EnumBitAnn _ _ _) = LT
  compare (EnumBitAnn _ _ _) (EnumTypeAnn _ _ _) = GT

enumBottom :: EnumAnn -> SMTEnum
enumBottom (EnumTypeAnn _ (c0:_) _) = SMTEnum c0
enumBottom (EnumTypeAnn alias [] _)
  = error $ "Enum " ++ alias ++ " has no constructors."
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

  -- getSort :: t -> SMTAnnotation t -> Sort
  getSort _ (EnumTypeAnn alias _ _) = Fix $ NamedSort alias []
  getSort _ (EnumBitAnn size _ _) = getSort (undefined :: BVType) size

  -- asDataType :: t -> SMTAnnotation t -> Maybe (String,TypeCollection)
  asDataType _ ann@(EnumTypeAnn alias constructors _) =
    Just (alias,
          TypeCollection { argCount = 0
                         , dataTypes = [dtEnum] })
    where
      dtEnum =
        DataType { dataTypeName = alias
                 , dataTypeConstructors = mkCons constructors
                 , dataTypeGetUndefined =
                   \_ f -> f (undefined :: SMTEnum) ann
                 }
      mkCons :: [EnumCons] -> [Constr]
      mkCons = map mkCons'
      mkCons' :: EnumCons -> Constr
      mkCons' cons =
        Constr { conName = cons
               , conFields = []
               , construct =
                 \[Just sort] _ f -> f [sort] (SMTEnum cons) ann
               , conTest = \_ x -> case cast x of
                   Just c -> c == cons
                   _ -> False
               }
  asDataType _ (EnumBitAnn size _ _) = asDataType (undefined :: BVType) size

  -- asValueType :: t -> SMTAnnotation t -> (forall v. SMTValue v => v -> SMTAnnotation v -> r) -> Maybe r
  asValueType x ann f = Just $ f x ann

  -- getProxyArgs :: t -> SMTAnnotation t -> [ProxyArg]
  getProxyArgs x ann = [ProxyArg x ann]

  -- additionalConstraints :: t -> SMTAnnotation t -> SMTExpr t -> [SMTExpr Bool]
  additionalConstraints _ (EnumBitAnn size _ highestCons) (Var i _)
    = [bvule (Var i size :: SMTExpr BVType) (constantAnn highestCons size)]
  additionalConstraints _ (EnumBitAnn _ _ _)  _ = []
  additionalConstraints _ (EnumTypeAnn _ _ _) _ = []

  -- annotationFromSort :: t -> Sort -> SMTAnnotation t
  annotationFromSort _ (Fix (NamedSort alias []))
    = EnumTypeAnn alias
      (error $ "Don't know" ++ alias ++ "'s constructors.")
      (error $ "Don't know" ++ alias ++ "'s TypeRep.")
  annotationFromSort _ s =
    let size = annotationFromSort (undefined :: BVType) s
    in EnumBitAnn size
       (error $ "Don't know constructors of enum represented by "
        ++ show size ++ " bits.")
       (error $ "Don't know size of enum represented by "
        ++ show size ++ " bits.")

instance SMTValue SMTEnum where
  unmangle (ConstrValue c [] _) (EnumTypeAnn _ _ _) = Just $ SMTEnum c
  unmangle x (EnumBitAnn size cons _) =
    do x' <- unmangle x size
       fmap SMTEnum $ Bimap.lookupR x' cons
  unmangle _ _ = Nothing

  mangle (SMTEnum c) (EnumTypeAnn _ _ _) =
    ConstrValue c [] Nothing
  mangle (SMTEnum c) (EnumBitAnn size cons _) =
    case Bimap.lookup c cons of
         Nothing -> error $ "Unknown enum constructor " ++ c
         Just bv -> mangle bv size

-- | Interpret an expression of type SMTEnum as bitvector expression
{-
toBVExpr :: SMTExpr SMTEnum -> SMTExpr BVType
toBVExpr (Var n (EnumBitAnn size _ _)) = Var n size
toBVExpr e@(App f ') =
  case inferResAnnotation f (argAnn f) of
    EnumBitAnn size _ _ -> App (SMTFun f size) e'
    _ -> error $ "cannot convert enum expr to bit vector expr: " ++ show e
toBVExpr e = error $ "cannot convert enum expr to bit vector expr: " ++ show e
-}
