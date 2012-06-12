{-| Type system of LAMA
-}

module Lang.LAMA.Types(
  -- * Types
  TypeAlias,
  Type (..),
  BaseType(..),
  boolT, intT, realT,
  -- * Typing structures
  Typed, mkTyped, untyped, getType,
  mapTyped, preserveType,
  EqFunctor(..), ShowFunctor(..)
) where

import Control.Arrow (first, (&&&))
import Data.Natural

import Lang.LAMA.Identifier
import Lang.LAMA.Fix

-- | Naming user declared types like enums and records
type TypeAlias = Identifier

-- | LAMA type expressions
data Type
  = GroundType BaseType   -- ^ Basic sorts
  | NamedType TypeAlias      -- ^ Named type (enum, record)
  | ArrayType BaseType Natural  -- ^ Array with fixed length of basic sort
  | Prod [Type]
  deriving (Eq, Show)

-- | Basic LAMA sorts
data BaseType
  = BoolT         -- ^ Boolean
  | IntT          -- ^ Integers
  | RealT         -- ^ Ideal real numbers (but seen as rational numbers)
  | SInt Natural  -- ^ Bounded signed integer type (bounded by bit size)
  | UInt Natural  -- ^ Bounded unsigned integer type (bounded by bit size)
  deriving (Eq, Show)

-- | Construct ground bool type
boolT :: Type
boolT = GroundType BoolT

-- | Construct ground int type
intT :: Type
intT = GroundType IntT

-- | Construct ground real type
realT :: Type
realT = GroundType RealT


----- Structure typing ------

-- | Add type to an arbitrary structure
data Typed0 e x = Typed {
    untyped0 :: e x,
    getType0 :: Type
  }

instance EqFunctor e => EqFunctor (Typed0 e) where
  eqF (Typed e1 t1) (Typed e2 t2) = (e1 `eqF` e2) && (t1 == t2)

instance ShowFunctor e => ShowFunctor (Typed0 e) where
  showF (Typed e t) = "(Typed (" ++ showF e ++ ") (" ++ show t ++ "))"

type Typed e = Fix (Typed0 e)

mkTyped :: e (Typed e) -> Type -> Typed e
mkTyped e t = Fix $ Typed e t

untyped :: Typed e -> e (Typed e)
untyped = untyped0 . unfix

getType :: Typed e -> Type
getType = getType0 . unfix

-- | fmap for Typed
mapTyped :: (e1 (Typed e1) -> e2 (Typed e2)) -> (Typed e1 -> Typed e2)
mapTyped f (Fix (Typed a t)) = Fix (Typed (f a) t)

-- | Construct new typed expression preserving the type
preserveType :: (Typed e1 -> (e2 (Typed e2))) -> Typed e1 -> Typed e2
preserveType cons = Fix . (uncurry Typed) . (first cons) . (id &&& getType)
