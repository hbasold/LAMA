{-| Type system of LAMA
-}

module Lang.LAMA.Types(
  -- * Types
  TypeAlias,
  Type (..),
  BaseType(..),
  boolT, intT, realT, mkProductT,
  -- * Typing structures
  Typed, mkTyped, untyped, getType,
  mapTyped, preserveType
) where

import Prelude.Extras

import Control.Arrow (first, (&&&))
import Data.Natural

import Lang.LAMA.Identifier
import Lang.LAMA.Fix

-- | Naming user declared types like enums and records
type TypeAlias i = i

-- | LAMA type expressions
data Type i
  = GroundType BaseType   -- ^ Basic sorts
  | EnumType (TypeAlias i)      -- ^ Named type (enum)
  | ProdType [Type i] -- ^ Product type
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
boolT :: Type i
boolT = GroundType BoolT

-- | Construct ground int type
intT :: Type i
intT = GroundType IntT

-- | Construct ground real type
realT :: Type i
realT = GroundType RealT

mkProductT :: [Type i] -> Type i
mkProductT [] = error "emtpy type list"
mkProductT [t] = t
mkProductT ts = ProdType ts


----- Structure typing ------

-- | Add type to an arbitrary structure
data Typed0 i e x = Typed {
    untyped0 :: e x,
    getType0 :: Type i
  }

instance (Ident i, Eq1 e) => Eq1 (Typed0 i e) where
  (Typed e1 t1) ==# (Typed e2 t2) = (e1 ==# e2) && (t1 == t2)

instance (Ident i, Show1 e) => Show1 (Typed0 i e) where
  showsPrec1 p (Typed e t) =
    showParen (p > 10) $ showString "Typed" . showsPrec1 p e . showsPrec p t

type Typed i e = Fix (Typed0 i e)

mkTyped :: e (Typed i e) -> Type i -> Typed i e
mkTyped e t = Fix $ Typed e t

untyped :: Typed i e -> e (Typed i e)
untyped = untyped0 . unfix

getType :: Typed i e -> Type i
getType = getType0 . unfix

-- | fmap for Typed
mapTyped :: (e1 (Typed i e1) -> e2 (Typed i e2)) -> (Typed i e1 -> Typed i e2)
mapTyped f (Fix (Typed a t)) = Fix (Typed (f a) t)

-- | Construct new typed expression preserving the type
preserveType :: (Typed i e1 -> (e2 (Typed i e2))) -> Typed i e1 -> Typed i e2
preserveType cons = Fix . (uncurry Typed) . (first cons) . (id &&& getType)
