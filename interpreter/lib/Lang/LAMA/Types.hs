module Lang.LAMA.Types where

import Data.Natural
import Control.Arrow (first, (&&&))

import Lang.LAMA.Identifier

type TypeId = Identifier

-- | LAMA type expressions
data Type
  = GroundType BaseType   -- ^ Basic sorts
  | NamedType TypeId      -- ^ Named type (enum, record)
  | ArrayType BaseType Natural  -- ^ Array with fixed length of basic sort
  deriving (Eq, Show)

-- | Basic LAMA sorts
data BaseType
  = BoolT         -- ^ Boolean
  | IntT          -- ^ Integers
  | RealT         -- ^ Ideal real numbers (but seen as rational numbers)
  | SInt Natural  -- ^ Bounded signed integer type (bounded by bit size)
  | UInt Natural  -- ^ Bounded unsigned integer type (bounded by bit size)
  deriving (Eq, Show)
  
boolT :: Type
boolT = GroundType BoolT

intT :: Type
intT = GroundType IntT

realT :: Type
realT = GroundType RealT


-- | Add type to an arbitrary structure
data Typed e = Typed {
    untyped :: (e (Typed e)),
    getType :: Type
  }

-- | Construct new typed expression preserving the type
preserveType :: (Typed e1 -> (e2 (Typed e2))) -> Typed e1 -> Typed e2
preserveType cons = (uncurry Typed) . (first cons) . (id &&& getType)

-- | Equality for * -> * kinds
class EqFunctor f where
  eqF :: Eq a => f a -> f a -> Bool

instance EqFunctor e => Eq (Typed e) where
  (Typed e1 t1) == (Typed e2 t2) = eqF e1 e2 && t1 == t2

-- | Show for * -> * kinds
class ShowFunctor f where
  showF :: Show a => f a -> String

instance ShowFunctor e => Show (Typed e) where
  show (Typed e t) = "(Typed (" ++ showF e ++ ") (" ++ show t ++ "))"
