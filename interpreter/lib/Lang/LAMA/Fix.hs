module Lang.LAMA.Fix where

-- | Add type to an arbitrary structure
data Fix x = Fix {
    unfix :: (x (Fix x))
  }

-- | Equality for * -> * kinds
class EqFunctor f where
  eqF :: Eq a => f a -> f a -> Bool

instance EqFunctor x => Eq (Fix x) where
  (Fix e1) == (Fix e2) = eqF e1 e2

-- | Show for * -> * kinds
class ShowFunctor f where
  showF :: Show a => f a -> String

instance ShowFunctor x => Show (Fix x) where
  show (Fix e) = "(Fix (" ++ showF e ++ "))"
