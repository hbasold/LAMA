module Lang.LAMA.Fix where

import Prelude.Extras

-- | Add type to an arbitrary structure
data Fix x = Fix {
    unfix :: (x (Fix x))
  }

instance Eq1 x => Eq (Fix x) where
  (Fix e1) == (Fix e2) = e1 ==# e2

instance Show1 x => Show (Fix x) where
  show (Fix e) = "(Fix (" ++ show1 e ++ "))"
