{- Unrolls temporal constructs. We do that by the following rules:
  
  * x = e_1 -> pre e_2 ~> e_1 -> pre e_2
  * x = e ~>
      x_1 = e_1;
      ...
      x_k = e_k;
      x = e';
    where [] ⊢ e => (e', [(x_1, e_1), ..., (x_k, e_k)])
  
  Where => is defined by:
  * Γ ⊢ e_1 -> pre e_2 => (e_1 -> pre x, Γ ∪ [(x, e_2)]) , x ∉ Γ
  
  Example:
    z = a + (0 -> pre b);
    y = 0 -> pre (z + b);
  ~>
    b_1 = 0 -> pre b;
    z = a + b_1;
    y = 0 -> pre (z + b);
  
    This gives in LAMA:
    b_1' = b
    z = (+ a b_1)
    y' = z + b
    initial b_1 = 0, y = 0
-}

module UnrollTemporal where

import Language.Scade.Syntax as S

rewrite :: [Declaration] -> [Declaration]
rewrite = id
