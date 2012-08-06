{- Rewrites the program stucture s.t. an operator
  is only applied outside of any expression.
  
  Rules:
    * x = N(e); ~> x = N(e);
    * x = e;
      ~>
        n_1 = N_1(e_1);
        ...
        n_k = N_k(e_k);
        x = e';
      , e []=> (e', [N_1(e_1), ..., N_k(e_k)])
    
    For =>:
    * N(e) [[N_1(e_1), ..., N_k(e_k)]=> (n_(k+1), [N_1(e_1), ..., N_k(e_k), N(e)])
-}

module RewriteOperatorApp where

import Language.Scade.Syntax as S

import VarGen

rewrite :: MonadVarGen m => [Declaration] -> m [Declaration]
rewrite = return
