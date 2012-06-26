{- Rewrite the structure of temporal operators
  in a program such that only constructs
  of the form
    e_1 -> pre e_2
  remain.
  
  This is done by using the following two rewrite systems:
  
  The first propagates "pre" upwards:
  1)
    * e_1 -> e_2 ~> e_1 -> e_2
    * pre e ~> pre e
    * fby(...) ~> unroll
    * f(pre e_1, ..., pre e_k) ~> pre f(e_1, ..., e_k) , f ∈ Σ
    * c ~> c ; x ~> x
    * N(e) ~> if N ≠ N' then pre N'(e) else N(e) , N => N'
  Where => is defined by:
    node N (p) returns (x : t) let
      ...
      x = pre e;
      ...
    tel
  =>
    node N (p) returns (y : t) let
      var x : t;
      ...
      x = pre e;
      y = e;
    tel
  
  The second moves uninitialised "pre" (s is a substitution Ident -> Expr):
  2)
    * x = pre x (s)~> (y = e, s[x ↦ pre y])
    * x (s)~> s(x)
  
  Those systems should be used in the following manner:
    (~>* (id)~>*)*
  Where * stands for: use as often as possible to get to a fixed point and
  id is the identity.
  
  Example 1:
    x = pre a + pre (0 -> pre b);
    y = 0 -> x;
  ~>
    x = pre (a + (0 -> pre b);
    y = 0 -> x;
  (s)~>
    z = a + (0 -> pre b); s' = s[x ↦ pre z]
    y = 0 -> x;
  (s')~>
    z = a + (0 -> pre b);
    y = 0 -> pre z;
  
  Example 2:
    node N (a : int) returns (x : int) let
      x = pre a;
    tel
    y = 0 -> N(a);
  ~>
    node N' (a : int) returns (y : int) let
      var x : int;
      x = pre a;
      y = a;
    tel
    y = 0 -> pre N'(a);
    
-}

module RewriteTemporal where

import Language.Scade.Syntax as S

rewrite :: [Declaration] -> [Declaration]
rewrite = id
