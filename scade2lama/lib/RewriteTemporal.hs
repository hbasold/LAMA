{-# LANGUAGE TupleSections #-}

{- Rewrite the structure of temporal operators
  in a program such that only constructs
  of the form
    e_1 -> pre e_2
  remain.

  In the following e_1, e_2 are expression, Σ is the set
  of all operators that are lifted to streams (+, -, =, ...).
  
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
      x = pre y;
      y = e;
    tel
  
  The second moves uninitialised "pre" (s is a substitution Ident -> Expr):
  2)
    * x = pre e (s)~> (x = e, s[x ↦ pre x])
    * x (s)~> s(x)
  This must only be done if x is not an ouptut of an operator, i.e. a local
  variable.
  
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

import Data.Set as Set
import Data.Generics.Schemes
import Data.Generics.Aliases

import qualified Control.Monad.State as ST
import Control.Monad.State (MonadState(..), modify, runStateT)
import Control.Monad.Reader
import Control.Arrow (Arrow(..))

import Language.Scade.Syntax as S

import VarGen

rewrite :: [Declaration] -> VarGen [Declaration]
rewrite = fixUntil rewrite'
  where
    rewrite' :: [Declaration] -> VarGen ([Declaration], Bool)
    rewrite' ds =
      do (ds', f1) <- rewriteExprs ds
         (ds'', f2) <- rewriteAssigns ds'
         (ds''', f3) <- rewriteUninitOpOutputs ds''
         return (ds''', f1 && f2 && f3)

fixUntil :: Monad m => (a -> m (a, Bool)) -> a -> m a
fixUntil f x =
  do (y, finished) <- f x
     if finished then return y else fixUntil f y

rewriteExprs :: [Declaration] -> VarGen ([Declaration], Bool)
rewriteExprs ds = runStateT (mapM (everywhereM $ mkM rewriteExpr) ds) True

type RewrExprM = ST.StateT Bool VarGen
rewriteExpr :: Expr -> RewrExprM Expr
rewriteExpr (BinaryExpr o (UnaryExpr UnPre e1) (UnaryExpr UnPre e2))
  = put False >> return (UnaryExpr UnPre (BinaryExpr o e1 e2))
rewriteExpr e = return e

-- Works a bit different then in the description:
-- we do 2. for each scope in which variables can be declared (DataDef).
-- This gives us the required substitution which in then applied afterwards.
-- This ensures that each occurence of a variable is only replaced exactly once.
rewriteAssigns :: [Declaration] -> VarGen ([Declaration], Bool)
rewriteAssigns ds = runStateT (mapM (everywhereM $ mkM rewriteAssignsDataDef) ds) True

rewriteAssignsDataDef :: DataDef -> RewrExprM DataDef
rewriteAssignsDataDef def =
  do (eqs', (s, f')) <-
       get >>= \f -> lift
                     . flip runStateT (id, f)
                     . flip runReaderT (Set.fromList . getVars $ dataLocals def)
                     $ (mapM rewriteAssign $ dataEquations def)
     let eqs'' = everywhere (mkT s) eqs'
     state $ const (def { dataEquations = eqs'' }, f')
  where getVars = concat . fmap (fmap name . varNames)

type Substitution = Expr -> Expr
type RewrAssignM = ReaderT (Set String) (ST.StateT (Substitution, Bool) VarGen)
rewriteAssign :: Equation -> RewrAssignM Equation
rewriteAssign eq@(SimpleEquation [Named x] (UnaryExpr UnPre e)) =
  do inScope <- isInScope x
     if inScope
       then modify (second $ const False) >>
            modify (first (replace x (UnaryExpr UnPre $ IdExpr (Path [x])) .))  >>
            return (SimpleEquation [Named x] e)
       else return eq
rewriteAssign eq = return eq

replace :: String -> Expr -> Substitution
replace x e = \e' -> case e' of
  IdExpr (Path [y]) -> if x == y then e else e'
  _ -> e'

isInScope :: String -> RewrAssignM Bool
isInScope x = ask >>= return . Set.member x

-- | Implements relation =>
rewriteUninitOpOutputs :: [Declaration] -> VarGen ([Declaration], Bool)
rewriteUninitOpOutputs ds =
  do (ds', rewrittenNodes) <- runStateT (everywhereM (mkM rewriteOperatorOutput) ds) Set.empty
     if Set.null rewrittenNodes
       then return (ds', True)
       else return (everywhere (mkT $ rewriteOperatorEquation rewrittenNodes) ds', False)

rewriteOperatorEquation :: Set String -> Expr -> Expr
rewriteOperatorEquation uninitNodes app@(ApplyExpr (PrefixOp (PrefixPath p)) _)
  | p `isIn` uninitNodes = UnaryExpr UnPre app
  | otherwise = app
  where isIn (Path xs) s = (last xs) `Set.member` s
rewriteOperatorEquation _ e = e

type RewrOpOutpM = ST.StateT (Set String) VarGen
rewriteOperatorOutput :: Declaration -> RewrOpOutpM Declaration
rewriteOperatorOutput op@(UserOpDecl { userOpReturns = [xDecl] }) =
  case varNames xDecl of
    [xVar] ->
      let def = userOpContent op
          x = name xVar
      in
       do (eqs', my) <- lift $ runStateT (mapM (rewriteUninitOutput x) $ dataEquations def) Nothing
          case my of
            Nothing -> return op
            Just y ->
              -- x becomes now a local variable and y will be
              -- the new output (see module doc).
              let forward = SimpleEquation [Named x] (UnaryExpr UnPre $ IdExpr (Path [y]))
                  op' = op {
                    userOpReturns = [xDecl { varNames = [xVar { name = y }] }],
                    userOpContent = def {
                      dataLocals = xDecl : (dataLocals def),
                      dataEquations = forward : eqs'
                      }
                    }
              in modify (Set.insert $ userOpName op) >> return op'
    _ -> return op
rewriteOperatorOutput d = return d

type RewrOutpM = ST.StateT (Maybe String) VarGen
rewriteUninitOutput :: String -> Equation -> RewrOutpM Equation
rewriteUninitOutput outpX eq@(SimpleEquation [Named x] (UnaryExpr UnPre e))
  | x == outpX =
    do y <- newVar x
       put $ Just y
       return $ SimpleEquation [Named y] e
  | otherwise = return eq
rewriteUninitOutput _ eq = return eq