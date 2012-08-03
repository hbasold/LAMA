{- Unrolls temporal constructs. We do that by the following rules:
  
  * x = e_1 -> pre e_2 ~> e_1 -> pre e_2
  * x = e ~>
      x_1 = e_1;
      ...
      x_k = e_k;
      x = e';
    where [] ⊢ e => (e', [(x_1, e_1), ..., (x_k, e_k)])
  
  Where => is defined by:
  * Γ ⊢ e_1 -> pre e_2 => (x', Γ ∪ [(x', e_1 -> pre e_2)]) , x' ∉ Γ
  * Γ ⊢ pre e => (x', Γ ∪ [(x', pre e)]) , x' ∉ Γ
  
  Example:
    z = a + (0 -> pre (b + 1));
    y = 0 -> pre (z + b);
  ~>
    z_1 = 0 -> pre (b + 1); -- first temporal subexpression in z
    z = a + z_1;
    y = 0 -> pre (z + b);
  
    This gives in LAMA:
    z_1' = (+ b 1)
    z = (+ a z_1)
    y' = z + b
    initial z_1 = 0, y = 0
-}

module UnrollTemporal where

import Control.Monad ((>=>))
import Control.Arrow

import Prelude hiding (mapM)
import Data.Traversable
import Control.Monad.State (StateT(..), MonadState(..), modify)
import Data.Generics.Schemes
import Data.Generics.Aliases

import Data.Map as Map hiding (map)

import Language.Scade.Syntax as S

import VarGen

rewrite :: [Declaration] -> VarGen [Declaration]
rewrite = everywhereM $ mkM rewriteDecl

rewriteDecl :: Declaration -> VarGen Declaration
rewriteDecl op@(UserOpDecl {}) =
  let typesInp = Map.fromList
                 . concat
                 . map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs])
                 $ userOpParams op
      typesOutp = Map.fromList
                  . concat
                  . map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs])
                  $ userOpReturns op
  in do cont' <- rewriteDataDef (Map.union typesInp typesOutp) $ userOpContent op
        return $ op { userOpContent = cont' }
rewriteDecl d = return d

rewriteDataDef :: Map String TypeExpr -> DataDef -> VarGen DataDef
rewriteDataDef typesEnv (DataDef sigs locals equs) =
  let typesLocals = Map.fromList $ concat $ map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs]) locals
      types = typesEnv `Map.union` typesLocals
  in do (vs, equs') <- fmap ((concat *** concat) . unzip) $ mapM (rewriteEquation types) equs
        let locals' = locals ++ vs
        return $ DataDef sigs locals' equs'

-- We may produce multiple equations out of one
rewriteEquation :: Map String TypeExpr -> Equation -> VarGen ([VarDecl], [Equation])
-- We only rewrite equations that do not use nodes
rewriteEquation ts (SimpleEquation [Named x] e) =
  do (xs, equs) <- mkSubEquations x e
     let decls = map (\y -> VarDecl [VarId y False False] (ts ! x) Nothing Nothing) xs
     return (decls, equs)
rewriteEquation _ eq = return ([], [eq])

-- | Transports the name of the variable for which the current
-- equation is rewritten (just to have a prefix for the generated
-- variables). It also holds the pulled out equations
-- and the generated variables.
type SubEqM = StateT (String, ([Equation], [String])) VarGen

freshVar :: SubEqM String
freshVar = do
  (x, (_, _)) <- get
  x' <- newVar x
  modify (second $ second (x':))
  return x'

putEq :: Equation -> SubEqM ()
putEq e = modify (second $ first (e:))

mkSubEquations :: String -> Expr -> VarGen ([String], [Equation])
mkSubEquations x expr =
  do (expr', (_, (subs, newVars))) <- runStateT (mkSubEquationsTop expr) (x, ([], []))
     return (newVars, (SimpleEquation [Named x] expr') : subs)
  where
    -- Avoid unrolling on top level
    mkSubEquationsTop :: Expr -> SubEqM Expr
    mkSubEquationsTop (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)) =
      do e2' <- mkSubEquations' e2
         return $ S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2')
    mkSubEquationsTop (S.UnaryExpr S.UnPre e) =
      do e' <- mkSubEquations' e
         return $ S.UnaryExpr S.UnPre e'
    mkSubEquationsTop e = mkSubEquations' e

    -- first pull out initialised pre's because a pre alone is a sub-pattern and
    -- with everywhere this leads to pulled out pre's but left after's.
    mkSubEquations' :: Expr -> SubEqM Expr
    mkSubEquations' = (everywhereM $ mkM mkEqInitPre) >=> (everywhereM $ mkM mkEqUninitPre)

    mkEqInitPre (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)) = do
      e2' <- everywhereM (mkM mkEqUninitPre) e2
      x' <- freshVar
      putEq $ SimpleEquation [Named x'] (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2'))
      return $ IdExpr $ Path [x']
    mkEqInitPre e = return e

    mkEqUninitPre (S.UnaryExpr S.UnPre e) = do
      x' <- freshVar
      putEq $ SimpleEquation [Named x'] (S.UnaryExpr S.UnPre e)
      return $ IdExpr $ Path [x']
    mkEqUninitPre e = return e
