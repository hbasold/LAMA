{-# LANGUAGE FlexibleContexts #-}
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
import Data.Map as Map hiding (map)

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad (liftM)
import Control.Monad.State (StateT(..), MonadState(..), modify)
import Control.Applicative (Applicative)
import Control.Monad.Error (MonadError)

import Language.Scade.Syntax as S

import VarGen
import TransformCommon (tryConst)

rewrite :: (MonadVarGen m, Applicative m, MonadError String m)
           => [Declaration] -> m [Declaration]
rewrite = everywhereM $ mkM rewriteDecl

rewriteDecl :: (MonadVarGen m, Applicative m, MonadError String m)
               => Declaration -> m Declaration
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

rewriteDataDef :: (MonadVarGen m, Applicative m, MonadError String m)
                  => Map String TypeExpr -> DataDef -> m DataDef
rewriteDataDef typesEnv (DataDef sigs locals equs) =
  let typesLocals = Map.fromList $ concat $ map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs]) locals
      types = typesEnv `Map.union` typesLocals
  in do (vs, equs') <- liftM ((concat *** concat) . unzip) $ mapM (rewriteEquation types) equs
        let locals' = locals ++ vs
        return $ DataDef sigs locals' equs'

-- We may produce multiple equations out of one
rewriteEquation :: (MonadVarGen m, Applicative m, MonadError String m)
                   => Map String TypeExpr -> Equation -> m ([VarDecl], [Equation])
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
type SubEqM = StateT (String, ([Equation], [String]))

freshVar :: MonadVarGen m => SubEqM m String
freshVar = do
  (x, (_, _)) <- get
  x' <- newVar x
  modify (second $ second (x':))
  return x'

putEq :: (MonadVarGen m, Applicative m, MonadError String m) => Equation -> SubEqM m ()
putEq e = modify (second $ first (e:))

mkSubEquations :: (MonadVarGen m, Applicative m, MonadError String m) => String -> Expr -> m ([String], [Equation])
mkSubEquations x expr =
  do (expr', (_, (subs, newVars))) <- runStateT (mkSubEquationsTop expr) (x, ([], []))
     return (newVars, (SimpleEquation [Named x] expr') : subs)
  where
    -- Avoid unrolling on top level
    mkSubEquationsTop :: (MonadVarGen m, Applicative m, MonadError String m) => Expr -> SubEqM m Expr
    mkSubEquationsTop (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)) =
      do e2' <- mkSubEquations' e2
         return $ S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2')
    mkSubEquationsTop (S.UnaryExpr S.UnPre e) =
      do e' <- mkSubEquations' e
         return $ S.UnaryExpr S.UnPre e'
    mkSubEquationsTop (S.BinaryExpr S.BinAfter e1 e2) =
      do e2' <- mkSubEquations' e2
         return $ S.BinaryExpr S.BinAfter e1 e2'
    mkSubEquationsTop e = mkSubEquations' e

    -- first pull out initialised pre's because a pre alone is a sub-pattern and
    -- with everywhere this leads to pulled out pre's but left after's.
    mkSubEquations' :: (MonadVarGen m, Applicative m, MonadError String m) => Expr -> SubEqM m Expr
    mkSubEquations' = (everywhereM $ mkM mkEqInitPre) >=> (everywhereM $ mkM mkEqSeparated)

    -- if the initialisation is a constant, we pull the
    -- expression out. Otherwise we let mkEqSeparated do the work.
    mkEqInitPre e@(S.BinaryExpr S.BinAfter i (S.UnaryExpr S.UnPre _)) =
      do isC <- isConstant i
         if isC then
           do x' <- freshVar
              putEq $ SimpleEquation [Named x'] e
              return $ IdExpr $ Path [x']
           else return e
      where
        isConstant e' = tryConst e' >>= return . (const True ||| const False)
    mkEqInitPre e = return e

    mkEqSeparated e@(S.UnaryExpr S.UnPre _) = do
      x' <- freshVar
      putEq $ SimpleEquation [Named x'] e
      return $ IdExpr $ Path [x']
    mkEqSeparated e@(S.BinaryExpr S.BinAfter _ _) = do
      x' <- freshVar
      putEq $ SimpleEquation [Named x'] e
      return $ IdExpr $ Path [x']
    mkEqSeparated e = return e
