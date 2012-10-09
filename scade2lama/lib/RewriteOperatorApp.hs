{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
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




import Data.Data
import Data.Generics.Schemes (everywhereM)
import Data.Generics.Aliases (mkM)
import Prelude hiding (mapM)
import Data.Traversable (mapM)

import Control.Monad (liftM)
import Control.Monad.State (StateT(..), modify)
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Monad.Error (MonadError(..))

import Language.Scade.Syntax as S

import VarGen
import ExtractPackages
import TransformMonads

rewrite :: (MonadError String m, MonadVarGen m) => Package -> m Package
rewrite ps = (flip runReaderT $ ScadePackages ps ps) $ rewritePackage ps

type RewrT = ReaderT ScadePackages
type LocalRewrT m = StateT ([Equation], [VarDecl]) (RewrT m)

rewritePackage :: (MonadError String m, MonadVarGen m) => Package -> RewrT m Package
rewritePackage p = local (\sps -> sps { current = p }) $
  do subP' <- mapM rewritePackage $ pkgSubPackages p
     userOps' <- mapM rewriteUserOp $ pkgUserOps p
     return $ p { pkgSubPackages = subP', pkgUserOps = userOps' }

rewriteUserOp :: (MonadError String m, MonadVarGen m) => Declaration -> RewrT m Declaration
rewriteUserOp d =
  do def' <- everywhereM (mkM rewriteDataDef) $ userOpContent d
     return $ d { userOpContent = def' }

-- | DataDef is the only place where we can put data flow, so
-- we start here.
rewriteDataDef :: (MonadError String m, MonadVarGen m) => DataDef -> RewrT m DataDef
rewriteDataDef def =
  do (eqs', (extraEqs, extraVars)) <-
       (flip runStateT ([], [])) $ mapM rewriteEquation $ dataEquations def
     return $ def { dataLocals = dataLocals def ++ extraVars
                  , dataEquations = eqs' ++ extraEqs }

rewriteEquation :: (MonadError String m, MonadVarGen m) => Equation -> LocalRewrT m Equation
rewriteEquation (SimpleEquation lhs expr) = liftM (SimpleEquation lhs) $ rewriteExprTop expr
rewriteEquation (AssertEquation assertType assertName expr) =
  liftM (AssertEquation assertType assertName) $ rewriteExprAll expr
rewriteEquation (EmitEquation (EmissionBody sigs (Just expr))) =
  liftM (EmitEquation . EmissionBody sigs . Just) $ rewriteExprAll expr
rewriteEquation (StateEquation sm returns retAll) =
  rewriteStateMachine sm >>= \sm' -> return $ StateEquation sm' returns retAll
rewriteEquation eq = return eq

-- | Avoid unrolling on top level
rewriteExprTop :: (MonadError String m, MonadVarGen m) => Expr -> LocalRewrT m Expr
rewriteExprTop (ApplyExpr op es) = liftM (ApplyExpr op) $ rewriteExprAll es
rewriteExprTop e = rewriteExprAll e

rewriteExpr :: (MonadError String m, MonadVarGen m) => Expr -> LocalRewrT m Expr
rewriteExpr app@(ApplyExpr (PrefixOp (PrefixPath p)) _) =
  do appRes <- newVar "opresult"
     t <- ask >>= \ps -> getOpType p [global ps, current ps]
     modify $ \(eqs, vs) -> ((SimpleEquation [Named appRes] app) : eqs,
                             (VarDecl [VarId appRes False False] t Nothing Nothing) : vs)
     return . IdExpr $ Path [appRes]
rewriteExpr e = return e

rewriteExprAll :: (MonadError String m, MonadVarGen m, Data a) => a -> LocalRewrT m a
rewriteExprAll = everywhereM $ mkM rewriteExpr

rewriteStateMachine :: (MonadError String m, MonadVarGen m) => StateMachine -> LocalRewrT m StateMachine
rewriteStateMachine (StateMachine smName states) =
  liftM (StateMachine smName) $ mapM rewriteState states

-- | Only rewrites transitions. The flow is already handled
-- earlier.
rewriteState :: (MonadError String m, MonadVarGen m) => State -> LocalRewrT m State
rewriteState s =
  do unless' <- mapM rewriteTransition $ stateUnless s
     until' <- mapM rewriteTransition $ stateUntil s
     return $ s { stateUnless = unless'
                , stateUntil = until' }

-- | Fixme: pull out from ActionEmission and ConditionalFork
rewriteTransition :: (MonadError String m, MonadVarGen m) => Transition -> LocalRewrT m Transition
rewriteTransition (Transition cond actions fork) =
  do cond' <- rewriteExprAll cond
     fork' <- rewriteFork fork
     return $ Transition cond' actions fork'

rewriteFork :: MonadVarGen m => Fork -> LocalRewrT m Fork
rewriteFork f = return f