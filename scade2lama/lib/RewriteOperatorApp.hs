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

import Control.Monad (liftM)
import Control.Monad.State (StateT(..), modify)

import Language.Scade.Syntax as S

import VarGen

rewrite :: MonadVarGen m => [Declaration] -> m [Declaration]
rewrite = everywhereM (mkM rewriteDataDef)

-- | DataDef is the only place where we can put data flow, so
-- we start here.
rewriteDataDef :: MonadVarGen m => DataDef -> m DataDef
rewriteDataDef def =
  do (eqs', (extraEqs, extraVars)) <-
       (flip runStateT ([], [])) $ mapM rewriteEquation $ dataEquations def
     return $ def { dataLocals = dataLocals def ++ extraVars
                  , dataEquations = eqs' ++ extraEqs }

type RewrT = StateT ([Equation], [VarDecl])

rewriteEquation :: MonadVarGen m => Equation -> RewrT m Equation
rewriteEquation (SimpleEquation lhs expr) = liftM (SimpleEquation lhs) $ rewriteExprTop expr
rewriteEquation (AssertEquation assertType assertName expr) =
  liftM (AssertEquation assertType assertName) $ rewriteExprAll expr
rewriteEquation (EmitEquation (EmissionBody sigs (Just expr))) =
  liftM (EmitEquation . EmissionBody sigs . Just) $ rewriteExprAll expr
rewriteEquation (StateEquation sm returns retAll) =
  rewriteStateMachine sm >>= \sm' -> return $ StateEquation sm' returns retAll
rewriteEquation eq = return eq

-- | Avoid unrolling on top level
rewriteExprTop :: MonadVarGen m => Expr -> RewrT m Expr
rewriteExprTop (ApplyExpr op es) = liftM (ApplyExpr op) $ rewriteExprAll es
rewriteExprTop e = rewriteExprAll e

rewriteExpr :: MonadVarGen m => Expr -> RewrT m Expr
rewriteExpr app@(ApplyExpr _ _) =
  do appRes <- newVar "opresult"
     -- FIXME: we need the type of the operator here
     modify $ \(eqs, vs) -> ((SimpleEquation [Named appRes] app) : eqs, vs)
     return . IdExpr $ Path [appRes]
rewriteExpr e = return e

rewriteExprAll :: (MonadVarGen m, Data a) => a -> RewrT m a
rewriteExprAll = everywhereM $ mkM rewriteExpr

rewriteStateMachine :: MonadVarGen m => StateMachine -> RewrT m StateMachine
rewriteStateMachine (StateMachine smName states) =
  liftM (StateMachine smName) $ mapM rewriteState states

-- | Only rewrites transitions. The flow is already handled
-- earlier.
rewriteState :: MonadVarGen m => State -> RewrT m State
rewriteState s =
  do unless' <- mapM rewriteTransition $ stateUnless s
     until' <- mapM rewriteTransition $ stateUntil s
     return $ s { stateUnless = unless'
                , stateUntil = until' }

-- | Fixme: pull out from ActionEmission and ConditionalFork
rewriteTransition :: MonadVarGen m => Transition -> RewrT m Transition
rewriteTransition (Transition cond actions fork) =
  do cond' <- rewriteExprAll cond
     fork' <- rewriteFork fork
     return $ Transition cond' actions fork'

rewriteFork :: MonadVarGen m => Fork -> RewrT m Fork
rewriteFork f = return f
