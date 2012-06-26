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

import Control.Arrow
import Control.Applicative
import Data.Traversable
import Control.Monad.State hiding (State)
import qualified Control.Monad.State as M (State)

import Data.Map as Map hiding (map)

import Language.Scade.Syntax as S

rewrite :: [Declaration] -> [Declaration]
rewrite = map rewriteDecl

rewriteDecl :: Declaration -> Declaration
rewriteDecl (OpenDecl path) = OpenDecl path
rewriteDecl (TypeBlock decls) = TypeBlock decls
rewriteDecl (PackageDecl vis n decls) = PackageDecl vis n (rewrite decls)
rewriteDecl op@(UserOpDecl {}) =
  let typesInp = Map.fromList $ concat $ map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs]) $ userOpParams op
      typesOutp = Map.fromList $ concat $ map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs]) $ userOpReturns op
  in op { userOpContent = rewriteDataDef (Map.union typesInp typesOutp) $ userOpContent op }
rewriteDecl (ConstBlock consts) = ConstBlock $ map rewriteConstDecl consts

rewriteVarDecl :: VarDecl -> VarDecl
rewriteVarDecl (VarDecl ns t def lastVal) = VarDecl ns t def lastVal

rewriteConstDecl :: ConstDecl -> ConstDecl
rewriteConstDecl (ConstDecl ifSt n t val) = ConstDecl ifSt n t val

rewriteDataDef :: Map String TypeExpr -> DataDef -> DataDef
rewriteDataDef typesEnv (DataDef sigs locals equs) =
  let typesLocals = Map.fromList $ concat $ map (\(VarDecl xs t _ _) -> [(x,t) | (VarId x _ _) <- xs]) locals
      types = typesEnv `Map.union` typesLocals
      (vs, equs') = concat *** concat $ unzip $  map (rewriteEquation types) equs
      locals' = locals ++ vs
  in DataDef sigs locals' equs'

-- We may produce multiple equations out of one
rewriteEquation :: Map String TypeExpr -> Equation -> ([VarDecl], [Equation])
-- We only rewrite equations that do not use nodes
rewriteEquation ts (SimpleEquation [Named x] e) =
  let (xs, equs) = mkSubEquations x e
      decls = map (\y -> VarDecl [VarId y False False] (ts ! x) Nothing Nothing) xs
  in (decls, equs)
rewriteEquation _ (SimpleEquation [Bottom] e) = ([], [SimpleEquation [Bottom] e])
rewriteEquation ts (StateEquation sm rets returnsAll) = ([], [StateEquation (rewriteStateMachine ts sm) rets returnsAll])
rewriteEquation _ eq = ([], [eq])

type SubEqM = M.State (String, (Int, [Equation]))

freshVar :: SubEqM String
freshVar = do
  (x, (k, eqs)) <- get
  put (x, (k+1, eqs))
  return $ x ++ "_" ++ show k

putEq :: Equation -> SubEqM ()
putEq e = modify (second $ second (e:))

-- TODO: do not unroll top level pre constructs
mkSubEquations :: String -> Expr -> ([String], [Equation])
mkSubEquations x expr =
  let (expr', (_, (k, subs))) = runState (mkSubEquations' expr) (x, (1, []))
      newVars = map (\i -> x ++ "_" ++ show i) [1..k-1]
  in (newVars, (SimpleEquation [Named x] expr') : subs)
  where
    -- We require temporal constructs to
    -- be of the form e1 -> pre e2 where
    -- e1 and e2 are expressions.
    mkSubEquations' :: Expr -> SubEqM Expr
    mkSubEquations' (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)) = do
      e2' <- mkSubEquations' e2
      x' <- freshVar
      putEq $ SimpleEquation [Named x'] (S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2'))
      return $ IdExpr $ Path [x']

    mkSubEquations' (IdExpr path) = pure $ IdExpr path
    mkSubEquations' (NameExpr n) = pure $ NameExpr n
    mkSubEquations' (LastExpr z) = pure $ LastExpr z
    mkSubEquations' (ConstIntExpr c) = pure $ ConstIntExpr c
    mkSubEquations' (ConstBoolExpr c) = pure $ ConstBoolExpr c
    mkSubEquations' (ConstFloatExpr c) = pure $ ConstFloatExpr c
    mkSubEquations' (ConstPolyIntExpr i s) = pure $ ConstPolyIntExpr i s
    mkSubEquations' (BinaryExpr op e1 e2) = BinaryExpr op <$> mkSubEquations' e1 <*> mkSubEquations' e2
    mkSubEquations' (UnaryExpr op e) = UnaryExpr op <$> mkSubEquations' e
    mkSubEquations' (ListExpr es) = ListExpr <$> traverse mkSubEquations' es
    mkSubEquations' (ArrayExpr es) = ArrayExpr <$> traverse mkSubEquations' es
    mkSubEquations' (IfExpr c e1 e2) = IfExpr <$> mkSubEquations' c <*> mkSubEquations' e1 <*> mkSubEquations' e2
    mkSubEquations' (ApplyExpr op es) = ApplyExpr op <$> traverse mkSubEquations' es
    mkSubEquations' (FBYExpr es1 e es2) = FBYExpr <$> traverse mkSubEquations' es1 <*> mkSubEquations' e <*> traverse mkSubEquations' es2
    mkSubEquations' (ReverseExpr e) = ReverseExpr <$> mkSubEquations' e
    mkSubEquations' (CaseExpr e ps) = CaseExpr <$> mkSubEquations' e <*> pure ps
    mkSubEquations' (IndexExpr e1 e2) = IndexExpr <$> mkSubEquations' e1 <*> mkSubEquations' e2
    mkSubEquations' (DefaultIndexExpr e1 es e2) = DefaultIndexExpr <$> mkSubEquations' e1 <*> traverse mkSubEquations' es <*> mkSubEquations' e2
    mkSubEquations' (StaticProjectionExpr e1 e2 e3) = StaticProjectionExpr <$> mkSubEquations' e1 <*> mkSubEquations' e2 <*> mkSubEquations' e3
    mkSubEquations' (AppendExpr e1 e2) = AppendExpr <$> mkSubEquations' e1 <*> mkSubEquations' e2
    mkSubEquations' (TransposeExpr e i1 i2) = TransposeExpr <$> mkSubEquations' e <*> pure i1 <*> pure i2
    mkSubEquations' (TimesExpr e1 e2) = TimesExpr <$> mkSubEquations' e1 <*> mkSubEquations' e2

rewriteEmissionBody :: EmissionBody -> EmissionBody
rewriteEmissionBody (EmissionBody s e) = EmissionBody s e

rewriteStateMachine :: Map String TypeExpr -> StateMachine -> StateMachine
rewriteStateMachine ts (StateMachine n states) = StateMachine n (map (rewriteState ts) states)

rewriteState :: Map String TypeExpr -> State -> State
rewriteState ts s
  = s { stateData = rewriteDataDef ts $ stateData s,
        stateUnless = map (rewriteTransition ts) $ stateUnless s,
        stateUntil = map (rewriteTransition ts) $ stateUntil s,
        stateSynchro = fmap ((fmap $ rewriteActions ts) *** rewriteFork ts) $ stateSynchro s
      }

rewriteTransition :: Map String TypeExpr -> Transition -> Transition
rewriteTransition ts (Transition e act fork) = Transition e (fmap (rewriteActions ts) act) (rewriteFork ts fork)

rewriteActions :: Map String TypeExpr -> Actions -> Actions
rewriteActions _ (ActionEmission bodies) = ActionEmission $ map (id *** rewriteEmissionBody) bodies
rewriteActions ts (ActionDef def) = ActionDef $ rewriteDataDef ts def

rewriteFork :: Map String TypeExpr -> Fork -> Fork
rewriteFork _ (TargetFork t n) = TargetFork t n
rewriteFork ts (ConditionalFork trs sync)
  = ConditionalFork
      (map (\(e, a, f) -> (e, fmap (rewriteActions ts) a, rewriteFork ts f)) trs)
      (fmap ((fmap $ rewriteActions ts) *** rewriteFork ts) sync)

rewriteIfBlock :: Map String TypeExpr -> IfBlock -> IfBlock
rewriteIfBlock ts (IfBlock e b1 b2) = IfBlock e (rewriteDataDef ts +++ rewriteIfBlock ts $ b1) (rewriteDataDef ts +++ rewriteIfBlock ts $ b2)

rewriteMatchBlock :: Map String TypeExpr -> MatchBlock -> MatchBlock
rewriteMatchBlock ts (MatchBlock e cases) = MatchBlock e (map (id *** rewriteDataDef ts) cases)
