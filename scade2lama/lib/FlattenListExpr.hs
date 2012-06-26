{- The parser generates list expressions every time
  an expression in parenthesis is found.
  We flatten this structure here.
-}

module FlattenListExpr (rewrite) where

import Control.Arrow
import Control.Applicative
import Data.Functor.Identity
import Data.Traversable

import Language.Scade.Syntax as S

rewrite :: [Declaration] -> [Declaration]
rewrite = map rewriteDecl

rewriteDecl :: Declaration -> Declaration
rewriteDecl (OpenDecl path) = OpenDecl path
rewriteDecl (TypeBlock decls) = TypeBlock decls
rewriteDecl (PackageDecl vis n decls) = PackageDecl vis n (rewrite decls)
rewriteDecl op@(UserOpDecl {}) =
  op { userOpParams = map rewriteVarDecl $ userOpParams op,
        userOpReturns = map rewriteVarDecl $ userOpReturns op,
        userOpContent = rewriteDataDef $ userOpContent op
      }
rewriteDecl (ConstBlock consts) = ConstBlock $ map rewriteConstDecl consts

rewriteVarDecl :: VarDecl -> VarDecl
rewriteVarDecl (VarDecl ns t def lastVal) = VarDecl ns t (fmap rewriteExpr def) (fmap rewriteExpr lastVal)

rewriteConstDecl :: ConstDecl -> ConstDecl
rewriteConstDecl (ConstDecl ifSt n t val) = ConstDecl ifSt n t (fmap rewriteExpr val)

rewriteDataDef :: DataDef -> DataDef
rewriteDataDef (DataDef sigs locals equs) = DataDef sigs (map rewriteVarDecl locals) (map rewriteEquation equs)

rewriteEquation :: Equation -> Equation
rewriteEquation (SimpleEquation pat e) = SimpleEquation pat (rewriteExpr e)
rewriteEquation (AssertEquation t n e) = AssertEquation t n (rewriteExpr e)
rewriteEquation (EmitEquation body) = EmitEquation $ rewriteEmissionBody body
rewriteEquation (StateEquation sm ret returnsAll) = StateEquation (rewriteStateMachine sm) ret returnsAll
rewriteEquation (ClockedEquation n block ret returnsAll) = ClockedEquation n (rewriteIfBlock +++ rewriteMatchBlock $ block) ret returnsAll

rewriteEmissionBody :: EmissionBody -> EmissionBody
rewriteEmissionBody (EmissionBody s e) = EmissionBody s (fmap rewriteExpr e)

rewriteStateMachine :: StateMachine -> StateMachine
rewriteStateMachine (StateMachine n states) = StateMachine n (map rewriteState states)

rewriteState :: State -> State
rewriteState s
  = s { stateData = rewriteDataDef $ stateData s,
        stateUnless = map rewriteTransition $ stateUnless s,
        stateUntil = map rewriteTransition $ stateUntil s,
        stateSynchro = fmap ((fmap rewriteActions) *** rewriteFork) $ stateSynchro s
      }

rewriteTransition :: Transition -> Transition
rewriteTransition (Transition e act fork) = Transition (rewriteExpr e) (fmap rewriteActions act) (rewriteFork fork)

rewriteActions :: Actions -> Actions
rewriteActions (ActionEmission bodies) = ActionEmission $ map (id *** rewriteEmissionBody) bodies
rewriteActions (ActionDef def) = ActionDef $ rewriteDataDef def

rewriteFork :: Fork -> Fork
rewriteFork (TargetFork t n) = TargetFork t n
rewriteFork (ConditionalFork trs sync)
  = ConditionalFork
      (map (\(e, a, f) -> (rewriteExpr e, fmap rewriteActions a, rewriteFork f)) trs)
      (fmap ((fmap rewriteActions) *** rewriteFork) sync)

rewriteIfBlock :: IfBlock -> IfBlock
rewriteIfBlock (IfBlock e b1 b2) = IfBlock (rewriteExpr e) (rewriteDataDef +++ rewriteIfBlock $ b1) (rewriteDataDef +++ rewriteIfBlock $ b2)

rewriteMatchBlock :: MatchBlock -> MatchBlock
rewriteMatchBlock (MatchBlock e cases) = MatchBlock (rewriteExpr e) (map (id *** rewriteDataDef) cases)

rewriteExpr :: Expr -> Expr
rewriteExpr = runIdentity . rewriteExpr'
  where
    rewriteExpr' (IdExpr path) = pure $ IdExpr path
    rewriteExpr' (NameExpr n) = pure $ NameExpr n
    rewriteExpr' (LastExpr x) = pure $ LastExpr x
    rewriteExpr' (ConstIntExpr c) = pure $ ConstIntExpr c
    rewriteExpr' (ConstBoolExpr c) = pure $ ConstBoolExpr c
    rewriteExpr' (ConstFloatExpr c) = pure $ ConstFloatExpr c
    rewriteExpr' (ConstPolyIntExpr i s) = pure $ ConstPolyIntExpr i s
    rewriteExpr' (BinaryExpr op e1 e2) = BinaryExpr op <$> rewriteExpr' e1 <*> rewriteExpr' e2
    rewriteExpr' (UnaryExpr op e) = UnaryExpr op <$> rewriteExpr' e
    -- Here is the point of all this:
    rewriteExpr' (ListExpr [e]) = rewriteExpr' e
    rewriteExpr' (ListExpr es) = ListExpr <$> traverse rewriteExpr' es

    rewriteExpr' (ArrayExpr es) = ArrayExpr <$> traverse rewriteExpr' es
    rewriteExpr' (IfExpr c e1 e2) = IfExpr <$> rewriteExpr' c <*> rewriteExpr' e1 <*> rewriteExpr' e2
    rewriteExpr' (ApplyExpr op es) = ApplyExpr op <$> traverse rewriteExpr' es
    rewriteExpr' (FBYExpr es1 e es2) = FBYExpr <$> traverse rewriteExpr' es1 <*> rewriteExpr' e <*> traverse rewriteExpr' es2
    rewriteExpr' (ReverseExpr e) = ReverseExpr <$> rewriteExpr' e
    rewriteExpr' (CaseExpr e ps) = CaseExpr <$> rewriteExpr' e <*> pure ps
    rewriteExpr' (IndexExpr e1 e2) = IndexExpr <$> rewriteExpr' e1 <*> rewriteExpr' e2
    rewriteExpr' (DefaultIndexExpr e1 es e2) = DefaultIndexExpr <$> rewriteExpr' e1 <*> traverse rewriteExpr' es <*> rewriteExpr' e2
    rewriteExpr' (StaticProjectionExpr e1 e2 e3) = StaticProjectionExpr <$> rewriteExpr' e1 <*> rewriteExpr' e2 <*> rewriteExpr' e3
    rewriteExpr' (AppendExpr e1 e2) = AppendExpr <$> rewriteExpr' e1 <*> rewriteExpr' e2
    rewriteExpr' (TransposeExpr e i1 i2) = TransposeExpr <$> rewriteExpr' e <*> pure i1 <*> pure i2
    rewriteExpr' (TimesExpr e1 e2) = TimesExpr <$> rewriteExpr' e1 <*> rewriteExpr' e2
