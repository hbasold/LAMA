{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

{-| Feeding LAMA programs to the SMT solver -}

module Transform where

import Development.Placeholders

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Types
import Language.SMTLib2 as SMT
import Language.SMTLib2.Internals (SMTExpr(Fun))

import Data.Natural
import NatInstance ()
import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable

import Control.Monad.State (StateT, MonadState(..), evalStateT, modify)

import Control.Monad.Error (ErrorT(..), MonadError(..))
import Control.Monad.Reader (ReaderT(..), MonadReader(..), asks)
import Control.Applicative (Applicative(..), (<$>))

{-
type TypedExpr i = SMTExpr (TypeWrap i)

instance Ident i => SMTType (TypeWrap i) where
  type SMTAnnotation (TypeWrap i) = (Type i)
  getSort _ t = L.Symbol $ typeStr t
    where
      typeStr (GroundType BoolT) = "Bool"
      typeStr (GroundType IntT) = "Int"
      typeStr (GroundType RealT) = "Real"
      typeStr _ = error "type not implemented"
  declareType u _ = [(typeOf u, return ())]

instance Ident i => SMTValue (TypeWrap i) where
  unmangle v (GroundType BoolT)  =
    do v' <- unmangle v undefined :: SMT (Maybe Bool)
       return $ fmap BoolExpr v'
  unmangle v (GroundType IntT) =
    do v' <- unmangle v undefined :: SMT (Maybe Integer)
       return $ fmap IntExpr v'
  unmangle v (GroundType RealT) =
    do v' <- unmangle v undefined :: SMT (Maybe Rational)
       return $ fmap RealExpr v'
  unmangle _ _ = return Nothing

  mangle (BoolExpr v) _ = mangle v undefined
  mangle (IntExpr v) _ = mangle v undefined
  mangle (RealExpr v) _ = mangle v undefined
-}
{-
type StreamPos = SMTExpr Natural
type Stream t = SMTExpr (SMTFun StreamPos t)
type TypedStream i = Stream (TypeWrap i)

type Definition = Stream Bool
-}

succ' :: (SMTValue t, Enum t) => SMTExpr t -> SMTExpr t
succ' e = Fun "succ" (extractAnnotation e) (extractAnnotation e) `app` e 

data TypedExpr i
  = BoolExpr { unBool :: SMTExpr Bool }
  | IntExpr { unInt :: SMTExpr Integer }
  | RealExpr { unReal :: SMTExpr Rational }
  deriving (Eq, Show)

type StreamPos = SMTExpr Natural
type Stream t = SMTExpr (SMTFun StreamPos t)
data TypedStream i
  = BoolStream (Stream Bool)
  | IntStream (Stream Integer)
  | RealStream (Stream Rational)

type Definition = Stream Bool

ensureDefinition :: TypedStream i -> Definition
ensureDefinition (BoolStream s) = s
ensureDefinition _ = error "ensureDefinition: not a boolean stream"

defStream :: Type i -> (StreamPos -> TypedExpr i) -> SMT (TypedStream i)
defStream (GroundType BoolT) f = fmap BoolStream $ defFun (unBool . f)
defStream (GroundType IntT) f = fmap IntStream $ defFun (unInt . f)
defStream (GroundType RealT) f = fmap RealStream $ defFun (unReal . f)
defStream _ _ = $notImplemented

appStream :: TypedStream i -> StreamPos -> TypedExpr i
appStream (BoolStream s) n = BoolExpr $ s `app` n
appStream (IntStream s) n = IntExpr $ s `app` n
appStream (RealStream s) n = RealExpr $ s `app` n

liftRel :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool)
           -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftRel r (BoolExpr e1) (BoolExpr e2) = BoolExpr $ r e1 e2
liftRel r (IntExpr e1) (IntExpr e2) = BoolExpr $ r e1 e2
liftRel r (RealExpr e1) (RealExpr e2) = BoolExpr $ r e1 e2
liftRel _ _ _ = error "liftRel: argument types don't match"

lift1Bool :: (SMTExpr Bool -> SMTExpr Bool) -> TypedExpr i -> TypedExpr i
lift1Bool f (BoolExpr e) = BoolExpr $ f e
lift1Bool _ _ = error "lift1Bool: argument is not boolean"

lift2 :: (forall a. SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr a)
         -> TypedExpr i -> TypedExpr i -> TypedExpr i
lift2 f (BoolExpr e1) (BoolExpr e2) = BoolExpr $ f e1 e2
lift2 f (IntExpr e1) (IntExpr e2) = IntExpr $ f e1 e2
lift2 f (RealExpr e1) (RealExpr e2) = RealExpr $ f e1 e2
lift2 _ _ _ = error "lift2: argument types don't match"

liftIte :: TypedExpr i -> TypedExpr i -> TypedExpr i -> TypedExpr i
liftIte (BoolExpr c) = lift2 (ite c)
liftIte _ = error "liftIte: condition is not boolean"

data NodeEnv i = NodeEnv
                 { nodeEnvIn :: [TypedStream i]
                 , nodeEnvOut :: [TypedStream i]
                 }

data VarEnv i = VarEnv
                { nodes :: Map i (NodeEnv i)
                  -- | Maps names of variables to a SMT expression for using that variable
                , vars :: Map i (TypedStream i)
                }

data Env i = Env
           { constants :: Map i (TypedExpr i)
           , varEnv :: VarEnv i
           }

emptyVarEnv :: VarEnv i
emptyVarEnv = VarEnv Map.empty Map.empty

emptyEnv :: Env i
emptyEnv = Env Map.empty emptyVarEnv

type DeclM i = StateT (Env i) (ErrorT String SMT)

putConstants :: Ident i => Map i (Constant i) -> DeclM i ()
putConstants cs =
  let cs' = fmap trConstant cs
  in modify $ \env -> env { constants = cs' }

modifyVarEnv :: (VarEnv i -> VarEnv i) -> DeclM i ()
modifyVarEnv f = modify $ \env -> env { varEnv = f $ varEnv env }

modifyNodes :: (Map i (NodeEnv i) -> Map i (NodeEnv i)) -> DeclM i ()
modifyNodes f = modifyVarEnv $ (\env -> env { nodes = f $ nodes env })

modifyVars :: (Map i (TypedStream i) -> Map i (TypedStream i)) -> DeclM i ()
modifyVars f = modifyVarEnv $ (\env -> env { vars = f $ vars env })

lookupVar :: Ident i => i -> DeclM i (TypedStream i)
lookupVar x =
  do vs <- fmap (vars . varEnv) $ get
     case Map.lookup x vs of
       Nothing -> throwError $ "Unknown variable " ++ identPretty x
       Just x' -> return x'

localVarEnv :: (VarEnv i -> VarEnv i) -> DeclM i a -> DeclM i a
localVarEnv f m =
  do curr <- get
     modifyVarEnv f
     r <- m
     put curr
     return r

data ProgDefs = ProgDefs
                { flowDef :: [Definition]
                , invariantDef :: Definition
                }

lamaSMT :: Ident i => Program i -> ErrorT String SMT ProgDefs
lamaSMT = flip evalStateT emptyEnv . declProgram 

declProgram :: Ident i => Program i -> DeclM i ProgDefs
declProgram p =
  do preamble
     putConstants (progConstantDefinitions p)
     declareEnums (progEnumDefinitions p)
     declDefs <- declareDecls (progDecls p)
     flowDefs <- declareFlow (progFlow p)
     assertInits (progInitial p)
     assertPrecond (progAssertion p)
     invarDef <- declareInvariant (progInvariant p)
     return $ ProgDefs (declDefs ++ flowDefs) invarDef

preamble :: DeclM i ()
preamble = return ()

trConstant :: Ident i => Constant i -> TypedExpr i
trConstant (untyped -> BoolConst c) = BoolExpr $ constant c
trConstant (untyped -> IntConst c) = IntExpr $ constant c
trConstant (untyped -> RealConst c) = RealExpr $ constant c
trConstant (untyped -> SIntConst n c) = $notImplemented
trConstant (untyped -> UIntConst n c) = $notImplemented

declareEnums :: Map (TypeAlias i) (EnumDef i) -> DeclM i ()
declareEnums _ = return ()

declareDecls :: Ident i => Declarations i -> DeclM i [Definition]
declareDecls d =
  do r <- mapM (localVarEnv (const emptyVarEnv) . declareNode) $ declsNode d
     let (defs, interface) = splitIfDefs r
     modifyNodes $ Map.union interface
     locs <- declareVars $ declsLocal d
     states <- declareVars $ declsState d
     modifyVars $ Map.union (locs `Map.union` states)
     return defs
  where
    splitIfDefs = mapAccumL (\ds (x, ds') -> (ds' ++ ds, x)) [] 

declareVars :: Ident i => [Variable i] -> DeclM i (Map i (TypedStream i))
declareVars = fmap Map.fromList . mapM declareVar

declareVar :: Ident i => Variable i -> DeclM i (i, TypedStream i)
declareVar (Variable x t) =
  do x' <- liftSMT $ typedVar t
     return (x, x')
  where
    typedVar :: Type i -> SMT (TypedStream i)
    typedVar (GroundType BoolT) = fmap BoolStream fun
    typedVar (GroundType IntT) = fmap IntStream fun
    typedVar (GroundType RealT) = fmap RealStream fun
    typedVar _ = $notImplemented

declareNode :: Ident i => Node i -> DeclM i (NodeEnv i, [Definition])
declareNode n =
  do declDefs <- declareDecls $ nodeDecls n
     ins <- declareVars $ nodeInputs n
     outs <- declareVars $ nodeOutputs n
     modifyVars $ Map.union (ins `Map.union` outs)
     flowDefs <- declareFlow $ nodeFlow n
     outDefs <- mapM declareInstantDef $ nodeOutputDefs n
     automDefs <- fmap concat . mapM declareAutomaton . Map.elems $ nodeAutomata n
     assertInits $ nodeInitial n
     return (NodeEnv (Map.elems ins) (Map.elems outs),
             declDefs ++ flowDefs ++ outDefs ++ automDefs)

declareInstantDef :: Ident i => InstantDefinition i -> DeclM i Definition
declareInstantDef (InstantDef x e) = declareDef id x (trInstant e)

declareDef :: Ident i => (StreamPos -> StreamPos) -> i -> TransM i (TypedExpr i) -> DeclM i Definition
declareDef f x em =
  do x' <- lookupVar x
     env <- get
     s <- liftSMT . defStream boolT $ \t ->
       let e = runTransM em t env
       in liftRel (.==.) (x' `appStream` (f t)) e
     return $ ensureDefinition s

declareTransition :: Ident i => StateTransition i -> DeclM i Definition
declareTransition (StateTransition x e) = declareDef succ' x (trExpr e)

declareFlow :: Ident i => Flow i -> DeclM i [Definition]
declareFlow f =
  do defDefs <- mapM declareInstantDef $ flowDefinitions f
     transitionDefs <- mapM declareTransition $ flowTransitions f
     return $ defDefs ++ transitionDefs

declareAutomaton :: Automaton i -> DeclM i [Definition]
declareAutomaton = $notImplemented

assertInits :: StateInit i -> DeclM i ()
assertInits = $notImplemented

assertPrecond :: Expr i -> DeclM i ()
assertPrecond = $notImplemented

declareInvariant :: Expr i -> DeclM i Definition
declareInvariant = $notImplemented

type TransM i = ReaderT (StreamPos, Env i) (Either String)

-- beware: uses error
runTransM :: TransM i a -> StreamPos -> Env i -> a
runTransM m n e = case runReaderT m (n, e) of
  Left err -> error err
  Right r -> r

lookupVar' :: Ident i => i -> TransM i (TypedStream i)
lookupVar' x =
  do vs <- asks $ vars . varEnv . snd
     case Map.lookup x vs of
       Nothing -> throwError $ "Unknown variable " ++ identPretty x
       Just x' -> return x'

askStreamPos :: TransM i StreamPos
askStreamPos = asks fst

trInstant :: Ident i => Instant i -> TransM i (TypedExpr i)
trInstant (untyped -> InstantExpr e) = trExpr e
trInstant (untyped -> NodeUsage n es) = $notImplemented

-- we do no further type checks since this
-- has been done beforhand.
trExpr :: Ident i => Expr i -> TransM i (TypedExpr i)
trExpr expr =
  let t = getType expr
  in case untyped expr of
    AtExpr (AtomConst c) -> $notImplemented
    AtExpr (AtomVar x) ->
      do s <- lookupVar' x
         n <- askStreamPos
         return $ s `appStream` n
    AtExpr (AtomEnum x) -> $notImplemented
    LogNot e -> lift1Bool not' <$> trExpr e
    Expr2 op e1 e2 -> $notImplemented
    Ite c e1 e2 -> liftIte <$> trExpr c <*> trExpr e1 <*> trExpr e2
    ProdCons (Prod es) -> $notImplemented
    Match e pats -> $notImplemented
    _ -> $notImplemented

{-
trBoolExpr :: Ident i => StreamPos -> Expr i -> TransM i (SMTExpr Bool)
trBoolExpr n expr =
  case untyped expr of
    AtExpr (AtomConst c) -> $notImplemented
    AtExpr (AtomVar x) ->
      do x' <- lookupVar' x
         let f =
               forceFunType x'
               (unit :: ArgAnnotation StreamPos) (unit :: SMTAnnotation Bool)
         return $ f `app` n
    AtExpr _ -> error "not a bool expr"
    LogNot e -> $notImplemented
    Expr2 op e1 e2 -> $notImplemented
    Ite c e1 e2 ->
      do c' <- trBoolExpr n c
         e1' <- trBoolExpr n e1
         e2' <- trBoolExpr n e2
         return $ ite c' e1' e2'
    ProdCons (Prod es) -> $notImplemented
    Match e pats -> $notImplemented
    _ -> $notImplemented

forceType :: SMTValue t2 => SMTExpr t1 -> (t1 -> t2) -> SMTAnnotation t2 -> SMTExpr t2
forceType (SMT.Var x _) _ ann2 = SMT.Var x ann2
forceType (SMT.Const v _) f ann2 = SMT.Const (f v) ann2
forceType _ _ _ = error "cannot force type"

forceFunType :: (Args a2, SMTType r2) =>
                SMTExpr (SMTFun a1 r1) ->
                ArgAnnotation a2 -> SMTAnnotation r2 -> SMTExpr (SMTFun a2 r2)
forceFunType (Fun x _ _) argAnn2 resAnn2 = Fun x argAnn2 resAnn2
forceFunType _ _ _ = error "cannot force function type"

-}