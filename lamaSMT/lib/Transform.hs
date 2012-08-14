{-# LANGUAGE TupleSections #-}
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
import Language.SMTLib2.Internals (SMTType(..), SMTExpr(Var, Fun))
import Data.Unit
import Data.String (IsString(..))
import Data.Array as Arr

import Data.Natural
import NatInstance
import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Foldable (foldrM)

import Control.Monad.State (StateT(..), MonadState(..), modify, gets)
import Control.Monad.Error (ErrorT(..), MonadError(..))
import Control.Monad.Reader (ReaderT(..), asks)
import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow (second, (&&&))

import SMTEnum
import LamaSMTTypes
import Definition
import TransformEnv
import RewriteAutomaton

lamaSMT :: Ident i => Program i -> ErrorT String SMT (ProgDefs, VarEnv i)
lamaSMT = fmap (second varEnv) . flip runStateT emptyEnv . declProgram

declProgram :: Ident i => Program i -> DeclM i ProgDefs
declProgram p =
  do preamble
     putConstants (progConstantDefinitions p)
     declareEnums (progEnumDefinitions p)
     declDefs <- declareDecls (progDecls p)
     flowDefs <- declareFlow (progFlow p)
     assertInits (progInitial p)
     precondDef <- declarePrecond (progAssertion p)
     invarDef <- declareInvariant (progInvariant p)
     return $ ProgDefs (declDefs ++ flowDefs) precondDef invarDef

preamble :: DeclM i ()
preamble =
  liftSMT $
  declareType (undefined :: Natural) unit

declareEnums :: Ident i => Map (TypeAlias i) (EnumDef i) -> DeclM i ()
declareEnums es =
  do anns <- (fmap Map.fromList . mapM declareEnum $ Map.toList es)
     let consAnns =
           foldl
           (\consAnns (x, EnumDef conss) -> insEnumConstrs (anns Map.! x) consAnns conss)
           Map.empty $ Map.toList es
     putEnumAnn anns
     putEnumConsAnn consAnns
  where
    insEnumConstrs ann = foldl (\consAnns cons -> Map.insert cons ann consAnns)

declareEnum :: Ident i => (TypeAlias i, EnumDef i) -> DeclM i (i, SMTAnnotation SMTEnum)
declareEnum (t, EnumDef cs) =
  let t' = fromString $ identString t
      cs' = map (fromString . identString) cs
      ann = (t', cs')
  in liftSMT (declareType (undefined :: SMTEnum) ann) >> return (t, ann)

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
declareVars = fmap Map.fromList . declareVarList

declareVarList :: Ident i => [Variable i] -> DeclM i [(i, TypedStream i)]
declareVarList = mapM declareVar

declareVar :: Ident i => Variable i -> DeclM i (i, TypedStream i)
declareVar (Variable x t) = (x,) <$> typedVar t
  where
    typedVar :: Ident i => Type i -> DeclM i (TypedStream i)
    typedVar (GroundType BoolT) = liftSMT $ fmap BoolStream fun
    typedVar (GroundType IntT) = liftSMT $ fmap IntStream fun
    typedVar (GroundType RealT) = liftSMT $ fmap RealStream fun
    typedVar (GroundType _) = $notImplemented
    typedVar (EnumType t) = lookupEnumAnn t >>= liftSMT . fmap EnumStream . funAnnRet
    typedVar (ProdType ts) =
      do vs <- mapM typedVar ts
         return . ProdStream $ listArray (0, (length vs) - 1) vs

declareNode :: Ident i => Node i -> DeclM i (NodeEnv i, [Definition])
declareNode n =
  do inDecls <- declareVarList $ nodeInputs n
     outDecls <- declareVarList $ nodeOutputs n
     let ins = map snd inDecls
     let outs = map snd outDecls
     modifyVars $ Map.union ((Map.fromList inDecls) `Map.union` (Map.fromList outDecls))
     declDefs <- declareDecls $ nodeDecls n
     flowDefs <- declareFlow $ nodeFlow n
     outDefs <- fmap concat . mapM declareInstantDef $ nodeOutputDefs n
     automDefs <- fmap concat . mapM declareAutomaton . Map.toList $ nodeAutomata n
     assertInits $ nodeInitial n
     precondDef <- declarePrecond $ nodeAssertion n
     varDefs <- gets varEnv
     return (NodeEnv ins outs varDefs,
             declDefs ++ flowDefs ++ outDefs ++ automDefs ++ [precondDef])

declareInstantDef :: Ident i => InstantDefinition i -> DeclM i [Definition]
declareInstantDef (InstantExpr x e) = (:[]) <$> (lookupVar x >>= \x' -> declareDef id x' (trExpr e))
declareInstantDef (NodeUsage x n es) =
  do nEnv <- lookupNode n
     let esTr = map trExpr es
     inpDefs <- mapM (uncurry $ declareDef id) $ zip (nodeEnvIn nEnv) esTr
     outpDef <- declareAssign x (nodeEnvOut nEnv)
     return $ inpDefs ++ [outpDef]

declareTransition :: Ident i => StateTransition i -> DeclM i Definition
declareTransition (StateTransition x e) = lookupVar x >>= \x' -> declareDef succ' x' (trExpr e)

declareDef :: Ident i => (StreamPos -> StreamPos) -> TypedStream i -> TransM i (TypedExpr i) -> DeclM i Definition
declareDef f x em =
  do env <- get
     let defType = streamDefType x
     d <- defStream defType $ \t ->
       let e = runTransM em t env
       in liftRel (.==.) (x `appStream` (f t)) e
     return $ ensureDefinition d
  where
    streamDefType (ProdStream ts) = ProdType . fmap streamDefType $ Arr.elems ts
    streamDefType _ = boolT

declareAssign :: Ident i => i -> [TypedStream i] -> DeclM i Definition
declareAssign _ [] = throwError $ "Cannot assign empty stream"
declareAssign x [y] = lookupVar x >>= \x' -> declareDef id x' (doAppStream y)
declareAssign x ys =
  let y = case ys of
        [y'] -> y
        _ -> mkProdStream ys
  in lookupVar x >>= \x' -> declareDef id x' (doAppStream y)

declareFlow :: Ident i => Flow i -> DeclM i [Definition]
declareFlow f =
  do defDefs <- fmap concat . mapM declareInstantDef $ flowDefinitions f
     transitionDefs <- mapM declareTransition $ flowTransitions f
     return $ defDefs ++ transitionDefs

declareAutomaton :: Ident i => (Int, Automaton i) -> DeclM i [Definition]
declareAutomaton (x, a) =
  let n = "Autom" ++ show x -- FIXME: generate better name!
      (e, sVars, f, i) = mkAutomatonEquations n a
  in do declareEnums e
        declDefs <- declareDecls sVars
        flowDefs <- declareFlow f
        assertInits i
        return $ declDefs ++ flowDefs

assertInits :: Ident i => StateInit i -> DeclM i ()
assertInits = mapM_ assertInit . Map.toList

assertInit :: Ident i => (i, ConstExpr i) -> DeclM i ()
assertInit (x, e) =
  do x' <- lookupVar x
     e' <- trConstExpr e
     let def = liftRel (.==.) (x' `appStream` zero') e'
     liftSMT $ liftAssert def

declarePrecond :: Ident i => Expr i -> DeclM i Definition
declarePrecond e =
  do env <- get
     d <- defStream boolT $ \t -> runTransM (trExpr e) t env
     return $ ensureDefinition d

declareInvariant :: Ident i => Expr i -> DeclM i Definition
declareInvariant = declarePrecond

trConstExpr :: Ident i => ConstExpr i -> DeclM i (TypedExpr i)
trConstExpr (untyped -> Const c) = return $ trConstant c
trConstExpr (untyped -> ConstEnum x) = lookupEnumConsAnn x >>= return . trEnumConsAnn x
trConstExpr (untyped -> ConstProd (Prod cs)) =
  ProdExpr . listArray (0, length cs - 1) <$> mapM trConstExpr cs

type TransM i = ReaderT (StreamPos, Env i) (Either String)

doAppStream :: TypedStream i -> TransM i (TypedExpr i)
doAppStream s = askStreamPos >>= return . appStream s

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

lookupEnumConsAnn' :: Ident i => (EnumConstr i) -> TransM i (SMTAnnotation SMTEnum)
lookupEnumConsAnn' t = asks (enumConsAnn . snd) >>= lookupErr ("Unknown enum constructor " ++ identPretty t) t

askStreamPos :: TransM i StreamPos
askStreamPos = asks fst

-- we do no further type checks since this
-- has been done beforehand.
trExpr :: Ident i => Expr i -> TransM i (TypedExpr i)
trExpr expr =
  let t = getType expr
  in case untyped expr of
    AtExpr (AtomConst c) -> return $ trConstant c
    AtExpr (AtomVar x) ->
      do s <- lookupVar' x
         n <- askStreamPos
         return $ s `appStream` n
    AtExpr (AtomEnum x) -> trEnumCons x
    LogNot e -> lift1Bool not' <$> trExpr e
    Expr2 op e1 e2 -> applyOp op <$> trExpr e1 <*> trExpr e2
    Ite c e1 e2 -> liftIte <$> trExpr c <*> trExpr e1 <*> trExpr e2
    ProdCons (Prod es) -> (ProdExpr . listArray (0, (length es) - 1)) <$> mapM trExpr es
    Project x i ->
      do (ProdStream s) <- lookupVar' x
         n <- askStreamPos
         return $ (s ! fromEnum i) `appStream` n
    Match e pats -> trExpr e >>= flip trPattern pats

trPattern :: Ident i => TypedExpr i -> [Pattern i] -> TransM i (TypedExpr i)
trPattern e@(EnumExpr _) = trEnumMatch e
trPattern _ = $notImplemented

trEnumMatch :: Ident i => TypedExpr i -> [Pattern i] -> TransM i (TypedExpr i)
trEnumMatch x pats =
  -- respect order of patterns here by putting the last in the default match
  -- and bulding the expression bottom-up:
  -- (match x {P_1.e_1, ..., P_n.e_n})
  -- ~> (ite P_1 e_1 (ite ... (ite P_n-1 e_n-1 e_n) ...))
  do innermostPat <- fmap snd . trEnumPattern x $ last pats
     foldrM (chainPatterns x) innermostPat (init pats)
  where
    chainPatterns c p ifs = trEnumPattern c p >>= \(cond, e) -> return $ liftIte cond e ifs
    trEnumPattern c (Pattern h e) = (,) <$> trEnumHead c h <*> trExpr e
    trEnumHead c (EnumPattern e) = trEnumCons e >>= \y -> return $ liftRel (.==.) c y
    trEnumHead _ BottomPattern = return . BoolExpr $ constant True

trEnumConsAnn :: Ident i => EnumConstr i -> SMTAnnotation SMTEnum -> TypedExpr i
trEnumConsAnn x = EnumExpr . constantAnn (SMTEnum . fromString $ identString x)

trEnumCons :: Ident i => EnumConstr i -> TransM i (TypedExpr i)
trEnumCons x = lookupEnumConsAnn' x >>= return . trEnumConsAnn x

applyOp :: BinOp -> TypedExpr i -> TypedExpr i -> TypedExpr i
applyOp Or e1 e2 = liftBoolL or' [e1, e2]
applyOp And e1 e2 = liftBoolL and' [e1, e2]
applyOp Xor e1 e2 = liftBool2 xor e1 e2
applyOp Implies e1 e2 = liftBool2 (.=>.) e1 e2
applyOp Equals e1 e2 = prodAll $ liftRel (.==.) e1 e2
applyOp Less e1 e2 = liftOrd (.<.) e1 e2
applyOp LEq e1 e2 = liftOrd (.<=.) e1 e2
applyOp Greater e1 e2 = liftOrd (.>.) e1 e2
applyOp GEq e1 e2 = liftOrd (.>=.) e1 e2
applyOp Plus e1 e2 = liftArithL plus [e1, e2]
applyOp Minus e1 e2 = liftArith minus e1 e2
applyOp Mul e1 e2 = liftArithL mult [e1, e2]
applyOp RealDiv e1 e2 = liftReal2 divide e1 e2
applyOp IntDiv e1 e2 = liftInt2 div' e1 e2
applyOp Mod e1 e2 = liftInt2 mod' e1 e2