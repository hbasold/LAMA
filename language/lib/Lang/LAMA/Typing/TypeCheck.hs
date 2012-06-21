{-# LANGUAGE TupleSections, TemplateHaskell, ScopedTypeVariables #-}

module Lang.LAMA.Typing.TypeCheck (typecheck, typecheckConstExpr) where

import Data.Map as Map hiding (map)
import Data.Natural

import Development.Placeholders

import Control.Monad (when, void)
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State.Lazy (MonadState(..), StateT, evalStateT)
import Control.Applicative hiding (Const)
import Control.Arrow (first, second, Kleisli(..))

import Prelude hiding (mapM)
import Data.Traversable (mapM)

import Text.PrettyPrint

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import qualified Lang.LAMA.UnTypedStructure as UT
import Lang.LAMA.UnTypedStructure (Fix(Fix))
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Typing.Environment
import Lang.LAMA.PrettyTyped

firstM :: Monad m => (a -> m b) -> (a, c) -> m (b, c)
firstM f = runKleisli $ first (Kleisli f)

secondM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
secondM f = runKleisli $ second (Kleisli f)

-- | Intermediate type for type inference
type TypeId = Int
showTypeId :: TypeId -> String
showTypeId x = "a" ++ show x

data Universe = NumU | TypeU deriving Eq

instance Ord Universe where
  compare _ TypeU = LT
  compare TypeU NumU = GT
  compare NumU NumU = EQ

instance Show Universe where
  show NumU = "Num"
  show TypeU = "Type"

data InterType0 i =
  Ground (Type i)
  | Named TypeId
  | ArrowT (InterType0 i) (InterType0 i)

instance Ident i => Show (InterType0 i) where
  show (Ground t) = render $ prettyType t
  show (Named x) = showTypeId x
  show (ArrowT t1 t2) = "(" ++ show t1 ++ ") -> " ++ show t2

gBool0, gInt0, gReal0 :: InterType0 i
gBool0 = Ground boolT
gInt0 = Ground intT
gReal0 = Ground realT

data InterType i =
  Simple (InterType0 i)
  | Forall TypeId Universe (InterType i)

instance Ident i => Show (InterType i) where
  show (Simple t) = show t
  show (Forall x u t) = "∀ " ++ showTypeId x ++ ":" ++ show u ++ ". " ++ show t

mkGround :: Type i -> InterType i
mkGround = Simple . Ground

gBool, gInt, gReal :: InterType i
gBool = mkGround boolT
gInt = mkGround intT
gReal = mkGround realT

-- | Type unification

type Substitution i = InterType0 i -> InterType0 i

replaceBy :: TypeId -> InterType0 i -> Substitution i
replaceBy x t = \t' -> case t' of
  (Ground a) -> Ground a
  (Named x') -> if x == x' then t else (Named x')
  (ArrowT t0 t1) -> ArrowT (replaceBy x t t0) (replaceBy x t t1)

getUniverse :: InterType0 i -> Universe
getUniverse (Ground (GroundType BoolT)) = TypeU
getUniverse (Ground (GroundType IntT)) = NumU
getUniverse (Ground (GroundType RealT)) = NumU
getUniverse (Ground (GroundType (SInt _))) = NumU
getUniverse (Ground (GroundType (UInt _))) = NumU
getUniverse _ = TypeU

unify0 :: Ident i => InterType0 i -> InterType0 i -> Result i (InterType0 i, Substitution i)
unify0 t (Named x) = return (t, replaceBy x t)
unify0 (Named x) t = return (t, replaceBy x t)
unify0 t@(Ground t1) t'@(Ground t2) =
  if t1 == t2 then return (t, id)
  else throwError $ "Incompatible types: " ++ show t ++ " and " ++ show t'
unify0 (ArrowT t1 t2) (ArrowT t1' t2') = do
  (t1'', s1) <- unify0 t1 t1'
  (t2'', s2) <- unify0 (s1 t2) (s1 t2')
  return (ArrowT t1'' t2'', s2 . s1)
unify0 t1 t2 = throwError $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

unify :: Ident i => InterType i -> InterType i -> Result i (InterType i, Substitution i)
unify (Simple t1) (Simple t2) = first Simple <$> unify0 t1 t2
unify (Forall x u t0) t1 = do
  (t', s) <- unify t0 t1
  let u' = getUniverse $ s (Named x)
  if u' <= u then return (t', s) else throwError $ "Incompatible universes: " ++ show u' ++ " not contained in " ++ show u
unify t1 t2 = throwError $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

appArrow :: Ident i => Expr i -> InterType i -> Result i (InterType i)
appArrow e = appArrow' (getGround0 e)

appArrow' :: Ident i => InterType0 i -> InterType i -> Result i (InterType i)
appArrow' c (Simple (ArrowT a b))  = unify0 a c >>= \(_, s) -> return (Simple $ s b)
appArrow' c a = do
  t0 <- genTypeId
  (a', _) <- unify a (Simple $ ArrowT c (Named t0)) `catchError` (\e -> throwError $ "Could not apply " ++ show a ++ " to " ++ show c ++ ": " ++ e)
  appArrow' c a'
-- appArrow' a b = throwError $ "Could not apply type " ++ show b ++ " to " ++ show a

getGround0 :: Typed i e -> InterType0 i
getGround0 = Ground . getType

getGround :: Typed i e -> InterType i
getGround = Simple . Ground . getType

-- | Check if ground type (not a type variable) and
--    return that type.
ensureGround :: Ident i => InterType i -> Result i (Type i)
ensureGround (Simple (Ground t)) = return t
ensureGround t = throwError $ "Unresolved type: " ++ show t

typeExists :: Ident i => Type i -> Result i ()
typeExists (NamedType n) = void $ envLookupType n
typeExists _ = return ()

typecheck :: Ident i => UT.Program i -> Either String (Program i)
typecheck p = runReader (evalStateT (runErrorT $ checkProgram p) 0) emptyEnv

typecheckConstExpr :: Ident i => UT.ConstExpr i -> Either String (ConstExpr i)
typecheckConstExpr e = runReader (evalStateT (runErrorT $ checkConstExpr e) 0) emptyEnv

-- | Monad for the transformation process
--    Carries possible errors, an environment
--    and a generator for type variables
type TypeIdEnvMonad i = StateT Int (Reader (Env i))
type Result i = ErrorT String (TypeIdEnvMonad i)

genTypeId :: Result i TypeId
genTypeId = do
  current <- get
  put (current + 1)
  return current

checkProgram :: Ident i => UT.Program i -> Result i (Program i)
checkProgram (Program typedefs constantdefs declarations flow initial assertion invariant) = do
  checkTypeDefs typedefs >>= \types -> envAddTypes types $
    checkConstantDefs constantdefs >>= \consts -> envAddConsts consts $
      checkDeclarations declarations >>= \decls -> envAddDecls decls $ do
        Program types consts decls <$>
          (checkFlow flow) <*>
          (checkInitial initial) <*>
          (checkAssertion assertion) <*>
          (checkInvariant invariant)

checkTypeDefs :: Ident i => Map (TypeAlias i) (UT.TypeDef i) -> Result i (Map (TypeAlias i) (TypeDef i))
checkTypeDefs = fmap Map.fromList . checkTypeDefs' . Map.toList
  where
    checkTypeDefs' [] = return []
    checkTypeDefs' (td : tds) = do
      td'@(x, t) <- uncurry checkTypeDef $ td
      tds' <- envAddType x t $ checkTypeDefs' tds
      return $ td' : tds'

checkTypeDef :: Ident i => TypeAlias i -> UT.TypeDef i -> Result i (TypeAlias i, TypeDef i)
checkTypeDef x d@(EnumDef _) = return (x, d)
checkTypeDef x (RecordDef (RecordT fields)) =
  ((x,) . RecordDef . RecordT) <$> mapM (uncurry checkRecordField) fields

checkRecordField :: Ident i => RecordField i -> Type i -> Result i (RecordField i, Type i)
checkRecordField f t = typeExists t >> return (f, t)

checkConstantDefs :: Ident i => Map i UT.Constant -> Result i (Map i (Constant i))
checkConstantDefs = fmap Map.fromList . checkConstantDefs' . Map.toList
  where
    checkConstantDefs' = mapM (secondM checkConstant)

checkDeclarations :: Ident i => UT.Declarations i -> Result i (Declarations i)
checkDeclarations (UT.Declarations nodes states locals) =
  envEmptyDecls $
    Declarations <$>
      (fmap Map.fromAscList $ mapM (secondM checkNode) $ Map.toAscList nodes) <*>
      (mapM checkVarDecl states) <*>
      (mapM checkVarDecl locals)

checkNode :: Ident i => UT.Node i -> Result i (Node i)
checkNode (Node inp outp decls flow outpDef automata initial) = do
  inp' <- mapM checkVarDecl inp
  outp' <- mapM checkVarDecl outp
  decls' <- checkDeclarations decls
  envAddLocal (variableMap Input inp') $
    envAddLocal (variableMap Output outp') $
    envAddDecls decls' $
      Node inp' outp' decls' <$>
        (checkFlow flow) <*>
        (mapM checkInstantDef outpDef) <*>
        (mapM checkAutomaton automata) <*>
        (checkInitial initial)

checkVarDecl :: Ident i => Variable i -> Result i (Variable i)
checkVarDecl v@(Variable _ t) = typeExists t >> return v

checkFlow :: Ident i => UT.Flow i -> Result i (Flow i)
checkFlow (Flow definitions transitions) =
  Flow <$>
    mapM checkInstantDef definitions <*>
    mapM checkStateTransition transitions

checkInstantDef :: Ident i => UT.InstantDefinition i -> Result i (InstantDefinition i)
checkInstantDef (InstantDef xs i) = do
    i' <- checkInstant i
    ts <- mapM envLookupWritable xs
    void $ unify (getGround i') (mkGround $ mkProductT ts)
    return $ InstantDef xs i'

checkInstant :: Ident i => UT.Instant i -> Result i (Instant i)
checkInstant (Fix (InstantExpr e)) = preserveType InstantExpr <$> checkExpr e
checkInstant (Fix (NodeUsage n params)) = do
  params' <- mapM checkExpr params
  let inTypes = map getType params'
  (nInp, nOutp) <- envLookupNodeSignature n
  checkNodeTypes "input" n nInp inTypes
  return $ mkTyped (NodeUsage n params') (mkProductT $ map varType nOutp)

checkStateTransition :: Ident i => UT.StateTransition i -> Result i (StateTransition i)
checkStateTransition (StateTransition x e) = do
  t <- envLookupState x
  e' <- checkExpr e
  void $ unify (getGround e') (mkGround t)
  return $ StateTransition x e'

checkAutomaton :: Ident i => UT.Automaton i -> Result i (Automaton i)
checkAutomaton (Automaton locs initial edges) =
  Automaton <$>
    mapM checkLocation locs <*>
    pure initial <*>
    mapM checkEdge edges

checkLocation :: Ident i => UT.Location i -> Result i (Location i)
checkLocation (Location l flow) = Location l <$> checkFlow flow

checkEdge :: Ident i => UT.Edge i -> Result i (Edge i)
checkEdge (Edge t h c) = Edge t h <$> checkExpr c

checkInitial :: Ident i => UT.StateInit i -> Result i (StateInit i)
checkInitial = fmap Map.fromList . mapM checkInit . Map.toList
  where
    checkInit (x, c) = do
      t <- envLookupState x
      c' <- checkConstExpr c
      void $ unify (getGround c') (mkGround t)
      return (x, c')

checkAssertion :: Ident i => UT.Expr i -> Result i (Expr i)
checkAssertion = checkExpr

checkInvariant :: Ident i => UT.Expr i -> Result i (Expr i)
checkInvariant = checkExpr

checkConstExpr :: forall i. Ident i => UT.ConstExpr i -> Result i (ConstExpr i)
checkConstExpr (Fix (Const c)) = preserveType Const <$> checkConstant c
checkConstExpr (Fix (ConstRecord ctr)) = do
   ctr' <- checkRecordConstrConst ctr :: Result i (GRecordConstr i (ConstExpr i), Type i)
   return $ (uncurry mkTyped) $ (first ConstRecord) ctr'
checkConstExpr (Fix (ConstTuple t)) = $notImplemented

checkExpr :: Ident i => UT.Expr i -> Result i (Expr i)
checkExpr = checkExpr' . UT.unfix
  where
    checkExpr' :: Ident i => (GExpr i UT.Constant (UT.Atom i) (UT.Expr i)) -> Result i (Expr i)
    checkExpr' (AtExpr a) = (mapTyped AtExpr) <$> (checkAtom a)
    checkExpr' (LogNot e) = do
      e' <- checkExpr e
      void $ unify (getGround e') gBool
      return $ preserveType LogNot e'

    checkExpr' (Expr2 o e1 e2) = do
      to <- opType o
      e1' <- checkExpr e1
      e2' <- checkExpr e2
      t <- ensureGround =<< appArrow e2' =<< appArrow e1' to
      return $ mkTyped (Expr2 o e1' e2') t

    checkExpr' (Ite c e1 e2) =
      let iteType a = return $ Simple $ ArrowT gBool0 (ArrowT (Named a) (ArrowT (Named a) (Named a)))
      in do
        c' <- checkExpr c
        e1' <- checkExpr e1
        e2' <- checkExpr e2

        a <- iteType =<< genTypeId
        t <- ensureGround =<< appArrow e2' =<< appArrow e1' =<< appArrow c' a
        return $ mkTyped (Ite c' e1' e2') t

    checkExpr' (Constr ctr) = do
      (ctr', t) <- checkRecordConstr ctr
      return $ mkTyped (Constr ctr') t

    checkExpr' (Select _ _) = $notImplemented

    checkExpr' (Project x i) = do
      a <- envLookupReadable x
      case a of
        (ArrayType t n) -> do
          when (i >= n)
            (throwError $ "Projection of " ++ identPretty x ++ " out of range")
          return $ mkTyped (Project x i) (GroundType t)
        _ -> throwError $ identPretty x ++ " is not an array type"

-- | Checks the signature of a used node
checkNodeTypes :: Ident i => String -> i -> [Variable i] -> [Type i] -> Result i ()
checkNodeTypes kind node namedSig expected =
  case checkTypeList 1 namedSig expected of
    Nothing -> return ()
    Just e -> throwError $ "Could not match " ++ kind ++ " signature of " ++ identPretty node ++
      case e of
      (err, True) -> ": number of types did not match (" ++ err ++ ")"
      (err, False) -> ": type mismatch " ++ err
  where
    checkTypeList :: Ident i => Int -> [Variable i] -> [Type i] -> Maybe (String, Bool)
    checkTypeList _ [] [] = Nothing
    checkTypeList p [] r = Just ("had " ++ (show $ p + (length r)) ++ " but expected " ++ show p, True)
    checkTypeList p r [] = Just ("had" ++ show p ++ " but expected " ++ (show $ p + (length r)), True)
    checkTypeList p (v:vs) (t:ts) =
      if (varType v) == t then checkTypeList (p+1) vs ts
      else Just (show p ++ " (expected " ++ show v ++ " but got " ++ show t ++ ")", False)

checkAtom :: Ident i => GAtom i UT.Constant (UT.Atom i) -> Result i (Atom i)
checkAtom (AtomConst c) = preserveType AtomConst <$> checkConstant c
checkAtom (AtomVar x) = mkTyped (AtomVar x) <$> envLookupReadable x

checkRecordConstr :: Ident i => UT.GRecordConstr i (UT.Expr i) -> Result i (GRecordConstr i (Expr i), Type i)
checkRecordConstr (RecordConstr x es) = do
  (RecordT fields) <- envLookupRecordType x
  es' <- mapM checkExpr es
  when ((map snd fields) /= (map getType es'))
    (throwError $ "Arguments of record constructor do not match while constructing " ++ identPretty x)
  return $ (RecordConstr x es', NamedType x)

checkRecordConstrConst :: Ident i => UT.GRecordConstr i (UT.ConstExpr i) -> Result i (GRecordConstr i (ConstExpr i), Type i)
checkRecordConstrConst (RecordConstr x es) = do
  (RecordT fields) <- envLookupRecordType x
  es' <- mapM checkConstExpr es
  when ((map snd fields) /= (map getType es'))
    (throwError $ "Arguments of record constructor do not match while constructing " ++ identPretty x)
  return $ (RecordConstr x es', NamedType x)

checkConstant :: UT.Constant -> Result i (Constant i)
checkConstant (Fix (BoolConst a)) = return $ mkTyped (BoolConst a) boolT
checkConstant (Fix (IntConst a)) = return $ mkTyped (IntConst a) intT
checkConstant (Fix (RealConst a)) = return $ mkTyped (RealConst a) realT
checkConstant (Fix (SIntConst bits a)) =
  let neededBits = (usedBits $ abs a) + 1 -- extra sign bit
  in if neededBits > bits
      then throwError $ show a ++ " (signed) does not fit into " ++ show bits ++ " bits, requires at least " ++ show neededBits
      else return $ mkTyped (SIntConst bits a) (GroundType $ SInt bits)
checkConstant (Fix (UIntConst bits a)) =
  let neededBits = (usedBits $ toInteger a)
  in if neededBits > bits
      then throwError $ show a ++ " (unsigned) does not fit into " ++ show bits ++ " bits, requires at least " ++ show neededBits
      else return $ mkTyped (UIntConst bits a) (GroundType $ UInt bits)

usedBits :: Integer -> Natural
usedBits = (+ 1) . log2
  where
    log2 :: (Integral a, Num b) => a -> b
    log2 x
      | x < 0 = error "Argument to log2 must be non-negative"
      | otherwise = log2' x
      where
        log2' 0 = 0
        log2' 1 = 0
        log2' y = 1 + (log2 $ div y 2)

opType :: BinOp -> Result i (InterType i)
opType o = case o of
  Or  -> return $ Simple $ ArrowT gBool0 (ArrowT gBool0 gBool0)
  And  -> return $ Simple $ ArrowT gBool0 (ArrowT gBool0 gBool0)
  Xor  -> return $ Simple $ ArrowT gBool0 (ArrowT gBool0 gBool0)
  Implies  -> return $ Simple $ ArrowT gBool0 (ArrowT gBool0 gBool0)
  Equals  -> genTypeId >>= \a -> return $ Forall a TypeU $ Simple (ArrowT (Named a) (ArrowT (Named a) gBool0))
  Less  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) gBool0))
  Greater  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) gBool0))
  LEq  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) gBool0))
  GEq  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) gBool0))
  Plus  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) (Named a)))
  Minus  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) (Named a)))
  Mul  -> genTypeId >>= \a -> return $ Forall a NumU $ Simple (ArrowT (Named a) (ArrowT (Named a) (Named a)))
  RealDiv  -> return $ Simple $ ArrowT gReal0 (ArrowT gReal0 gReal0)
  IntDiv  -> return $ Simple $ ArrowT gInt0 (ArrowT gInt0 gInt0)
  Mod  -> return $ Simple $ ArrowT gInt0 (ArrowT gInt0 gInt0)
