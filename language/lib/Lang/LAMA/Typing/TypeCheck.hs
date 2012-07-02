{-# LANGUAGE TupleSections, ScopedTypeVariables #-}

module Lang.LAMA.Typing.TypeCheck (typecheck, typecheckConstExpr) where

import Data.Map as Map hiding (map, foldl)
import Data.Natural

import Control.Monad (when, void, liftM)
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Reader (MonadReader(ask), Reader, runReader)
import Control.Monad.State.Lazy (MonadState(..), gets, StateT(..), evalStateT)
import Control.Monad.Trans.Class
import Control.Applicative hiding (Const)
import Control.Arrow (first, second, Kleisli(..))

import Prelude hiding (mapM, foldl, sequence)
import Data.Traversable (Traversable(..), mapM)
import Data.Foldable (Foldable, foldl, foldlM)
import Data.List (intercalate)
import Data.String (IsString(..))
import Data.Tuple (swap)

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

-- | mapAccumL lifted to monads.
mapAccumLM :: (Monad m, Traversable t) => (a -> b -> m (a, c)) -> a -> t b -> m (a, t c)
mapAccumLM f r = liftM swap . (flip runStateT r) . (k f)
  where
    -- Tricky implementation to make it work with Traversable:
    -- First apply f to the elements in the structure. This results in functions that
    --  map the accumulator (ts).
    -- Then apply these functions via the state monad from left to right to r (ys).
    --  This results into a sequence of state actions.
    -- These state actions are then evaluated by using sequence.
    k :: forall a b c m t. (Monad m, Traversable t) => (a -> b -> m (a, c)) -> t b -> StateT a m (t c)
    k g xs =
      let ts = fmap (flip g) xs :: t (a -> m (a, c))
          ys = fmap (\t -> get >>= lift . t >>= \(a, y) -> put a >> return y) ts :: t (StateT a m c)
      in sequence ys

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
  | InterProd [InterType0 i]
  | ArrowT (InterType0 i) (InterType0 i)

instance Ident i => Show (InterType0 i) where
  show (Ground t) = render $ prettyType t
  show (Named x) = showTypeId x
  show (InterProd ts) = intercalate "*" $ map show ts
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
  show (Forall x u t) = "∀" ++ showTypeId x ++ ":" ++ show u ++ ". " ++ show t

mkGround :: Type i -> InterType i
mkGround = Simple . Ground

{-
-- be careful with types that are bound after the mapping by
-- a quantifier!
mapSimple :: (InterType0 i -> InterType0 i) -> InterType i -> InterType i
mapSimple f (Simple t) = Simple $ f t
mapSimple f (Forall x u t) = Forall x u $ mapSimple f t
-}

gBool, gInt, gReal :: InterType i
gBool = mkGround boolT
gInt = mkGround intT
gReal = mkGround realT

-- | Type unification

type Substitution0 i = InterType0 i -> InterType0 i
--type Substitution i = InterType i -> InterType i

{-
-- not really a lifting ...
liftSubst :: Substitution0 i -> Substitution i
liftSubst s (Simple t) = Simple $ s t
liftSubst _ _ = undefined
-}

replaceBy :: TypeId -> InterType0 i -> Substitution0 i
replaceBy x t = \t' -> case t' of
  Ground a -> Ground a
  Named x' -> if x == x' then t else (Named x')
  InterProd ts -> InterProd $ map (replaceBy x t) ts
  ArrowT t0 t1 -> ArrowT (replaceBy x t t0) (replaceBy x t t1)

getUniverse :: InterType0 i -> Universe
getUniverse (Ground (GroundType BoolT)) = TypeU
getUniverse (Ground (GroundType IntT)) = NumU
getUniverse (Ground (GroundType RealT)) = NumU
getUniverse (Ground (GroundType (SInt _))) = NumU
getUniverse (Ground (GroundType (UInt _))) = NumU
getUniverse _ = TypeU

unify0 :: Ident i => InterType0 i -> InterType0 i -> Result i (InterType0 i, Substitution0 i)
unify0 t (Named x) = return (t, replaceBy x t)
unify0 (Named x) t = return (t, replaceBy x t)
unify0 t@(Ground t1) t'@(Ground t2) =
  if t1 == t2 then return (t, id)
  else throwError $ "Incompatible types: " ++ show t ++ " and " ++ show t'
unify0 (ArrowT t1 t2) (ArrowT t1' t2') = do
  (t1'', s1) <- unify0 t1 t1'
  (t2'', s2) <- unify0 (s1 t2) (s1 t2')
  return (ArrowT t1'' t2'', s2 . s1)
-- Walk in parallel trough components and unify them using
-- the accumulated substitution.
unify0 (InterProd ts1) pt = do
  ts2 <- case pt of
        InterProd ts -> return ts
        Ground (ProdType ts) -> return $ map Ground ts
        _ -> throwError $ "Cannot unify " ++ show (InterProd ts1) ++ " and " ++ show pt

  (s, ts) <- mapAccumLM (\s (t1, t2) -> substAndUnify s t1 t2 >>= \(t, s') -> return (s' . s, t)) id $ zip ts1 ts2
  return (InterProd ts, s)
  where
    substAndUnify s t1 t2 = unify0 (s t1) (s t2)
unify0 t1 t2 = throwError $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

unify :: Ident i => InterType i -> InterType i -> Result i (InterType i, Substitution0 i)
unify (Simple t1) (Simple t2) = first Simple <$> unify0 t1 t2
unify (Forall x u t0) t1 = do
  (t', s) <- unify t0 t1
  let u' = getUniverse $ s (Named x)
  if u' <= u then return (t', s) else throwError $ "Incompatible universes: " ++ show u' ++ " not contained in " ++ show u
unify t1@(Simple _) t2@(Forall _ _ _) = unify t2 t1
-- unify t1 t2 = throwError $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

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
ensureGround (Simple (InterProd ts)) = do
  ts' <- mapM ensureGround (map Simple ts) `catchError` (\err -> throwError $ err ++ " in " ++ show (InterProd ts))
  return $ ProdType ts'
ensureGround t = throwError $ "Unresolved type: " ++ show t

typeExists :: Ident i => Type i -> Result i ()
typeExists (EnumType n) = do
  isEnumCons <- envIsEnum n
  if isEnumCons then return ()
  else throwError $ "Enum type " ++ identPretty n ++ " not defined"
typeExists _ = return ()

typecheck :: Ident i => UT.Program i -> Either String (Program i)
typecheck p =
  let check = checkProgram p `catchError` (\err -> getPos >>= \pos -> throwError $ err ++ " near " ++ identPretty pos)
  in runReader (evalStateT (runErrorT check) (0, Pos $ fromString "unknown")) emptyEnv

typecheckConstExpr :: Ident i => UT.ConstExpr i -> Either String (ConstExpr i)
typecheckConstExpr e =
  let check = checkConstExpr e `catchError` (\err -> getPos >>= \pos -> throwError $ err ++ " near " ++ identPretty pos)
  in runReader (evalStateT (runErrorT check) (0, Pos $ fromString "unknown")) emptyEnv

-- | Monad for the transformation process
--    Carries possible errors, an environment,
--    a generator for type variables and the
--    last known position.
type TypeIdEnvMonad i = StateT (Int, Pos i) (Reader (Env i))
type Result i = ErrorT String (TypeIdEnvMonad i)

newtype Pos i = Pos { runPos :: i }

genTypeId :: Result i TypeId
genTypeId = do
  (current, p) <- get
  put (current + 1, p)
  return current

putPos :: i -> Result i ()
putPos p = do
  (tv, _) <- get
  put (tv, Pos p)

getPos :: Result i i
getPos = gets (runPos . snd)

checkProgram :: Ident i => UT.Program i -> Result i (Program i)
checkProgram (Program typedefs constantdefs declarations flow initial assertion invariant) =
  checkTypeDefs typedefs >>= \types -> envAddEnums types $
  checkConstantDefs constantdefs >>= \consts -> envAddConsts consts $
  checkDeclarations declarations >>= \decls -> envAddDecls decls $
    Program types consts decls <$>
      (checkFlow flow) <*>
      (checkInitial initial) <*>
      (checkAssertion assertion) <*>
      (checkInvariant invariant)

checkTypeDefs :: Ident i => Map (TypeAlias i) (UT.EnumDef i) -> Result i (Map (TypeAlias i) (EnumDef i))
checkTypeDefs = return . fmap (\(UT.EnumDef ctors) -> EnumDef ctors)

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
checkInstantDef (InstantDef x i) = do
    putPos x
    i' <- checkInstant i
    t <- envLookupWritable x
    void $ unify (getGround i') (mkGround t)
    return $ InstantDef x i'

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
checkConstExpr (Fix (ConstEnum x)) = mkTyped (ConstEnum x) <$> envLookupEnum x
checkConstExpr (Fix (ConstProd (Prod vs))) = do
  vs' <- mapM checkConstExpr vs
  let ts = map getType vs'
  return $ mkTyped (ConstProd (Prod vs')) (mkProductT ts)
checkConstExpr (Fix (ConstArray (Array vs))) = do
  let l = length vs
  when (l == 0) (throwError "Empty arrays are not allowed")
  vs' <- mapM checkConstExpr vs
  let ts = map getGround0 vs'
  (t', _) <- foldlM (\(t1, s) t2 -> unify0 t1 (s t2)) (head ts, id) (tail ts)
  t <- ensureGround $ Simple t'
  case t of
    GroundType t1 -> return $ mkTyped (ConstArray $ Array vs') (ArrayType t1 $ fromInteger $ toInteger l)
    _ -> throwError $ (render $ prettyType t) ++ " is not a base type which is required for arrays"

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

    checkExpr' (ProdCons (Prod es)) = do
      es' <- mapM checkExpr es
      let ts = map getType es'
      return $ mkTyped (ProdCons (Prod es')) (mkProductT ts)

    checkExpr' (Match e pats) = do
      e' <- checkExpr e
      (pats', ts) <- fmap unzip $ mapM (checkPattern $ getType e') pats
      t <- foldlM (\t1 t2 -> ensureGround . fst =<< unify (mkGround t1) (mkGround t2)) (head ts) (tail ts)
      return $ mkTyped (Match e' pats') t

    checkExpr' (ArrayCons (Array es)) = do
      let l = length es
      when (l == 0) (throwError "Empty arrays are not allowed")
      es' <- mapM checkExpr es
      let ts = map getGround0 es'
      (t', _) <- foldlM (\(t1, s) t2 -> unify0 t1 (s t2)) (head ts, id) (tail ts)
      t <- ensureGround $ Simple t'
      case t of
        GroundType t1 -> return $ mkTyped (ArrayCons $ Array es') (ArrayType t1 $ fromInteger $ toInteger l)
        _ -> throwError $ (render $ prettyType t) ++ " is not a base type which is required for arrays"

    checkExpr' (Project x i) = do
      a <- envLookupReadable x
      case a of
        (ArrayType t n) -> do
          when (i >= n)
            (throwError $ "Projection of " ++ identPretty x ++ " out of range")
          return $ mkTyped (Project x i) (GroundType t)
        _ -> throwError $ identPretty x ++ " is not an array type"

    checkExpr' (Update x i e) = do
      a <- envLookupReadable x
      e' <- checkExpr e
      case a of
        (ArrayType t n) -> do
          when (i >= n)
            (throwError $ "Update of " ++ identPretty x ++ " out of range")
          void $ unify (mkGround $ GroundType t) (getGround e')
          return $ mkTyped (Update x i e') (ArrayType t n)
        _ -> throwError $ identPretty x ++ " is not an array type"

checkPattern :: Ident i => Type i -> UT.Pattern i -> Result i (Pattern i, Type i)
checkPattern inType (Pattern h e) = do
  (h', vs) <- checkPatHead inType h
  e' <- envAddVariables Input vs $ checkExpr e
  return (Pattern h' e', getType e')

checkPatHead :: Ident i => Type i -> UT.PatHead i -> Result i (PatHead i, [Variable i])
checkPatHead inType (EnumPat x) = do
  t <- envLookupEnum x
  void $ unify (mkGround inType) (mkGround t)
  return $ (EnumPat x, [])
checkPatHead inType (ProdPat xs) = do
  tids <- mapM (const genTypeId) xs
  let t = foldl (\t' a -> Forall a TypeU t') (Simple $ InterProd $ map Named tids) tids
  (ProdType ts) <- ensureGround . fst =<< unify (mkGround inType) t
  let vs = map (uncurry Variable) $ zip xs ts
  return $ (ProdPat xs, vs)

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
checkAtom (AtomVar x) = do
  putPos x
  env <- ask
  case getEnum env (EnumCons x) of
    Nothing -> envLookupReadable x >>= return . mkTyped (AtomVar x)
    Just t -> return $ mkTyped (AtomEnum $ EnumCons x) t
checkAtom (AtomEnum x) = putPos (runEnumCons x) >> mkTyped (AtomEnum x) <$> envLookupEnum x

{-
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
-}

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
