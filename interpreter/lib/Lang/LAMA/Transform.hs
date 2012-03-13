module Lang.LAMA.Transform (absToConc) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Natural
import Data.Ratio
import qualified Data.ByteString.Char8 as BS
import Prelude hiding (foldl, concat, any)
import Data.Foldable
import Control.Applicative hiding (Const)
import Control.Arrow (second)
import Control.Monad.Trans.Error
import Control.Monad.Reader

import qualified Lang.LAMA.Parser.Abs as Abs
import qualified Lang.LAMA.Parser.Print as Abs (printTree)
import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Structure

log2 :: (Integral a, Num b) => a -> b
log2 x
  | x < 0 = error "Argument to log2 must be non-negative"
  | otherwise = log2' x
  where
    log2' 0 = 0
    log2' 1 = 0
    log2' y = 1 + (log2 $ div y 2)

data VarUsage = Input | Output | Local | State

readable :: VarUsage -> Bool
readable Input = True
readable Output = False
readable Local = True
readable State = True

writable :: VarUsage -> Bool
writable Input = False
writable Output = True
writable State = True
writable Local = True

-- | Environment which holds declared types, constants and variables
data Environment = Env {
    envTypes :: Map TypeId TypeDef,
    envConsts :: Map Identifier Constant,
    envVars :: Map Identifier (Type, VarUsage),
    envNodes :: Map Identifier Node
  }

-- | Generate empty environment
emptyEnv :: Environment
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

-- | Monad for the transformation process
--    Carries possible errors and an environment
type Result = ErrorT String (Reader Environment)

-- | Lookup a record type
envLookupRecordType :: TypeId -> Result RecordT
envLookupRecordType ident = do
  env <- ask
  case Map.lookup ident $ envTypes env of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just (RecordDef t) -> return t
    _ -> fail $ show ident ++ " is not a record type"

-- | Lookup a type
envLookupType :: TypeId -> Result TypeDef
envLookupType ident = do
  env <- ask
  case Map.lookup ident $ envTypes env of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just t -> return t

-- | Lookup a variable that needs to be read
envLookupReadable :: Identifier -> Result Type
envLookupReadable ident = do
  env <- ask
  case Map.lookup ident $ envVars env of
    Nothing -> case Map.lookup ident $ envConsts env of
      Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
      Just c -> return $ getType c
    Just (t, u) -> if readable u then return t
                    else fail $ "Variable " ++ prettyIdentifier ident ++ " not readable"

-- | Lookup a variable that needs to be written
envLookupWritable :: Identifier -> Result Type
envLookupWritable ident = do
  env <- ask
  case Map.lookup ident $ envVars env of
    Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
    Just (t, u) -> if writable u then return t
                    else fail $ "Variable " ++ prettyIdentifier ident ++ " not writable"

-- | Lookup a state variable
envLookupState :: Identifier -> Result Type
envLookupState ident = do
  env <- ask
  case Map.lookup ident $ envVars env of
    Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
    Just (t, State) -> return t
    _ -> fail $ "Variable " ++ prettyIdentifier ident ++ " is not a state variable"

-- | Lookup a state variable
envLookupNodeSignature :: Identifier -> Result ([Variable], [Variable])
envLookupNodeSignature ident = do
  env <- ask
  case Map.lookup ident $ envNodes env of
    Nothing -> fail $ "Undefined nodes " ++ prettyIdentifier ident
    Just n -> return (nodeInputs n, nodeOutputs n)

variableMap :: VarUsage -> [Variable] -> Map Identifier (Type, VarUsage)
variableMap u = Map.fromList . map splitVar
  where splitVar (Variable ident t) = (ident, (t, u))

-- | Set the types in the environment
envSetTypes :: Map TypeId TypeDef -> Result a -> Result a
envSetTypes ts = local $ (\env -> env { envTypes = ts })

-- | Adds a type to in the environment
envAddType :: TypeId -> TypeDef -> Result a -> Result a
envAddType ident t = local $ (\env -> env { envTypes = Map.insert ident t $ envTypes env })

-- | Set the constants in the environment
envSetConsts :: Map Identifier Constant -> Result a -> Result a
envSetConsts cs = local $ (\env -> env { envConsts = cs })

-- | Add scoped variables to the environment
envAddLocal :: Map Identifier (Type, VarUsage) -> Result a -> Result a
envAddLocal vars = local $ (\env -> env { envVars = Map.union (envVars env) vars })

-- | Set the nodes in the environment
envSetNodes :: Map Identifier Node -> Result a -> Result a
envSetNodes ns = local $ (\env -> env { envNodes = ns })

absToConc :: Abs.File -> Either String File
absToConc f = runReader (runErrorT $ transFile f) emptyEnv

-- | Signals an undefined translation case. To be abandoned when finished.
failure :: Show a => a -> Result b
failure x = fail $ "Undefined case: " ++ show x

-- | Create identifier from position information and name
makeId :: ((Int, Int), BS.ByteString) -> Identifier
makeId (pos, str) = Id str pos

-- | Create identifier from position information and name without the last
--    character, this should be a "'" which is part of a state identifier
--    on the lhs in a state assignment.
makeStateId :: ((Int, Int), BS.ByteString) -> Identifier
makeStateId (pos, str) = Id (BS.init str) pos


--- Type inference

-- | Intermediate type for type inference
data InterType = Ground Type | VarType | VarArray | ArrowT InterType InterType deriving Show
gBool, gInt, gReal :: InterType
gBool = Ground boolT
gInt = Ground intT
gReal = Ground realT

-- | Very simple unification:
--    If rhs is a type variable, then the type
--    of the expression is chosen, otherwise
--    the types must be equal.
unify :: InterType -> InterType -> Result InterType
unify t@(Ground t1) (Ground t2) =
  if t1 == t2 then return t
  else fail $ "Incompatible types: " ++ show t1 ++ " and " ++ show t2

unify VarType t = return t
unify t VarType = return t

unify VarArray VarArray = return VarArray
unify t@(Ground (ArrayType _ _)) VarArray = return t
unify VarArray t@(Ground (ArrayType _ _)) = return t

unify t1 t2 = fail $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

-- | Checks the signature of a used node
checkSignature :: Identifier -> ([Variable], [Variable]) -> [Type] -> [Type] -> Result ()
checkSignature node (nInp, nOutp) inp outp =
  case checkTypeList 1 nInp inp of
    Nothing -> case checkTypeList 1 nOutp outp of
      Nothing -> return ()
      Just (err, True) -> fail $ "Could not match output signature of " ++ prettyIdentifier node ++ ": number of return values did not match (" ++ err ++ ")"
      Just (err, False) -> fail $ "Could not match output signature of " ++ prettyIdentifier node ++ ": type mismatch on return value " ++ err
    Just (err, True) -> fail $ "Could not match input signature of " ++ prettyIdentifier node ++ ": number of parameters did not match (" ++ err ++ ")"
    Just (err, False) -> fail $ "Could not match input signature of " ++ prettyIdentifier node ++ ": type mismatch on parameter " ++ err

  where
    checkTypeList _ [] [] = Nothing
    checkTypeList p [] r = Just ("had " ++ (show $ p + (length r)) ++ " but expected " ++ show p, True)
    checkTypeList p r [] = Just ("had" ++ show p ++ " but expected " ++ (show $ p + (length r)), True)
    checkTypeList p (v:vs) (t:ts) =
      if (getVarType v) == t then checkTypeList (p+1) vs ts
      else Just (show p ++ " (expected " ++ show v ++ " but got " ++ show t ++ ")", False)

    getVarType (Variable _ t) = t

appToArrow :: InterType -> InterType -> Result InterType
appToArrow t (ArrowT t1 t2) = do
  t' <- unify t1 t
  case t2 of
    VarType -> return t'
    (ArrowT VarType t3) -> return $ ArrowT t' t3
    _ -> return t2
appToArrow _ t = fail $ show t ++ " is not a function type"

-- | Check if ground type (not a type variable) and
--    return that type.
ensureGround :: InterType -> Result Type
ensureGround (Ground t) = return t
ensureGround VarType = fail "Not resolved type variable"
ensureGround _ = fail "Unresolved function type"

getGround :: Typed e -> InterType
getGround = Ground . getType

typeExists :: Type -> Result ()
typeExists (NamedType n) = void $ envLookupType n
typeExists _ = return ()


--- Translation functions

transIdentifier :: Abs.Identifier -> Result Identifier
transIdentifier x = case x of
  Abs.Identifier str  -> return $ makeId str


transStateId :: Abs.StateId -> Result Identifier
transStateId x = case x of
  Abs.StateId str  -> return $ makeStateId str


transFile :: Abs.File -> Result File
transFile x = case x of
  Abs.File typedefs constantdefs node assertion initial invariant -> do
    types <- transTypeDefs typedefs
    consts <- transConstantDefs constantdefs

    envSetTypes types $ envSetConsts consts $
      File types consts <$>
        (transNode node) <*>
        (transAssertion assertion) <*>
        (transInitial initial) <*>
        (transInvariant invariant)


transTypeDefs :: Abs.TypeDefs -> Result (Map TypeId TypeDef)
transTypeDefs x = case x of
  Abs.NoTypeDefs  -> return Map.empty
  Abs.JustTypeDefs typedefs  -> fmap Map.fromList $ transTypeDefs' typedefs

  where
    transTypeDefs' [] = return []
    transTypeDefs' (td:tds) = do
      td'@(ident, t) <- transTypeDef td
      tds' <- envAddType ident t $
                transTypeDefs' tds
      return $ td' : tds'

transTypeDef :: Abs.TypeDef -> Result (TypeId, TypeDef)
transTypeDef x = case x of
  Abs.EnumDef enumt  -> fmap (second EnumDef) $ transEnumT enumt
  Abs.RecordDef recordt  -> fmap (second RecordDef) $ transRecordT recordt


transEnumConstr :: Abs.EnumConstr -> Result EnumConstr
transEnumConstr x = case x of
  Abs.EnumConstr identifier  -> transIdentifier identifier


transEnumT :: Abs.EnumT -> Result (TypeId, EnumT)
transEnumT x = case x of
  Abs.EnumT identifier enumconstrs  ->
    (,) <$> (transIdentifier identifier) <*> (fmap EnumT $ mapM transEnumConstr enumconstrs)


transRecordField :: Abs.RecordField -> Result (RecordField, Type)
transRecordField x = case x of
  Abs.RecordField identifier t -> do
    ident <- transIdentifier identifier
    t' <- transType t
    typeExists t'
    return (ident, t')


transRecordT :: Abs.RecordT -> Result (TypeId, RecordT)
transRecordT x = case x of
  Abs.RecordT identifier recordfields  -> do
    ident <- transIdentifier identifier
    fields <- mapM transRecordField recordfields
    return (ident, RecordT fields)


transType :: Abs.Type -> Result Type
transType x = case x of
  Abs.GroundType basetype  -> fmap GroundType $ transBaseType basetype
  Abs.TypeId identifier  -> fmap NamedType $ transIdentifier identifier
  Abs.ArrayType basetype natural  ->
    ArrayType <$> (transBaseType basetype) <*> (transNatural natural)


transBaseType :: Abs.BaseType -> Result BaseType
transBaseType x = case x of
  Abs.BoolT  -> return BoolT
  Abs.IntT  -> return IntT
  Abs.RealT  -> return RealT
  Abs.SInt natural  -> fmap SInt $ transNatural natural
  Abs.UInt natural  -> fmap UInt $ transNatural natural

transConstantDefs :: Abs.ConstantDefs -> Result (Map Identifier Constant)
transConstantDefs x = case x of
  Abs.NoConstantDefs -> return Map.empty
  Abs.JustConstantDefs constantdefs -> fmap Map.fromList $ mapM transConstantDef constantdefs


transConstantDef :: Abs.ConstantDef -> Result (Identifier, Constant)
transConstantDef x = case x of
  Abs.ConstantDef identifier constant -> do
    ident <- transIdentifier identifier
    c <- transConstant constant
    return (ident, c)

transNatural :: Abs.Natural -> Result Natural
transNatural x = case x of
  Abs.Nat n  -> return $ fromInteger n


transIntegerConst :: Abs.IntegerConst -> Result Integer
transIntegerConst x = case x of
  Abs.NonNegativeInt n  -> return n
  Abs.NegativeInt n  -> return $ -n


transConstant :: Abs.Constant -> Result Constant
transConstant x = case x of
  Abs.BoolConst boolv  -> do
    v <- transBoolV boolv
    return $ Typed (BoolConst v) boolT

  Abs.IntConst integerconst  -> do
    v <- transIntegerConst integerconst
    return $ Typed (IntConst v) intT

  Abs.RealConst integerconst0 integerconst  -> do
    v1 <- transIntegerConst integerconst0
    v2 <- transIntegerConst integerconst
    return $ Typed (RealConst $ v1 % v2) realT

  Abs.SIntConst natural integerconst  -> do
    bits <- transNatural natural
    v <- transIntegerConst integerconst
    let neededBits = (usedBits $ abs v) + 1 -- extra sign bit
    when (neededBits > bits)
      (fail $ show v ++ " (signed) does not fit into " ++ show bits ++ " bits, requires at least " ++ show neededBits)
    return $ Typed (SIntConst v) (GroundType $ SInt bits)

  Abs.UIntConst natural0 natural  -> do
    bits <- transNatural natural0
    v <- transNatural natural
    let neededBits = usedBits $ toInteger v
    when (neededBits > bits)
      (fail $ show v ++ " (unsigned) does not fit into " ++ show bits ++ " bits, requires at least " ++ show neededBits)
    return $ Typed (UIntConst v) (GroundType $ UInt bits)

  where
    usedBits :: Integer -> Natural
    usedBits = (+ 1) . log2


transBoolV :: Abs.BoolV -> Result Bool
transBoolV x = case x of
  Abs.TrueV  -> return True
  Abs.FalseV  -> return False


transAssertion :: Abs.Assertion -> Result [Expr]
transAssertion x = case x of
  Abs.NoAssertion  -> return []
  Abs.JustAssertion expr  -> (:[]) <$> (transExpr expr)


transInitial :: Abs.Initial -> Result (Map Identifier ConstExpr)
transInitial x = case x of
  Abs.NoInitial  -> return Map.empty
  Abs.JustInitial stateinits  -> fmap Map.fromList $ mapM transStateInit stateinits


transInvariant :: Abs.Invariant -> Result [Expr]
transInvariant x = case x of
  Abs.NoInvariant  -> return []
  Abs.JustInvariant expr  -> fmap (:[]) $ transExpr expr


transStateInit :: Abs.StateInit -> Result (Identifier, ConstExpr)
transStateInit x = case x of
  Abs.StateInit identifier constexpr  -> do
    ident <- transIdentifier identifier
    t <- envLookupState ident
    e <- transConstExpr constexpr
    void $ unify (getGround e) (Ground t)
    return (ident, e)


transConstExpr :: Abs.ConstExpr -> Result ConstExpr
transConstExpr x = case x of
  Abs.ConstExpr expr  -> transExpr expr >>= (evalConst . untyped)
  where
    evalConst :: UExpr Expr -> Result ConstExpr
    evalConst (AtExpr (Typed (AtomConst c) _)) = return $ preserveType Const c
    evalConst (Constr (RecordConstr tid es)) = do
      cExprs <- mapM (evalConst . untyped) es
      return $ Typed (ConstRecord $ RecordConstr tid cExprs) (NamedType tid)
    evalConst _ = fail $ "Not a constant expression: " ++ Abs.printTree x


transTypedVars :: Abs.TypedVars -> Result [Variable]
transTypedVars x = case x of
  Abs.TypedVars identifiers t  -> do
    t' <- transType t
    let varCons = flip Variable $ t'
    fmap (map varCons) $ mapM transIdentifier identifiers


transMaybeTypedVars :: Abs.MaybeTypedVars -> Result [Variable]
transMaybeTypedVars x = case x of
  Abs.NoTypedVars  -> return []
  Abs.JustTypedVars typedvarss  -> fmap concat $ mapM transTypedVars typedvarss


transNode :: Abs.Node -> Result Node
transNode x = case x of
  Abs.Node identifier maybetypedvars typedvarss nodedecls statedecls localdecls flow controlstructure initial -> do
    name <- transIdentifier identifier
    inp <- transMaybeTypedVars maybetypedvars
    outp <- fmap concat $ mapM transTypedVars typedvarss
    nodes <- transNodeDecls nodedecls
    states <- transStateDecls statedecls
    locals <- transLocalDecls localdecls
    let vars = (variableMap Input inp)
                `Map.union` (variableMap Output outp)
                `Map.union` (variableMap State states)
                `Map.union` (variableMap Local locals)
    let localNodes = Map.fromList $ map (\n -> (nodeName n, n)) nodes
    
    envAddLocal vars $ envSetNodes localNodes $
      Node name inp outp nodes states locals <$>
        (transFlow flow) <*>
        (transControlStructure controlstructure) <*>
        (transInitial initial)


transVarDecls :: Abs.VarDecls -> Result [Variable]
transVarDecls x = case x of
  Abs.SingleDecl typedvars  -> transTypedVars typedvars
  Abs.ConsDecl typedvars vardecls  -> do
    vs <- transTypedVars typedvars
    vss <- transVarDecls vardecls
    return $ vs ++ vss


transNodeDecls :: Abs.NodeDecls -> Result [Node]
transNodeDecls x = case x of
  Abs.NoNodes  -> return []
  Abs.JustNodeDecls nodes  -> mapM transNode nodes


transStateDecls :: Abs.StateDecls -> Result [Variable]
transStateDecls x = case x of
  Abs.NoStateDecls  -> return []
  Abs.JustStateDecls vardecls  -> transVarDecls vardecls


transLocalDecls :: Abs.LocalDecls -> Result [Variable]
transLocalDecls x = case x of
  Abs.NoLocals  -> return []
  Abs.JustLocalDecls vardecls  -> transVarDecls vardecls


transFlow :: Abs.Flow -> Result Flow
transFlow x = case x of
  Abs.Flow localdefinitions outputs transitions  ->
    Flow <$>
      (transLocalDefinitions localdefinitions) <*>
      (transOutputs outputs) <*>
      (transTransitions transitions)

transLocalDefinitions :: Abs.LocalDefinitions -> Result [InstantDefinition]
transLocalDefinitions x = case x of
  Abs.NoLocalDefinitons  -> return []
  Abs.JustLocalDefinitons instantdefinitions  -> mapM transInstantDefinition instantdefinitions


transOutputs :: Abs.Outputs -> Result [InstantDefinition]
transOutputs x = case x of
  Abs.NoOutputs  -> return []
  Abs.JustOutputs instantdefinitions  -> mapM transInstantDefinition instantdefinitions


transTransitions :: Abs.Transitions -> Result [StateTransition]
transTransitions x = case x of
  Abs.NoTransitions  -> return []
  Abs.JustTransitions transitions  -> mapM transTransition transitions


transInstantDefinition :: Abs.InstantDefinition -> Result InstantDefinition
transInstantDefinition x = case x of
  Abs.SimpleDef identifier expr  -> do
    ident <- transIdentifier identifier
    t <- envLookupWritable ident
    e <- transExpr expr
    void $ unify (getGround e) (Ground t)
    return $ SimpleDef ident e

  Abs.NodeUsageDef pattern nodeusage  -> do
    p <- transPattern pattern
    u@(NodeUsage node exprs) <- transNodeUsage nodeusage
    outTypes <- mapM envLookupWritable p
    let inTypes = map getType exprs
    nodeSignature <- envLookupNodeSignature node
    checkSignature node nodeSignature inTypes outTypes
    return $ NodeUsageDef p u


transTransition :: Abs.Transition -> Result StateTransition
transTransition x = case x of
  Abs.Transition stateid expr  -> do
    s <- transStateId stateid
    t <- envLookupState s
    e <- transExpr expr
    void $ unify (getGround e) (Ground t)
    return $ StateTransition s e


transPattern :: Abs.Pattern -> Result Pattern
transPattern x = case x of
  Abs.Pattern list2id  -> transList2Id list2id


transList2Id :: Abs.List2Id -> Result [Identifier]
transList2Id x = case x of
  Abs.Id2 identifier0 identifier  -> do
    ident1 <- transIdentifier identifier0
    ident2 <- transIdentifier identifier
    return [ident1, ident2]
  Abs.ConsId identifier list2id  -> (:) <$> (transIdentifier identifier) <*> (transList2Id list2id)


transNodeUsage :: Abs.NodeUsage -> Result NodeUsage
transNodeUsage x = case x of
  Abs.NodeUsage identifier exprs  ->
    NodeUsage <$> (transIdentifier identifier) <*> (mapM transExpr exprs)


transControlStructure :: Abs.ControlStructure -> Result [Automaton]
transControlStructure x = case x of
  Abs.ControlStructure automatons  -> mapM transAutomaton automatons


transAutomaton :: Abs.Automaton -> Result Automaton
transAutomaton x = case x of
  Abs.Automaton locations initiallocation edges  -> do
    locs <- mapM transLocation locations
    Automaton locs <$>
      (transInitialLocation locs initiallocation) <*>
      (mapM (transEdge locs) edges)


transLocation :: Abs.Location -> Result Location
transLocation x = case x of
  Abs.Location identifier flow  ->
    Location <$> (transIdentifier identifier) <*> (transFlow flow)

isKnownLocation :: [Location] -> LocationId -> Result ()
isKnownLocation locs loc =
  when (not $ any (\(Location l _) -> l == loc) locs)
    (fail $ "Unknown location " ++ prettyIdentifier loc)

transInitialLocation :: [Location] -> Abs.InitialLocation -> Result LocationId
transInitialLocation locs x = case x of
  Abs.InitialLocation identifier  -> do
    loc <- transIdentifier identifier
    isKnownLocation locs loc
    return loc


transEdge :: [Location] -> Abs.Edge -> Result Edge
transEdge locs x = case x of
  Abs.Edge identifier0 identifier expr  -> do
    t <- transIdentifier identifier0
    isKnownLocation locs t
    h <- transIdentifier identifier
    isKnownLocation locs h
    e <- transExpr expr
    return $ Edge t h e


transAtom :: Abs.Atom -> Result Atom
transAtom x = case x of
  Abs.AtomConst constant  -> fmap (preserveType AtomConst) $ transConstant constant
  Abs.AtomVar identifier  -> do
    ident <- transIdentifier identifier
    t <- envLookupReadable ident
    return $ Typed (AtomVar ident) t

transExpr :: Abs.Expr -> Result Expr
transExpr x = case x of
  Abs.AtExpr atom -> fmap (preserveType AtExpr) $ transAtom atom

  Abs.Expr1 Abs.Not expr -> do
    e <- transExpr expr
    t <- ensureGround =<< unify (getGround e) (Ground boolT)
    return $ Typed (LogNot e) t

  Abs.Expr2 binop expr0 expr -> do
    (op, to) <- transBinOp binop
    e1 <- transExpr expr0
    e2 <- transExpr expr
    t <- ensureGround =<< appToArrow (getGround e2) =<< appToArrow (getGround e1) to
    return $ Typed (Expr2 op e1 e2) t

  Abs.Expr3 Abs.Ite expr0 expr1 expr  -> do
    c <- transExpr expr0
    _ <- unify (getGround c) (Ground boolT)
    e1 <- transExpr expr1
    e2 <- transExpr expr
    t <- ensureGround =<< unify (getGround e2) (getGround e1)
    return $ Typed (Ite c e1 e2) t

  Abs.Constr identifier exprs  -> do
    tid <- transIdentifier identifier
    (RecordT fields) <- envLookupRecordType tid
    es <- mapM transExpr exprs
    when ((map snd fields) /= (map getType es))
      (fail $ "Arguments of record constructor do not match while constructing " ++ prettyIdentifier tid)
    return $ Typed (Constr $ RecordConstr tid es) (NamedType tid)

  Abs.Project identifier natural  -> do
    ident <- transIdentifier identifier
    n <- transNatural natural
    t <- envLookupReadable ident
    (ArrayType base size) <- ensureGround =<< unify (Ground t) VarArray
    when (n >= size)
      (fail $ "Projection of " ++ prettyIdentifier ident ++ " out of range")
    return $ Typed (Project ident $ n) (GroundType base)

  Abs.Select identifier0 identifier  -> failure x


transBinOp :: Abs.BinOp -> Result (BinOp, InterType)
transBinOp = return . transBinOp'
  where
    transBinOp' :: Abs.BinOp -> (BinOp, InterType)
    transBinOp' x = case x of
      Abs.Or  -> (Or, ArrowT gBool (ArrowT gBool gBool))
      Abs.And  -> (And, ArrowT gBool (ArrowT gBool gBool))
      Abs.Xor  -> (Xor, ArrowT gBool (ArrowT gBool gBool))
      Abs.Implies  -> (Implies, ArrowT gBool (ArrowT gBool gBool))
      Abs.Equals  -> (Equals, ArrowT VarType (ArrowT VarType gBool))
      Abs.Less  -> (Less, ArrowT VarType (ArrowT VarType gBool))
      Abs.Greater  -> (Greater, ArrowT VarType (ArrowT VarType gBool))
      Abs.LEq  -> (LEq, ArrowT VarType (ArrowT VarType gBool))
      Abs.GEq  -> (GEq, ArrowT VarType (ArrowT VarType gBool))
      Abs.Plus  -> (Plus, ArrowT VarType (ArrowT VarType VarType))
      Abs.Minus  -> (Minus, ArrowT VarType (ArrowT VarType VarType))
      Abs.Mul  -> (Mul, ArrowT VarType (ArrowT VarType VarType))
      Abs.RealDiv  -> (RealDiv, ArrowT gReal (ArrowT gReal gReal))
      Abs.IntDiv  -> (IntDiv, ArrowT gInt (ArrowT gInt gInt))
      Abs.Mod  -> (Mod, ArrowT gInt (ArrowT gInt gInt))

