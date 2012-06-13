{-# LANGUAGE TemplateHaskell, TupleSections, FlexibleContexts, Rank2Types #-}

module Lang.LAMA.Interpret where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.ByteString.Char8 as BS

import Prelude hiding (lookup)

import Data.Graph.Inductive.Query.DFS (topsort')

import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Reader (MonadReader(..), Reader, runReader)
import Control.Monad (liftM)
import Data.Foldable (foldlM, find)
import Control.Applicative ((<$>), (<*>))

import Text.PrettyPrint as PP

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Dependencies
import Lang.LAMA.PrettyTyped

zipMaps :: Ord k => Map k a -> Map k b -> Map k (a, b)
zipMaps m1 = Map.foldlWithKey (\m k x -> maybe m (\y -> Map.insert k (y, x) m) $ Map.lookup k m1) Map.empty

-- | Location information are meaningless here,
--  so we drop them.
type Ident = BS.ByteString

type NodeEnv = Map Ident ConstExpr
type ActiveLocations = Map Int Ident
data State = State { stateEnv :: NodeEnv, stateActiveLocs :: ActiveLocations, stateNodes :: NodeStates } deriving Show
type NodeStates = Map Ident State

type NodeDecls = Map Identifier (Node, NodeDeps)
type AutomatonDecls = Map Int Automaton

data Environment = Environment { envNodeDecls :: NodeDecls, envAutomDecls :: AutomatonDecls, envState :: State }

prettyMap :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc
prettyMap pk pv = Map.foldlWithKey (\d x v -> d $+$ (pk x) <+> text "->" <+> (pv v)) empty

prettyNodeEnv :: NodeEnv -> Doc
prettyNodeEnv = prettyMap (ptext . BS.unpack) prettyConstExpr

prettyActiveLocs :: ActiveLocations -> Doc
prettyActiveLocs = prettyMap PP.int (ptext . BS.unpack)

prettyState :: State -> Doc
prettyState s = (prettyNodeEnv $ stateEnv s) $+$ (prettyActiveLocs $ stateActiveLocs s) $+$ (prettyStates $ stateNodes s)
  where prettyStates = Map.foldlWithKey (\d x s' -> d $+$ (ptext $ BS.unpack x) <> colon <> (braces $ prettyState s')) empty

emptyNodeEnv :: NodeEnv
emptyNodeEnv = Map.empty

emptyState :: State
emptyState = State emptyNodeEnv Map.empty Map.empty

emptyNodeDecls :: NodeDecls
emptyNodeDecls = Map.empty

emptyEnv :: Environment
emptyEnv = Environment Map.empty Map.empty emptyState

addToState :: State -> Map Ident ConstExpr -> State
addToState s vs = s { stateEnv = Map.union (stateEnv s) vs }

type EvalM = ErrorT String (Reader Environment)

askNodeDecls :: MonadReader Environment m => m NodeDecls
askNodeDecls = reader envNodeDecls

localNodeDecls :: MonadReader Environment m => (NodeDecls -> NodeDecls) -> m a -> m a
localNodeDecls f = local (\env -> env { envNodeDecls = f $ envNodeDecls env })

askAutomDecls :: MonadReader Environment m => m AutomatonDecls
askAutomDecls = reader envAutomDecls

localAutomDecls :: MonadReader Environment m => (AutomatonDecls -> AutomatonDecls) -> m a -> m a
localAutomDecls f = local (\env -> env { envAutomDecls = f $ envAutomDecls env })

askState :: MonadReader Environment m => m State
askState = reader envState

localState :: MonadReader Environment m => (State -> State) -> m a -> m a
localState f = local (\env -> env { envState = f $ envState env })

update :: Ident -> ConstExpr -> NodeEnv -> NodeEnv
update x v = Map.alter (const (Just v)) x

updateM :: MonadReader Environment m => Ident -> ConstExpr -> m NodeEnv
updateM x v = askState >>= return . (update x v) . stateEnv

lookup :: (MonadReader Environment m, MonadError String m) => Ident -> m ConstExpr
lookup x = do
  e <- liftM stateEnv askState
  case Map.lookup x e of
    Nothing -> throwError $ BS.unpack x ++ " undefined in environment: \n" ++ (render $ nest 1 $ prettyNodeEnv e)
    Just v -> return v

lookupNodeState :: (MonadReader Environment m, MonadError String m) => Ident -> m State
lookupNodeState n = askState >>= \s -> lookupErr ("No state for node " ++ BS.unpack n) (stateNodes s) n

lookupNode :: (MonadReader Environment m, MonadError String m) => Identifier -> m (Node, NodeDeps)
lookupNode n = askNodeDecls >>= \s -> lookupErr ("Unknown node" ++ identString n) s n

lookupAutomaton :: (MonadReader Environment m, MonadError String m) => Int -> m Automaton
lookupAutomaton a = askAutomDecls >>= \s -> lookupErr ("Unknown automaton " ++ show a) s a

lookupErr :: (MonadError e m, Ord k) => e -> Map k v -> k -> m v
lookupErr err m k = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

addParams :: Node -> [ConstExpr] -> NodeEnv -> NodeEnv
addParams (Node {nodeInputs = inp}) es env =
  foldl (\env'' (x, c) -> update (identBS $ varIdent x) c env'') env (zip inp es)

eval :: State -> Program -> ProgDeps -> Either String State
eval s p d = runReader (runErrorT $ evalProg p d) (emptyEnv{ envState = s})

evalProg :: Program -> ProgDeps -> EvalM State
evalProg p d =
  let defs = reverse $ topsort' $ progDepsFlow d
      nodes = declsNode $ progDecls p
  in do
    s <- askState
    let e = stateEnv s
    let e' = e `Map.union` (Map.mapKeys identBS $ progInitial p) -- only adds initial values if not already present
    let s' = s { stateEnv = e' }
    s'' <- localNodeDecls (const (zipMaps nodes $ progDepsNodes d)) $
            foldlM (\s'' -> localState (const s'') . assign) s' defs
    return s''

assign :: (IdentCtx, ExprCtx) -> EvalM State
assign (v, e) = case e of
  NoExpr -> askState
  GlobalExpr inst -> assignInstant v inst
  LocalExpr autom refs -> do
    l <- takeEdge autom -- get next state
    inst <- lookupErr ("Unknown location " ++ BS.unpack l ++ " in expressions " ++ show refs) refs l
    localState (\s -> s {stateActiveLocs = Map.alter (const $ Just l) autom (stateActiveLocs s)}) $
      assignInstant v inst
  where
    assignInstant v inst = do
      (r, nState') <- evalInstant inst
      env' <- updateM (ctxGetIdent v) r
      s <- askState
      return $ s { stateEnv = env', stateNodes = nState' }

-- | Takes an edge in the given automaton and returns the new location
takeEdge :: Int -> EvalM Ident
takeEdge a = do
    aDecl <- lookupAutomaton a
    al <- liftM stateActiveLocs askState
    let l = Map.findWithDefault (identBS $ automInitial aDecl) a al
    -- TODO: take transition if we just started from an initial state?
    let sucs = suc (automEdges aDecl) l
    sucs' <- mapM (\(t, c) -> evalExpr c >>= \c' -> return (t, c')) sucs
    let s = find (isTrue . snd) sucs'
    case s of
      Nothing -> throwError $ "Transition relation is not total at location " ++ BS.unpack l
      Just (t, _) -> return t
  where
    suc es l = foldr (\(Edge h t c) s -> if identBS h == l then (identBS t, c) : s else s) [] es

evalInstant :: Instant -> EvalM (ConstExpr, NodeStates)
evalInstant i = case untyped i of
  InstantExpr e -> (,) <$> evalExpr e <*> (liftM stateNodes askState)
  NodeUsage n params -> do
    let nBS = identBS n
    params' <- mapM evalExpr params
    (nDecl, nDeps) <- lookupNode n
    ns <- liftM stateNodes askState
    let nState = Map.findWithDefault emptyState nBS ns
    (r, nState') <- localState (const nState) $ evalNode nDecl nDeps params'
    return (r, Map.alter (const $ Just nState') nBS ns)

evalExpr :: Expr -> EvalM ConstExpr
evalExpr expr = case untyped expr of
  AtExpr a -> evalAtom a
  LogNot e -> negate <$> evalExpr e
  Expr2 o e1 e2 -> evalExpr e1 >>= \e1' -> evalExpr e2 >>= \e2' -> return $ evalBinOp o e1' e2'
  Ite c e1 e2 -> do
    c' <- evalExpr c
    e1' <- evalExpr e1
    e2' <- evalExpr e2
    return $ if isTrue c' then e1' else e2'
  Constr ctr -> $notImplemented
  Select _ _ -> $notImplemented
  Project x i -> $notImplemented
  
  where
    negate = mapBoolConst not

evalAtom :: GAtom Constant Atom -> EvalM ConstExpr
evalAtom (AtomConst c) = return $ preserveType Const c
evalAtom (AtomVar x) = lookup (identBS x)

mapConst :: (GConst Constant -> GConst Constant) -> ConstExpr -> ConstExpr
mapConst f = mapTyped f'
  where
    f' ce = case ce of
      Const c -> Const $ mapTyped f c
      x -> x

mapBoolConst :: (Bool -> Bool) -> ConstExpr -> ConstExpr
mapBoolConst f = mapConst f'
  where
    f' (BoolConst v) = BoolConst $ f v
    f' x = x

getBoolConst :: ConstExpr -> Bool
getBoolConst ce = case untyped ce of
  Const c -> case untyped c of
    BoolConst v -> v
    _ -> error "not a boolean const"
  _ -> error "not a boolean const"

isTrue :: ConstExpr -> Bool
isTrue = getBoolConst

liftBool :: (Bool -> Bool -> Bool) -> ConstExpr -> ConstExpr -> ConstExpr
liftBool f c1 = mapBoolConst (f $ getBoolConst c1)

getNumConst :: ConstExpr -> Either Integer Rational
getNumConst ce = case untyped ce of
  Const c -> case untyped c of
    IntConst v -> Left v
    RealConst v -> Right v
    SIntConst _ v -> Left v
    UIntConst _ v -> Left $ toInteger v
    _ -> error "not a numeric const"
  _ -> error "not a numeric const"

liftOrd :: (forall a. Ord a => a -> a -> Bool) -> ConstExpr -> ConstExpr -> ConstExpr
liftOrd g c1 = either (mapIntPredicate . g) (mapRealPredicate . g) $ getNumConst c1
  where
    mapIntPredicate f = mapConst f'
      where
        f' (IntConst v) = BoolConst $ f v
        f' (SIntConst _ v) = BoolConst $ f v
        f' (UIntConst _ v) = BoolConst $ f $ toInteger v
        f' _ = error "not an int valued const"

    mapRealPredicate f = mapConst f'
      where
        f' (RealConst v) = BoolConst $ f v
        f' _ = error "not a real valued const"

liftNum :: (forall a. Num a => a -> a -> a) -> ConstExpr -> ConstExpr -> ConstExpr
liftNum g c1 = either (mapIntLikeConst . g) (mapRealConst . g) $ getNumConst c1
  where
    mapIntLikeConst f = mapConst f'
      where
        f' (IntConst v) = IntConst $ f v
        f' (SIntConst s v) = SIntConst s $ f v -- TODO: range check
        f' (UIntConst s v) = UIntConst s $ fromInteger $ f (toInteger v) -- TODO: range check
        f' _ = error "not an int valued const"

    mapRealConst f = mapConst f'
      where
        f' (RealConst v) = RealConst $ f v
        f' _ = error "not a real valued const"

evalBinOp :: BinOp -> ConstExpr -> ConstExpr -> ConstExpr
evalBinOp o = case o of
  Or  -> liftBool (||)
  And  -> liftBool (&&)
  Xor  -> liftBool xor
  Implies  -> liftBool implies
  Equals  -> liftOrd (==)
  Less  -> liftOrd (<)
  Greater  -> liftOrd (>)
  LEq  -> liftOrd (<=)
  GEq  -> liftOrd (>=)
  Plus  -> liftNum (+)
  Minus  -> liftNum (-)
  Mul  -> liftNum (*)
  RealDiv  -> $notImplemented
  IntDiv  -> $notImplemented
  Mod  -> $notImplemented
  where
    xor a b = not (a == b)
    implies a b = not a || b

evalNode :: Node -> NodeDeps -> [ConstExpr] -> EvalM (ConstExpr, State)
evalNode nDecl nDeps params =
  let defs = reverse $ topsort' $ nodeDepsFlow nDeps
      nodes = declsNode $ nodeDecls nDecl
  in do
    s <- askState
    let e = stateEnv s
    let e' = e `Map.union` (Map.mapKeys identBS $ nodeInitial nDecl) -- only adds initial values if not already present
    let e'' = addParams nDecl params e'
    let s' = s { stateEnv = e'' }
    s'' <- localNodeDecls (const $ zipMaps nodes $ nodeDepsNodes nDeps) $
            localAutomDecls (const $ nodeAutomata nDecl) $
              foldlM (\s'' -> localState (const s'') . assign) s' defs
    r <- localState (const s'') $ fmap mkTuple $ mapM (lookup . identBS . varIdent) (nodeOutputs nDecl)
    return (r, s'')

mkTuple :: [ConstExpr] -> ConstExpr
mkTuple [] = error "cannot build empty tuple"
mkTuple [v] = v
mkTuple vs =
  let ts = map getType vs
      t = mkProductT ts
  in mkTyped (ConstTuple $ Tuple vs) t
