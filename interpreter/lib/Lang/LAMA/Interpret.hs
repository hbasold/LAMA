{-# LANGUAGE TemplateHaskell, TupleSections, FlexibleContexts #-}

module Lang.LAMA.Interpret where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.ByteString.Char8 as BS

import Prelude hiding (lookup)

import Data.Graph.Inductive.Query.DFS (topsort')

import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Reader (MonadReader(..), Reader, runReader)
import Data.Foldable (foldlM, foldrM)
import Control.Applicative ((<$>))

import Text.PrettyPrint

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
type NodeState = Map Ident State
data State = State { stateEnv :: Environment, stateNodes :: NodeState } deriving Show
type Environment = Map Ident ConstExpr

type NodeEnv = Map Identifier (Node, NodeDeps)

emptyEnv :: Environment
emptyEnv = Map.empty

prettyEnv :: Environment -> Doc
prettyEnv = Map.foldlWithKey (\d x v -> d $+$ (ptext $ BS.unpack x) <+> text "->" <+> prettyConstExpr v) empty

prettyState :: State -> Doc
prettyState (State env ns) = prettyEnv env $+$ (prettyStates ns)
  where prettyStates = Map.foldlWithKey (\d x s -> d $+$ (ptext $ BS.unpack x) <> colon <> (braces $ prettyState s)) empty

emptyState :: State
emptyState = State emptyEnv Map.empty

addToState :: State -> Map Ident ConstExpr -> State
addToState (State env ns) vs = State (Map.union env vs) ns

type EvalM = ErrorT String (Reader NodeEnv)

update :: Environment -> Ident -> ConstExpr -> Environment
update e x v = Map.alter (const (Just v)) x e

updateM :: Monad m => Environment -> Ident -> ConstExpr -> m Environment
updateM e x = return . update e x

lookup :: Environment -> Ident -> EvalM ConstExpr
lookup e x = case Map.lookup x e of
  Nothing -> throwError $ BS.unpack x ++ " undefined in environment: \n" ++ (render $ nest 1 $ prettyEnv e)
  Just v -> return v

lookupNodeState :: State -> Ident -> EvalM State
lookupNodeState s n = lookupErr ("No state for node " ++ BS.unpack n) (stateNodes s) n

lookupNode :: (MonadReader NodeEnv m, MonadError String m) => Identifier -> m (Node, NodeDeps)
lookupNode n = ask >>= \s -> lookupErr ("Unknown node" ++ identString n) s n

lookupErr :: (MonadError e m, Ord k) => e -> Map k v -> k -> m v
lookupErr err m k = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

addParams :: Node -> State -> [ConstExpr] -> State
addParams (Node {nodeInputs = inp}) (State env ns) es =
  let env' = foldl (\env'' (x, c) -> update env'' (identBS $ varIdent x) c) env (zip inp es)
  in State env' ns

eval :: State -> Program -> ProgDeps -> Either String State
eval s p d = runReader (runErrorT $ evalProg s p d) Map.empty

evalProg :: State -> Program -> ProgDeps -> EvalM State
evalProg s p d =
  let e = stateEnv s
      e' = e `Map.union` (Map.mapKeys identBS $ progInitial p) -- only adds initial values if not already present
      vs = reverse $ topsort' $ progDepsFlow d
      nodes = declsNode $ progDecls p
  in uncurry State <$> (local (const (zipMaps nodes $ progDepsNodes d)) $ foldlM assign (e', (stateNodes s)) vs)

assign :: (Environment, NodeState) -> (IdentCtx, ExprCtx) -> EvalM (Environment, NodeState)
assign (env, nState) (v, NoExpr) = return (env, nState)
assign (env, nState) (v, GlobalExpr inst) = do
  (r, nState') <- evalInstant (State env nState) inst
  env' <- updateM env (ctxGetIdent v) r
  return (env', nState')
assign (env, nState) (v, LocalExpr refs) = $notImplemented

evalInstant :: State -> Instant -> EvalM (ConstExpr, NodeState)
evalInstant s@(State env ns) i = case untyped i of
  InstantExpr e -> (,ns) <$> evalExpr s e
  NodeUsage n params -> do
    let nBS = identBS n
    params' <- evalExprs s params
    (nDecl, nDeps) <- lookupNode n
    let nState = Map.findWithDefault emptyState nBS ns
    (r, nState') <- evalNode nDecl nDeps nState params'
    return (r, Map.alter (const $ Just nState') nBS ns)

  where
    evalExprs :: State -> [Expr] -> EvalM [ConstExpr]
    evalExprs s = foldrM (evalExprs' s) []

    evalExprs' :: State -> Expr -> [ConstExpr] -> EvalM [ConstExpr]
    evalExprs' s e rs = (:rs) <$> evalExpr s e

evalExpr :: State -> Expr -> EvalM ConstExpr
evalExpr s@(State env ns) expr = case untyped expr of
  AtExpr a -> evalAtom env a
  LogNot e -> do
    e' <- evalExpr s e
    return $ negate e'
  Expr2 o e1 e2 -> $notImplemented
  Ite c e1 e2 -> do
    c' <- evalExpr s c
    e1' <- evalExpr s e1
    e2' <- evalExpr s e2
    return $ if isTrue c' then e1' else e2'
  Constr ctr -> $notImplemented
  Select _ _ -> $notImplemented
  Project x i -> $notImplemented
  
  where
    negate ce = case untyped ce of
      Const c -> case untyped c of
        BoolConst v -> mkTyped (Const $ mkTyped (BoolConst $ not v) boolT) boolT
        _ -> ce
      _ -> ce
    
    isTrue ce = case untyped ce of
      Const c -> case untyped c of
        BoolConst True -> True
        _ -> False
      _ -> False

evalAtom :: Environment -> GAtom Constant Atom -> EvalM ConstExpr
evalAtom _ (AtomConst c) = return $ preserveType Const c
evalAtom env (AtomVar x) = lookup env (identBS x)

evalNode :: Node -> NodeDeps -> State -> [ConstExpr] -> EvalM (ConstExpr, State)
evalNode nDecl nDeps s params =
  let s' = addParams nDecl s params
      env = stateEnv s'
      env' = env `Map.union` (Map.mapKeys identBS $ nodeInitial nDecl) -- only adds initial values if not already present
      vs = reverse $ topsort' $ nodeDepsFlow nDeps
      nodes = declsNode $ nodeDecls nDecl
  in do
    (env'', ns) <- local (const $ zipMaps nodes $ nodeDepsNodes nDeps) $ foldlM assign (env', (stateNodes s)) vs
    r <- fmap mkTuple $ mapM (lookup env'' . identBS . varIdent) (nodeOutputs nDecl)
    return (r, State env'' ns)

mkTuple :: [ConstExpr] -> ConstExpr
mkTuple [] = error "cannot build empty tuple"
mkTuple [v] = v
mkTuple vs =
  let ts = map getType vs
      t = mkProductT ts
  in mkTyped (ConstTuple $ Tuple vs) t
