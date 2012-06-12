{-# LANGUAGE TemplateHaskell, TupleSections #-}

module Lang.LAMA.Interpret where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.ByteString.Char8 as BS

import Prelude hiding (lookup)

import Data.Graph.Inductive.Query.DFS (topsort')

import Control.Monad.Error (MonadError(..))
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

type EvalM = Either String

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

lookupNode :: NodeEnv -> Identifier -> EvalM (Node, NodeDeps)
lookupNode s n = lookupErr ("Unknown node" ++ identString n) s n

lookupErr :: (MonadError e m, Ord k) => e -> Map k v -> k -> m v
lookupErr err m k = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

addParams :: Node -> State -> [ConstExpr] -> State
addParams (Node {nodeInputs = inp}) (State env ns) es =
  let env' = foldl (\env'' (x, c) -> update env'' (identBS $ varIdent x) c) env (zip inp es)
  in State env' ns

evalProg :: State -> Program -> ProgDeps -> EvalM State
evalProg s p d =
  let e = stateEnv s
      e' = e `Map.union` (Map.mapKeys identBS $ progInitial p) -- only adds initial values if not already present
      vs = reverse $ topsort' $ progDepsFlow d
      nodes = declsNode $ progDecls p
  in uncurry State <$> foldlM (assign (zipMaps nodes $ progDepsNodes d)) (e', (stateNodes s)) vs

assign :: NodeEnv -> (Environment, NodeState) -> (IdentCtx, ExprCtx) -> EvalM (Environment, NodeState)
assign _ (env, nState) (v, NoExpr) = return (env, nState)
assign nodes (env, nState) (v, GlobalExpr expr) = do
  (r, nState') <- evalExpr nodes (State env nState) expr
  env' <- updateM env (ctxGetIdent v) r
  return (env', nState')
assign nodes (env, nState) (v, LocalExpr refs) = $notImplemented

evalExpr :: NodeEnv -> State -> Expr -> EvalM (ConstExpr, NodeState)
evalExpr nodes s@(State env ns) expr = case untyped expr of
  AtExpr a -> (,ns) <$> evalAtom env a
  LogNot e -> do
    (e', ns1) <- evalExpr nodes s e
    return (negate e', ns1)
  Expr2 o e1 e2 -> $notImplemented
  Ite c e1 e2 -> do
    (c', ns1) <- evalExpr nodes s c
    let s1 = State env ns1
    (e1', ns2) <- evalExpr nodes s1 e1
    let s2 = State env ns2
    (e2', ns3) <- evalExpr nodes s2 e2
    let r = if isTrue c' then e1' else e2'
    return (r, ns3)
  Constr ctr -> $notImplemented
  Select _ _ -> $notImplemented
  Project x i -> $notImplemented
  NodeUsage n params -> do
    let nBS = identBS n
    (params', ns') <- evalExprs nodes s params
    (nDecl, nDeps) <- lookupNode nodes n
    let nState = Map.findWithDefault emptyState nBS ns'
    (r, nState') <- evalNode nDecl nDeps nState params'
    return (r, Map.alter (const $ Just nState') nBS ns')
  
  where
    evalExprs :: NodeEnv -> State -> [Expr] -> EvalM ([ConstExpr], NodeState)
    evalExprs nodes s = foldrM (evalExprs' nodes (stateEnv s)) ([], stateNodes s)
    
    evalExprs' :: NodeEnv -> Environment -> Expr -> ([ConstExpr], NodeState) -> EvalM ([ConstExpr], NodeState)
    evalExprs' nodes env e (rs, nEnv) = do
      (r, nEnv') <- evalExpr nodes (State env nEnv) e
      return (r : rs, nEnv')
    
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
    (env'', ns) <- foldlM (assign (zipMaps nodes $ nodeDepsNodes nDeps)) (env', (stateNodes s)) vs
    r <- fmap mkTuple $ mapM (lookup env'' . identBS . varIdent) (nodeOutputs nDecl)
    return (r, State env'' ns)

mkTuple :: [ConstExpr] -> ConstExpr
mkTuple [] = error "cannot build empty tuple"
mkTuple [v] = v
mkTuple vs =
  let ts = map getType vs
      t = mkProductT ts
  in mkTyped (ConstTuple $ Tuple vs) t
