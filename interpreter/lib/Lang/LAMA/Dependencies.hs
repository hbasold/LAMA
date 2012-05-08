{-# LANGUAGE TupleSections #-}

module Lang.LAMA.Dependencies where -- (
--   Assignment, NodeDeps, Dependencies, mkDependencies
-- ) where

import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.NodeMap as G hiding (insMapNode, insMapNodeM, insMapNodes, insMapNodesM)
import Data.Graph.Inductive.NodeMapSupport as G
import Data.Graph.Inductive.DAG
import qualified Data.Graph.Inductive.Graph as G
import Data.Map as Map hiding (map)
import Control.Monad.Trans.Error
import Control.Monad.Trans.Class
import Data.Foldable (foldlM)
import Control.Monad.State.Lazy
import Data.List (intercalate)
import Control.Monad.Trans.Reader

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Structure



data VarUsage = Constant | Input | Output | Local | StateIn | StateOut deriving (Show, Eq, Ord)
type VarMap = Map Identifier VarUsage
varMap :: Node -> VarMap
varMap n =
  (Map.fromList $ map ((, Input) . varIdent) $ nodeInputs n) `Map.union`
  (Map.fromList $ map ((, Output) . varIdent) $ nodeOutputs n) `Map.union`
  (declsVarMap $ nodeDecls n)

declsVarMap :: Declarations -> VarMap
declsVarMap d =
  (Map.fromList $ map ((, Local) . varIdent) $ declsLocal d) `Map.union`
  (Map.fromList $ map ((, StateIn) . varIdent) $ declsState d)

data Mode = GlobalMode | LocationMode Identifier deriving (Eq, Ord, Show)
type Var = (Identifier, VarUsage, Mode)
data InterNodeDeps = InterNodeDeps {
    depsGraph :: DAG Gr Var (),
    depsVars :: G.NodeMap Var,
    depsExprs :: Map Var Expr
  }

type NodeDeps = Map String InterNodeDeps

data ProgDeps = ProgDeps {
    nodeDeps :: Map String InterNodeDeps,
    progFlowDeps :: InterNodeDeps
  }

mkDeps :: Program -> Either String ProgDeps
mkDeps = mkDepsProgram

type DepMonad = Either String

checkCycles :: Gr Var () -> Either String (DAG Gr Var ())
checkCycles g = case mkDAG g of
  Left c -> Left $ "Cyclic dependency: " ++ depList g c
  Right dag -> Right dag
  where
    depList :: Gr Var () -> [G.Node] -> String
    depList h = intercalate " -> " . map (maybe "" id . fmap (\(v, u, m) -> show u ++ " in " ++ show m ++ " " ++ prettyIdentifier v) . G.lab h)

mkDepsProgram :: Program -> DepMonad ProgDeps
mkDepsProgram p = do
  nodeDeps <- (return . Map.unions) =<< mapM (mkDepsNode "" (progConstantDefinitions p)) (declsNode $ progDecls p)
  let vars = declsVarMap $ progDecls p
  let (mes, (vs, progFlowDeps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (progFlow p) [] []) vars
  es <- mes
  dagProgDeps <- checkCycles progFlowDeps
  return $ ProgDeps nodeDeps (InterNodeDeps dagProgDeps vs es)

mkDepsNode :: String -> Map Identifier Constant -> Node -> DepMonad NodeDeps
mkDepsNode scope consts node = do
  let scopedName = scope ++ (identString $ nodeName node)
  subDeps <- mapM (mkDepsNode (scopedName ++ "_") consts) $ declsNode $ nodeDecls node
  let vars = varMap node `Map.union` (fmap (const Constant) consts)
  let (mes, (vs, deps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (nodeFlow node) (nodeOutputDefs node) (nodeAutomata node)) vars
  es <- mes
  dagDeps <- checkCycles deps
  return $ Map.insert scopedName (InterNodeDeps dagDeps vs es) (Map.unions subDeps)

-- | We redefine 'Data.Graph.Inductive.NodeMap.NodeMapM' here, because
--    the original type alias does not allow leaving the monadic return type
--    unbound.
type DepNodeMapM = State (NodeMap Var, Gr Var ())

type DepGraphM = ErrorT String (ReaderT VarMap DepNodeMapM)
type ExprMap = Map Var Expr

mkDepsNodeParts :: Flow -> [InstantDefinition] -> [Automaton] -> DepGraphM ExprMap
mkDepsNodeParts f o a = do
  e1 <- mkDepsFlow GlobalMode f
  e2 <- foldlM (mkDepsInstant GlobalMode) e1 o
  e3s <- mapM mkDepsAutomaton a
  return $ foldl Map.union e2 e3s

mkDepsFlow :: Mode -> Flow -> DepGraphM ExprMap
mkDepsFlow m (Flow d s) = do
  e1 <- foldlM (mkDepsInstant m) Map.empty d
  foldlM (mkDepsState m) e1 s

mkDepsInstant :: Mode -> ExprMap -> InstantDefinition -> DepGraphM ExprMap
mkDepsInstant m boundExprs (InstantDef xs e) = do
  us <- mapM varUsage xs
  let xus = zipWith (, , m) xs us
  let ds = getDeps $ untyped e
  forM_ xus (insDeps ds)
  return $ foldl (\boundExprs' xu -> Map.insert xu e boundExprs') boundExprs xus

mkDepsState :: Mode -> ExprMap -> StateTransition -> DepGraphM ExprMap
mkDepsState m boundExprs (StateTransition x e) = do
  let xu = (x, StateOut, m)
  let ds = getDeps $ untyped e
  insDeps ds xu
  return $ Map.insert xu e boundExprs

mkDepsAutomaton :: Automaton -> DepGraphM ExprMap
mkDepsAutomaton = (fmap Map.unions) . (mapM mkDepsLocation) . automLocations
  where
    mkDepsLocation :: Location -> DepGraphM ExprMap
    mkDepsLocation (Location l flow) = mkDepsFlow (LocationMode l) flow

lift2 :: (Monad m, Monad (t1 m), MonadTrans t1, MonadTrans t2) => m a -> t2 (t1 m) a
lift2 = lift . lift

varUsage :: Identifier -> DepGraphM VarUsage
varUsage v = do
  vars <- lift ask
  case Map.lookup v vars of
    Just u -> return u
    Nothing -> throwError $ "Unknown variable " ++ prettyIdentifier v

insVar :: Var -> DepGraphM ()
insVar = void . lift2 . insMapNodeM'

insVars :: [Var] -> DepGraphM ()
insVars = void . lift2 . insMapNodesM'

insDep :: Var -> Var -> DepGraphM ()
insDep from = lift2 . insMapEdgeM . (from, ,())

-- | Inserts a dependency from each given identifier
--  to /x/ to the given variable /v/. /x/ is treated
--  as non-state-local variable, since we don't bother
--  where it is written, but only that it is readable.
insDeps :: [Identifier] -> Var -> DepGraphM ()
insDeps ds xu = do
  insVar xu
  ds' <- mapM (\v -> varUsage v >>= return . (v,,GlobalMode)) ds
  insVars ds'
  mapM_ (insDep xu) ds'
  insGlobLocDeps xu

-- | Inserts dependencies for a variable from
--    global usage to using it inside a location.
--    With this we can treat a variable as non-local
--    for reading but distinguish writing in the
--    respective states (see 'insDeps').
insGlobLocDeps :: Var -> DepGraphM ()
insGlobLocDeps (_, _, GlobalMode) = return ()
insGlobLocDeps v@(x, u, _) = do
    let vG = (x, u, GlobalMode)
    insVar vG
    insDep vG v

getDeps :: UExpr (Typed UExpr) -> [Identifier]
getDeps (AtExpr (Typed (AtomVar ident) _)) = [ident]
getDeps (AtExpr _) = []
getDeps (LogNot e) = getDeps $ untyped e
getDeps (Expr2 _ e1 e2) = (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Ite c e1 e2) = (getDeps $ untyped c) ++ (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Constr (RecordConstr _ es)) = concat $ map (getDeps . untyped) es
getDeps (Select x _) = [x]
getDeps (Project x _) = [x]
getDeps (NodeUsage _ es) = concat $ map (getDeps . untyped) es
