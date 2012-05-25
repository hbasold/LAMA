{-# LANGUAGE TupleSections #-}

module Lang.LAMA.Dependencies (
  VarUsage(..), Mode(..), Var,
  NodeDeps(..), ProgDeps(..),
  mkDeps
) where

import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.NodeMapSupport as G
import Data.Graph.Inductive.DAG
import qualified Data.Graph.Inductive.Graph as G
import Data.Map as Map hiding (map)
import Data.List (intercalate)
import Data.Foldable (foldlM)

import Control.Monad.Error (ErrorT, runErrorT, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad (forM_, void)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure

-- | Context in which a variable is used. With this context state variables
--  can be distinguished if they are use on lhs or rhs of an assignment.
data VarUsage =
  Constant
  | Input | Output
  | Local | StateIn | StateOut
  deriving (Show, Eq, Ord)

-- | Characterizes where a variable is defined (in a normal flow
--  or in a flow a state)
data Mode = GlobalMode | LocationMode Identifier deriving (Eq, Ord, Show)

-- | Bundle an identifier with its context.
type Var = (Identifier, VarUsage, Mode)

-- | Dependencies of a node
data NodeDeps = NodeDeps {
    nodeDepsNodes :: Map Identifier NodeDeps,
    nodeDepsFlow :: DAG Gr (Var, Expr) ()
  }

-- | Dependencies of the program
data ProgDeps = ProgDeps {
    progDepsNodes :: Map Identifier NodeDeps,
    progDepsFlow :: DAG Gr (Var, Expr) ()
  }

-- | Calculates the dependencies of a given program
--  and its defined nodes.
--  May return an error if the dependencies are cyclic
--  somewhere.
mkDeps :: Program -> Either String ProgDeps
mkDeps p = do
    d <- mkDepsProgram p
    let nodes = fmap convNodeGraphs $ ipDepsNodes d
    let exprDepGr = dagMapNLab (addExpr $ ipDepsExprs d) (ipDepsGraph d)
    return $ ProgDeps nodes exprDepGr
  where
    convNodeGraphs n =
      let nodes = fmap convNodeGraphs $ inDepsNodes n
          exprDepGr = dagMapNLab (addExpr $ inDepsExprs n) (inDepsGraph n)
      in NodeDeps nodes exprDepGr

type InterIdentCtx = (Identifier, VarUsage, Mode)

interCtxGetIdent :: InterIdentCtx -> Identifier
interCtxGetIdent (x, _, _) = x

type InterDepDAG = DAG Gr InterIdentCtx ()

-- | Carries node dependencies with split up
--  information to ease calculation.
data InterNodeDeps = InterNodeDeps {
    inDepsNodes :: Map Identifier InterNodeDeps,
    inDepsGraph :: InterDepDAG,
    inDepsVars :: G.NodeMap InterIdentCtx,
    inDepsExprs :: Map InterIdentCtx Expr
  }

-- | Carries program dependencies with split up
--  information to ease calculation.
data InterProgDeps = InterProgDeps {
    ipDepsNodes :: Map Identifier InterNodeDeps,
    ipDepsGraph :: InterDepDAG,
    ipDepsVars :: G.NodeMap InterIdentCtx,
    ipDepsExprs :: Map InterIdentCtx Expr
  }

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

type DepMonad = Either String

-- | Checks of the given graph is a DAG, if not results
--  in an error containing the found cycle.
checkCycles :: Gr InterIdentCtx () -> DepMonad (InterDepDAG)
checkCycles g = case mkDAG g of
  Left c -> throwError $ "Cyclic dependency: " ++ depList g c
  Right dag -> return dag
  where
    depList :: Gr InterIdentCtx () -> [G.Node] -> String
    depList h = intercalate " -> " . map (maybe "" id . fmap (\(v, u, m) -> show u ++ " in " ++ show m ++ " " ++ prettyIdentifier v) . G.lab h)

mkDepsProgram :: Program -> DepMonad InterProgDeps
mkDepsProgram p = do
  nodeDeps <- mkDepsMapNodes (progConstantDefinitions p) (declsNode $ progDecls p)

  let vars = declsVarMap $ progDecls p
  let (mes, (vs, progFlowDeps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (progFlow p) [] []) vars
  es <- mes
  dagProgDeps <- checkCycles progFlowDeps
  return $ InterProgDeps nodeDeps dagProgDeps vs es

mkDepsNode :: Map Identifier Constant -> Node -> DepMonad InterNodeDeps
mkDepsNode consts node = do
  subDeps <- mkDepsMapNodes consts (declsNode $ nodeDecls node)

  let vars = varMap node `Map.union` (fmap (const Constant) consts)
  let (mes, (vs, deps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (nodeFlow node) (nodeOutputDefs node) (nodeAutomata node)) vars
  es <- mes
  dagDeps <- checkCycles deps
  return $ InterNodeDeps subDeps dagDeps vs es

mkDepsMapNodes :: Map Identifier Constant -> [Node] -> DepMonad (Map Identifier InterNodeDeps)
mkDepsMapNodes consts nodes = do
  nodeDeps <- mapM (mkDepsNode consts) nodes
  return $ Map.fromList $ zip (map nodeName nodes) nodeDeps

type DepGraphM = ErrorT String (ReaderT VarMap (NodeMapM InterIdentCtx () Gr))
type ExprMap = Map InterIdentCtx Expr

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

varUsage :: Identifier -> DepGraphM VarUsage
varUsage v = do
  vars <- lift ask
  case Map.lookup v vars of
    Just u -> return u
    Nothing -> throwError $ "Unknown variable " ++ prettyIdentifier v

insVar :: InterIdentCtx -> DepGraphM ()
insVar = void . insMapNodeM'

insVars :: [InterIdentCtx] -> DepGraphM ()
insVars = void . insMapNodesM'

insDep :: InterIdentCtx -> InterIdentCtx -> DepGraphM ()
insDep from = lift2 . insMapEdgeM . (from, ,())
  where lift2 = lift . lift

-- | Inserts a dependency from each given identifier
--  to /x/ to the given variable /v/. /x/ is treated
--  as non-state-local variable, since we don't bother
--  where it is written, but only that it is readable.
insDeps :: [Identifier] -> InterIdentCtx -> DepGraphM ()
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
insGlobLocDeps :: InterIdentCtx -> DepGraphM ()
insGlobLocDeps (_, _, GlobalMode) = return ()
insGlobLocDeps v@(x, u, _) = do
    let vG = (x, u, GlobalMode)
    insVar vG
    insDep vG v

getDeps :: GExpr Constant Atom Expr -> [Identifier]
getDeps (AtExpr (AtomVar ident)) = [ident]
getDeps (AtExpr _) = []
getDeps (LogNot e) = getDeps $ untyped e
getDeps (Expr2 _ e1 e2) = (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Ite c e1 e2) = (getDeps $ untyped c) ++ (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Constr (RecordConstr _ es)) = concat $ map (getDeps . untyped) es
getDeps (Select x _) = [x]
getDeps (Project x _) = [x]
getDeps (NodeUsage _ es) = concat $ map (getDeps . untyped) es
