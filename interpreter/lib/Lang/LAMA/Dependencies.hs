{-# LANGUAGE ScopedTypeVariables, TupleSections #-}

module Lang.LAMA.Dependencies where -- (
--   Assignment, NodeDeps, Dependencies, mkDependencies
-- ) where

import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Tree as GTree
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

instance forall a b. (Show a, Show b) => Show (Gr a b) where
  show g =
    let n = G.labNodes g
        e = G.labEdges g
        g' = G.mkGraph n e :: GTree.Gr a b
    in show g'

data VarUsage = Constant | Input | Output | Local | StateIn | StateOut deriving (Show, Eq, Ord)
type VarMap = Map Identifier VarUsage
varMap :: Node -> VarMap
varMap n =
  (Map.fromList $ map ((, Input) . varIdent) $ nodeInputs n) `Map.union`
  (Map.fromList $ map ((, Output) . varIdent) $ nodeOutputs n) `Map.union`
  (Map.fromList $ map ((, Local) . varIdent) $ nodeLocals n) `Map.union`
  (Map.fromList $ map ((, StateIn) . varIdent) $ nodeState n)

data Assignment = SimpleAssign Expr | NodeAssign NodeUsage deriving Show
type NodeDeps = DAG Gr Assignment ()
-- | Dependencies of assignments in nodes
newtype Dependencies = Dependencies (Map Identifier NodeDeps) deriving (Show)

mkDependencies :: Program -> Either String Dependencies
mkDependencies = undefined

data Mode = GlobalMode | LocationMode Identifier deriving (Eq, Ord, Show)
type Var = (Identifier, VarUsage, Mode)
data InterNodeDeps = InterNodeDeps {
    graph :: DAG Gr Var (),
    vars :: G.NodeMap Var,
    exprs :: Map Var Assignment
  }

instance Show InterNodeDeps where
  show = show . graph 

type InterDeps = Map Identifier InterNodeDeps

type DepMonad = Either String

checkCycles :: Gr Var () -> Either String (DAG Gr Var ())
checkCycles g = case mkDAG g of
  Left c -> Left $ "Cyclic dependency: " ++ depList g c
  Right dag -> Right dag
  where
    depList :: Gr Var () -> [G.Node] -> String
    depList h = intercalate " -> " . map (maybe "" id . fmap (\(v, u, m) -> show u ++ " in " ++ show m ++ " " ++ prettyIdentifier v) . G.lab h)

mkDepsProgram :: Program -> DepMonad InterDeps
mkDepsProgram (Program { progConstantDefinitions=consts, progMainNode=mainNode })
  = mkDepsNode consts mainNode

mkDepsNode :: Map Identifier Constant -> Node -> DepMonad InterDeps
mkDepsNode consts node = do
  subDeps <- mapM (mkDepsNode consts) $ nodeSubNodes node
  let vars = varMap node `Map.union` (fmap (const Constant) consts)
  let (mes, (vs, deps)) = G.run G.empty $ runReaderT (runErrorT $ nodeDeps (nodeFlow node) (nodeAutomata node)) vars
  es <- mes
  dagDeps <- checkCycles deps
  return $ Map.insert (nodeName node) (InterNodeDeps dagDeps vs es) (Map.unions subDeps)

-- | We redefine 'Data.Graph.Inductive.NodeMap.NodeMapM' here, because
--    the original type alias does not allow leaving the monadic return type
--    unbound.
type DepNodeMapM = State (NodeMap Var, Gr Var ())

type DepGraphM = ErrorT String (ReaderT VarMap DepNodeMapM)
type ExprMap = Map Var Assignment

lift2 :: (Monad m, Monad (t1 m), MonadTrans t1, MonadTrans t2) => m a -> t2 (t1 m) a
lift2 = lift . lift

varUsage :: Identifier -> DepGraphM VarUsage
varUsage v = do
  vars <- lift ask
  case Map.lookup v vars of
    Just u -> return u
    Nothing -> fail $ "Unknown variable " ++ prettyIdentifier v

nodeDeps :: Flow -> [Automaton] -> DepGraphM ExprMap
nodeDeps f a = do
  e1 <- mkDepsFlow GlobalMode f
  e2s <- mapM mkDepsAutomaton a
  return $ foldl Map.union e1 e2s

mkDepsFlow :: Mode -> Flow -> DepGraphM ExprMap
mkDepsFlow m (Flow d o s) = do
  e1 <- foldlM (mkDepsInstant m) Map.empty d
  e2 <- foldlM (mkDepsInstant m) e1 o
  foldlM (mkDepsState m) e2 s

mkDepsInstant :: Mode -> ExprMap -> InstantDefinition -> DepGraphM ExprMap
mkDepsInstant m boundExprs (SimpleDef x e) = do
  u <- varUsage x
  let xu = (x, u, m)
  let ds = getDeps $ untyped e
  insDeps ds xu 
  return $ Map.insert xu (SimpleAssign e) boundExprs

mkDepsInstant m boundExprs (NodeUsageDef p nu@(NodeUsage _ es)) = do
  u <- mapM varUsage p
  let pu = zip3 p u (repeat m)
  let ds = concat $ map (getDeps . untyped) es
  mapM_ (insDeps ds) pu
  return $ foldl (\be v -> Map.insert v (NodeAssign nu) be) boundExprs pu

insDeps :: [Identifier] -> Var -> DepGraphM ()
insDeps ds xu = do
  void $ lift2 $ insMapNodeM' xu
  ds' <- mapM (\v -> varUsage v >>= return . (v,,GlobalMode)) ds
  void $ lift2 $ insMapNodesM' $ ds'
  lift2 $ insMapEdgesM $ map (\x' -> (xu,x',())) ds'
  insGlobLocDeps xu


mkDepsState :: Mode -> ExprMap -> StateTransition -> DepGraphM ExprMap
mkDepsState m boundExprs (StateTransition x e) = do
  let xu = (x, StateOut, m)
  void $ lift2 $ insMapNodeM' xu
  let ds = getDeps $ untyped e
  ds' <- mapM (\v -> varUsage v >>= return . (v,,GlobalMode)) ds
  void $ lift2 $ insMapNodesM' ds'
  lift2 $ insMapEdgesM $ map (\x' -> (xu,x',())) ds'
  insGlobLocDeps xu
  return $ Map.insert xu (SimpleAssign e) boundExprs

mkDepsAutomaton :: Automaton -> DepGraphM ExprMap
mkDepsAutomaton = (fmap Map.unions) . (mapM mkDepsLocation) . automLocations
  where
    mkDepsLocation :: Location -> DepGraphM ExprMap
    mkDepsLocation (Location l flow) = mkDepsFlow (LocationMode l) flow

-- | Inserts dependencies for a variable from
--    global usage to using it inside a location.
--    The given variables should not be used
--    globally, as that would introduce loops.
insGlobLocDeps :: Var -> DepGraphM ()
insGlobLocDeps (_, _, GlobalMode) = return ()
insGlobLocDeps v@(x, u, _) = do
    let vG = (x, u, GlobalMode)
    void $ lift2 $ insMapNodeM' vG
    void $ lift2 $ insMapEdgeM (vG, v, ())

getDeps :: UExpr (Typed UExpr) -> [Identifier]
getDeps (AtExpr (Typed (AtomVar ident) _)) = [ident]
getDeps (AtExpr _) = []
getDeps (LogNot e) = getDeps $ untyped e
getDeps (Expr2 _ e1 e2) = (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Ite c e1 e2) = (getDeps $ untyped c) ++ (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Constr (RecordConstr _ es)) = concat $ map (getDeps . untyped) es
getDeps (Select x _) = [x]
getDeps (Project x _) = [x]
