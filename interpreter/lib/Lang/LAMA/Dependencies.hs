{-# LANGUAGE TupleSections #-}

module Lang.LAMA.Dependencies (
  VarUsage(..), Mode(..), ExprCtx(..),
  IdentCtx, ctxGetIdent,
  NodeDeps(..), ProgDeps(..),
  mkDeps, getFreeVariables
) where

import Prelude hiding (mapM, foldl)

import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.NodeMapSupport as G
import Data.Graph.Inductive.DAG
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.UnlabeledGraph as U
import Data.Graph.Inductive.Graph (Context, ufold, insEdges, pre)
import Data.Map as Map hiding (map, null, foldl)
import qualified Data.IntMap as IMap
import Data.List (intercalate)
import Data.Foldable (foldl, foldlM)
import Data.Traversable (mapM)
import qualified Data.ByteString.Char8 as BS

import Control.Monad.Error (ErrorT, runErrorT, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad (forM_, void)
import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure

import Data.Graph.Inductive.GenShow

-- | Context in which a variable is used. With this context state variables
--  can be distinguished if they are use on lhs or rhs of an assignment.
data VarUsage =
  Constant
  | Input | Output
  | Local | StateIn | StateOut
  deriving (Show, Eq, Ord)

-- | Characterizes where a variable is defined (in a normal flow
--  or in a flow a state)
data Mode = GlobalMode | LocationRefMode | LocationMode Identifier deriving (Eq, Ord, Show)

-- | Bundle an identifier with its context.
type IdentCtx = (BS.ByteString, VarUsage, Mode)

ctxGetIdent :: IdentCtx -> BS.ByteString
ctxGetIdent (i, _, _) = i

-- | Puts an expression (if any) into its context. A variable may
--  be not defined at all, have one global expression or
--  one for each location in the automaton.
data ExprCtx = NoExpr | GlobalExpr Instant | LocalExpr (Map BS.ByteString Instant) deriving Show

-- | Dependencies of a node
data NodeDeps = NodeDeps {
    nodeDepsNodes :: Map Identifier NodeDeps,
    nodeDepsFlow :: DAG Gr (IdentCtx, ExprCtx) ()
  }

-- | Dependencies of the program
--  TODO: and nodes
data ProgDeps = ProgDeps {
    progDepsNodes :: Map Identifier NodeDeps,
    progDepsFlow :: DAG Gr (IdentCtx, ExprCtx) ()
  }

getFreeVariables :: ProgDeps -> [BS.ByteString]
getFreeVariables d = ufold putIfFree [] $ progDepsFlow d
  where putIfFree (_, _, ((x, _, _), e), _) vs = case e of
          NoExpr -> x : vs
          _ -> vs

-- | Calculates the dependencies of a given program
--  and its defined nodes.
--  May return an error if the dependencies are cyclic
--  somewhere.
mkDeps :: Program -> Either String ProgDeps
mkDeps p = do
    d <- mkDepsProgram p
    nodes <- mapM convNodeDeps $ ipDepsNodes d
    (dg, refs) <- mergeLocationNodes $ ipDepsGraph d
    exprDepGr <- dagMapNLabM (fmap dropLocInfo . (addExprFV refs $ ipDepsExprs d)) dg
    return $ ProgDeps nodes exprDepGr

  where
    convNodeDeps :: InterNodeDeps -> Either String NodeDeps
    convNodeDeps n = do
      nodes <- mapM convNodeDeps $ inDepsNodes n
      (dg, refs) <- mergeLocationNodes $ inDepsGraph n
      exprDepGr <- dagMapNLabM (fmap dropLocInfo . (addExprNoFV refs $ inDepsExprs n)) dg
      return $ NodeDeps nodes exprDepGr

    dropLocInfo ((i, u, m), e) = ((identBS i, u, m), e)

    -- | Allow variables to be free
    addExprFV :: RefMap -> InstantMap -> InterIdentCtx -> Either String (InterIdentCtx, ExprCtx)
    addExprFV refs es v@(x, _, m) = case m of
      GlobalMode -> case Map.lookup v es of
        Nothing -> return (v, NoExpr)
        Just e -> return (v, GlobalExpr e)
      LocationRefMode -> case Map.lookup v refs of
        Nothing -> throwError $ prettyIdentifier x ++ " references to a definition in location which does not exist"
        Just refVars -> lookupExprs es refVars >>= \refExprs -> return (v, LocalExpr refExprs)
      LocationMode _ -> error "Remaining location mode" -- should no longer be present here

    addExprNoFV :: RefMap -> InstantMap -> InterIdentCtx -> Either String (InterIdentCtx, ExprCtx)
    addExprNoFV refs es v@(x, u, _) = case u of
      Constant -> return (v, NoExpr)
      Input -> return (v, NoExpr)
      StateIn -> return (v, NoExpr)
      _ -> addExprFV refs es v >>= \(v', e) ->
        case e of
          NoExpr -> throwError $ prettyIdentifier x ++ " (" ++ show u ++ ")" ++ " not defined"
          _ -> return (v', e)

    lookupExprs es rs = case mapM (flip Map.lookup es) rs of
      Nothing -> throwError $ "Variable in location undefined"
      Just res -> return $ Map.fromList $ zip (map (identBS . interCtxGetIdent) rs) res


type RefMap = Map InterIdentCtx [InterIdentCtx]

mergeLocationNodes :: InterDepDAG -> Either String (InterDepDAG, RefMap)
mergeLocationNodes dg =
  let (g', nodeVarMap, refs) = ufold (mergeLs dg) (G.empty, Map.empty, Map.empty) (getGraph dg)
      g'' = setVarLabels nodeVarMap g'
      mdg' = mkDAG g''
  in case mdg' of
    Left cycl -> throwError $ "Merging lead to cycle: " ++ show cycl -- should not happen!
    Right dg' -> return (dg', refs)
  where
    mergeLs :: InterDepDAG -> Context InterIdentCtx () ->
                (Gr () (), Map G.Node InterIdentCtx, RefMap) -> (Gr () (), Map G.Node InterIdentCtx, RefMap)
    -- x is not local to a location and does not refer to variable inside a
    -- location, it is set in global flow.
    -- If its successors are set in a location then it is a reference node. In that
    -- case its label is updated and all successors (which are set in a location)
    -- are dropped.
    -- Edges coming from a locally set variable have to be changed, so that
    -- they come now from the corresponding reference node (see last case of
    -- mergeLs.
    mergeLs deps (i, n, v@(x, u, GlobalMode), o) (g, nodeVarMap, refs) =
      let isRef = locations deps o
          i' = redirect deps i
          g' = if isRef
                  then U.merge' (i', n, (), []) g
                  else U.merge' (i', n, (), o) g
          v' = if isRef then (x, u, LocationRefMode) else v
      in (g', Map.insert n v' nodeVarMap, refs)
    -- Should not be present in the given graph
    mergeLs _ (_, _, (_, _, LocationRefMode), _) _ = undefined
    -- If x is set in a location, its incoming edges will be attached to its unique
    -- predecessor which is then a reference node. Additionally a mapping from the
    -- reference to x is set so that the expressions can be recovered.
    -- This should form a graph homomorphism.
    mergeLs deps (_, n, v@(x, u, LocationMode _), o) (g, nodeVarMap, refs) =
      case pre deps n of
        [r] -> (insEdges (edgesFromTo r o) $ U.insNode' r g , nodeVarMap, alter (addRef v) (x, u, LocationRefMode) refs)
        ps -> error $ "Predecessor should be unique (at " ++ show v ++ "), "
                        ++ " but has " ++ show ps ++ " in : " ++ show deps

    edgesFromTo r = map (r,,()) . map snd

    redirect deps =
      map (\((), n) -> case G.lab deps n of
            Just (_, _, LocationMode _) -> ((), head $ pre deps n)
            _ -> ((), n)
          )

    -- if one successor is defined in a location
    -- by construction all are so.
    locations _ [] = False
    locations deps (((), d):_) = case G.lab deps d of
      Nothing -> False -- should not happen
      Just (_, _, m) -> case m of
        LocationMode _ -> True
        _ -> False

    addRef l = maybe (Just [l]) (Just . (l:))

    setVarLabels nodeVarMap = G.gmap (setVarLabel nodeVarMap)
      where
        setVarLabel nvm (i, n, (), o) = case Map.lookup n nvm of
          Nothing -> error $ "could not find variable for " ++ show n ++ " in " ++ show nvm
          Just v -> (i, n, v, o)


type InterIdentCtx = (Identifier, VarUsage, Mode)

interCtxGetIdent :: InterIdentCtx -> Identifier
interCtxGetIdent (x, _, _) = x

type InterDepDAG = DAG Gr InterIdentCtx ()
type InstantMap = Map InterIdentCtx Instant

-- | Carries node dependencies with split up
--  information to ease calculation.
data InterNodeDeps = InterNodeDeps {
    inDepsNodes :: Map Identifier InterNodeDeps,
    inDepsGraph :: InterDepDAG,
    inDepsVars :: G.NodeMap InterIdentCtx,
    inDepsExprs :: InstantMap
  }

-- | Carries program dependencies with split up
--  information to ease calculation.
data InterProgDeps = InterProgDeps {
    ipDepsNodes :: Map Identifier InterNodeDeps,
    ipDepsGraph :: InterDepDAG,
    ipDepsVars :: G.NodeMap InterIdentCtx,
    ipDepsExprs :: InstantMap
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
  let (mes, (vs, deps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (nodeFlow node) (nodeOutputDefs node) (IMap.elems $ nodeAutomata node)) vars
  es <- mes
  dagDeps <- checkCycles deps
  return $ InterNodeDeps subDeps dagDeps vs es

mkDepsMapNodes :: Map Identifier Constant -> Map Identifier Node -> DepMonad (Map Identifier InterNodeDeps)
mkDepsMapNodes consts nodes = do
  let (nNames, nDefs) = unzip $ Map.toAscList nodes
  nodeDeps <- mapM (mkDepsNode consts) nDefs
  return $ Map.fromAscList $ zip nNames nodeDeps

type DepGraphM = ErrorT String (ReaderT VarMap (NodeMapM InterIdentCtx () Gr))

mkDepsNodeParts :: Flow -> [InstantDefinition] -> [Automaton] -> DepGraphM InstantMap
mkDepsNodeParts f o a = do
  e1 <- mkDepsFlow GlobalMode f
  e2 <- foldlM (mkDepsInstant GlobalMode) e1 o
  e3s <- mapM mkDepsAutomaton a
  return $ foldl Map.union e2 e3s

-- | Calculates the dependencies of the definitions
--    and the state changes and gives back a map
--    from variables to the defining statement.
mkDepsFlow :: Mode -> Flow -> DepGraphM InstantMap
mkDepsFlow m (Flow d s) = do
  e1 <- foldlM (mkDepsInstant m) Map.empty d
  foldlM (mkDepsState m) e1 s

-- | Inserts a dependency from the assigned variables to each
--    variable used in the statement on the rhs. Additionally
--    adds each assigned variable to the given statement map
--    so that it maps to the rhs.
--    The variables are being put in the requested mode.
mkDepsInstant :: Mode -> InstantMap -> InstantDefinition -> DepGraphM InstantMap
mkDepsInstant m boundExprs (InstantDef xs i) = do
  us <- mapM varUsage xs
  let xus = zipWith (, , m) xs us
  let ds = getDepsInstant $ untyped i
  forM_ xus (insDeps ds)
  return $ foldl (\boundExprs' xu -> Map.insert xu i boundExprs') boundExprs xus

mkDepsState :: Mode -> InstantMap -> StateTransition -> DepGraphM InstantMap
mkDepsState m boundExprs (StateTransition x e) = do
  let xu = (x, StateOut, m)
  let ds = getDeps $ untyped e
  insDeps ds xu
  return $ Map.insert xu (preserveType InstantExpr e) boundExprs

mkDepsAutomaton :: Automaton -> DepGraphM InstantMap
mkDepsAutomaton (Automaton locs _ edges) = do
  im <- (fmap Map.unions) $ mapM mkDepsLocation locs
  mapM_ (mkDepsEdge (map fst $ Map.toList im)) edges
  return im
  where
    -- Insert a dependency for each variable used in some
    -- location to each variable used in the conditions
    -- of the edges of an automaton. This ensures that no
    -- condition depends on a variable that could change
    -- the condition after a transition.
    mkDepsEdge :: [InterIdentCtx] -> Edge -> DepGraphM ()
    mkDepsEdge vs (Edge _ _ e) = do
      let ds = getDeps $ untyped e
      mapM_ (insDeps ds) vs

    mkDepsLocation :: Location -> DepGraphM InstantMap
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

-- | Inserts a dependency from the first to the
--    second context.
insDep :: InterIdentCtx -> InterIdentCtx -> DepGraphM ()
insDep from = lift2 . insMapEdgeM' . (from, ,())
  where lift2 = lift . lift

-- | Inserts a dependency to each given identifier
--  from /x/ to the given variable /v/. /x/ is treated
--  as non-state-local variable, since we don't bother
--  where it is written, but only that it is readable.
insDeps :: [Identifier] -> InterIdentCtx -> DepGraphM ()
insDeps ds xu = do
  insVar xu
  ds' <- mapM (\v -> varUsage v >>= return . (v,,GlobalMode)) ds
  insVars ds'
  forM_ ds' (\(v, u, m) -> case u of { StateIn -> insVar (v, StateOut, m) ; _-> return () })
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

getDepsInstant :: GInstant Expr Instant -> [Identifier]
getDepsInstant (InstantExpr e) = getDeps $ untyped e
getDepsInstant (NodeUsage _ es) = concat $ map (getDeps . untyped) es

getDeps :: GExpr Constant Atom Expr -> [Identifier]
getDeps (AtExpr (AtomVar ident)) = [ident]
getDeps (AtExpr _) = []
getDeps (LogNot e) = getDeps $ untyped e
getDeps (Expr2 _ e1 e2) = (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Ite c e1 e2) = (getDeps $ untyped c) ++ (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Constr (RecordConstr _ es)) = concat $ map (getDeps . untyped) es
getDeps (Select x _) = [x]
getDeps (Project x _) = [x]
