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
import Data.Map as Map hiding (map, null, foldl, (\\))
import Data.List (intercalate, (\\))
import Data.Foldable (foldl, foldlM)
import Data.Traversable (mapM)
import qualified Data.ByteString.Char8 as BS
import Data.Maybe (isJust)

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
data Mode i = GlobalMode | LocationRefMode Int | LocationMode Int i deriving (Eq, Ord, Show)

-- | Bundle an identifier with its context.
type IdentCtx i = (BS.ByteString, VarUsage, Mode i)

ctxGetIdent :: IdentCtx i -> BS.ByteString
ctxGetIdent (i, _, _) = i

-- | Puts an expression (if any) into its context. A variable may
--  be not defined at all, have one global expression or
--  one for each location in the automaton.
data ExprCtx i =
  NoExpr
  | GlobalExpr (InstantDefinition i)
  | LocalExpr Int (Map BS.ByteString (InstantDefinition i))
  deriving Show

-- | Dependencies of a node
data NodeDeps i = NodeDeps {
    nodeDepsNodes :: Map i (NodeDeps i),
    nodeDepsFlow :: DAG Gr (IdentCtx i, ExprCtx i) ()
  }

-- | Dependencies of the program
--  TODO: and nodes
data ProgDeps i = ProgDeps {
    progDepsNodes :: Map i (NodeDeps i),
    progDepsFlow :: DAG Gr (IdentCtx i, ExprCtx i) ()
  }

getFreeVariables :: ProgDeps i -> [SimpIdent]
getFreeVariables d = ufold putIfFree [] $ progDepsFlow d
  where putIfFree (_, _, ((x, u, _), e), _) vs = case e of
          NoExpr -> case u of
            Constant -> vs
            StateIn -> vs
            _ -> SimpIdent x : vs
          _ -> vs

-- | Calculates the dependencies of a given program
--  and its defined nodes.
--  May return an error if the dependencies are cyclic
--  somewhere.
mkDeps :: Ident i => Program i -> Either String (ProgDeps i)
mkDeps p = do
    d <- mkDepsProgram p
    nodes <- mapM convNodeDeps $ ipDepsNodes d
    (dg, refs) <- mergeLocationNodes $ ipDepsGraph d
    exprDepGr <- dagMapNLabM (fmap dropLocInfo . (addExprFV refs $ ipDepsExprs d)) dg
    return $ ProgDeps nodes exprDepGr

  where
    convNodeDeps :: Ident i => InterNodeDeps i -> Either String (NodeDeps i)
    convNodeDeps n = do
      nodes <- mapM convNodeDeps $ inDepsNodes n
      (dg, refs) <- mergeLocationNodes $ inDepsGraph n
      exprDepGr <- dagMapNLabM (fmap dropLocInfo . (addExprNoFV refs $ inDepsExprs n)) dg
      return $ NodeDeps nodes exprDepGr

    dropLocInfo ((i, u, m), e) = ((identBS i, u, m), e)

    -- | Allow variables to be free
    addExprFV :: Ident i => RefMap i -> InstantMap i -> InterIdentCtx i -> Either String (InterIdentCtx i, ExprCtx i)
    addExprFV refs es v@(x, _, m) = case m of
      GlobalMode -> case Map.lookup v es of
        Nothing -> return (v, NoExpr)
        Just e -> return (v, GlobalExpr e)
      LocationRefMode autom -> case Map.lookup v refs of
        Nothing -> throwError $ identPretty x ++ " references to a definition in location which does not exist"
        Just refVars -> lookupExprs es refVars >>= \refExprs -> return (v, LocalExpr autom refExprs)
      LocationMode _ _ -> error "Remaining location mode" -- should no longer be present here

    addExprNoFV :: Ident i => RefMap i -> InstantMap i -> InterIdentCtx i -> Either String (InterIdentCtx i, ExprCtx i)
    addExprNoFV refs es v@(x, u, _) = case u of
      Constant -> return (v, NoExpr)
      Input -> return (v, NoExpr)
      StateIn -> return (v, NoExpr)
      _ -> addExprFV refs es v >>= \(v', e) ->
        case e of
          NoExpr -> throwError $ identPretty x ++ " (" ++ show u ++ ")" ++ " not defined"
          _ -> return (v', e)

    lookupExprs es rs = case mapM (flip Map.lookup es) rs of
      Nothing -> throwError $ "Variable in location undefined"
      Just res -> return $ Map.fromList $ zip (map (identBS . interCtxGetLocation) rs) res


type RefMap i = Map (InterIdentCtx i) [InterIdentCtx i]

mergeLocationNodes :: Ident i => InterDepDAG i -> Either String (InterDepDAG i, RefMap i)
mergeLocationNodes dg =
  let (g', nodeVarMap, refs) = ufold (mergeLs dg) (G.empty, Map.empty, Map.empty) (getGraph dg)
      g'' = setVarLabels nodeVarMap g'
      mdg' = mkDAG g''
  in case mdg' of
    Left cycl -> throwError $ "Merging lead to cycle: " ++ show cycl -- should not happen!
    Right dg' -> return (dg', refs)
  where
    mergeLs :: Ident i => InterDepDAG i -> Context (InterIdentCtx i) () ->
                (Gr () (), Map G.Node (InterIdentCtx i), RefMap i) -> (Gr () (), Map G.Node (InterIdentCtx i), RefMap i)
    -- x is not local to a location and does not refer to variable inside a
    -- location, it is set in global flow.
    -- If its successors are set in a location then it is a reference node. In that
    -- case its label is updated and all successors (which are set in a location)
    -- are dropped.
    -- Edges coming from a locally set variable have to be changed, so that
    -- they come now from the corresponding reference node (see last case of
    -- mergeLs.
    mergeLs deps (i, n, v@(x, u, GlobalMode), o) (g, nodeVarMap, refs) =
      let ref = locations deps o
          isRef = isJust ref
          i' = redirect deps i
          g' = if isRef
                  then U.merge' (i', n, (), []) g
                  else U.merge' (i', n, (), o) g
          v' = case ref of
                Just autom -> (x, u, LocationRefMode autom)
                Nothing -> v
      in (g', Map.insert n v' nodeVarMap, refs)
    -- Should not be present in the given graph
    mergeLs _ (_, _, (_, _, LocationRefMode _), _) _ = undefined
    -- If x is set in a location, its incoming edges will be attached to its unique
    -- predecessor which is then a reference node. Additionally a mapping from the
    -- reference to x is set so that the expressions can be recovered.
    -- This should form a graph homomorphism.
    mergeLs deps (_, n, v@(x, u, LocationMode autom _), o) (g, nodeVarMap, refs) =
      case pre deps n of
        [r] -> (insEdges (edgesFromTo r o) $ U.insNode' r g , nodeVarMap, alter (addRef v) (x, u, LocationRefMode autom) refs)
        ps -> error $ "Predecessor should be unique (at " ++ show v ++ "), "
                        ++ " but has " ++ show ps ++ " in : " ++ show deps

    edgesFromTo r = map (r,,()) . map snd

    redirect deps =
      map (\((), n) -> case G.lab deps n of
            Just (_, _, LocationMode _ _) -> ((), head $ pre deps n)
            _ -> ((), n)
          )

    -- if one successor is defined in a location
    -- by construction all are so.
    locations _ [] = Nothing
    locations deps (((), d):_) = case G.lab deps d of
      Nothing -> Nothing -- should not happen
      Just (_, _, m) -> case m of
        LocationMode autom _ -> Just autom
        _ -> Nothing

    addRef l = maybe (Just [l]) (Just . (l:))

    setVarLabels nodeVarMap = G.gmap (setVarLabel nodeVarMap)
      where
        setVarLabel nvm (i, n, (), o) = case Map.lookup n nvm of
          Nothing -> error $ "could not find variable for " ++ show n ++ " in " ++ show nvm
          Just v -> (i, n, v, o)


type InterIdentCtx i = (i, VarUsage, Mode i)

interCtxGetIdent :: InterIdentCtx i -> i
interCtxGetIdent (x, _, _) = x

-- | Beware: should only be used if the context is
--    known to be from a location.
interCtxGetLocation :: InterIdentCtx i -> i
interCtxGetLocation (_, _, (LocationMode _ l)) = l
interCtxGetLocation _ = error "cannot get location from context"

type InterDepDAG i = DAG Gr (InterIdentCtx i) ()
type InstantMap i = Map (InterIdentCtx i) (InstantDefinition i)

-- | Carries node dependencies with split up
--  information to ease calculation.
data InterNodeDeps i = InterNodeDeps {
    inDepsNodes :: Map i (InterNodeDeps i),
    inDepsGraph :: InterDepDAG i,
    inDepsVars :: G.NodeMap (InterIdentCtx i),
    inDepsExprs :: InstantMap i
  }

-- | Carries program dependencies with split up
--  information to ease calculation.
data InterProgDeps i = InterProgDeps {
    ipDepsNodes :: Map i (InterNodeDeps i),
    ipDepsGraph :: InterDepDAG i,
    ipDepsVars :: G.NodeMap (InterIdentCtx i),
    ipDepsExprs :: InstantMap i
  }

type VarMap i = Map i VarUsage

varMap :: Ident i => Node i -> VarMap i
varMap n =
  (Map.fromList $ map ((, Input) . varIdent) $ nodeInputs n) `Map.union`
  (Map.fromList $ map ((, Output) . varIdent) $ nodeOutputs n) `Map.union`
  (declsVarMap $ nodeDecls n)

declsVarMap :: Ident i => Declarations i -> VarMap i
declsVarMap d =
  (Map.fromList $ map ((, Local) . varIdent) $ declsLocal d) `Map.union`
  (Map.fromList $ map ((, StateIn) . varIdent) $ declsState d)

type DepMonad = Either String

-- | Checks of the given graph is a DAG, if not results
--  in an error containing the found cycle.
checkCycles :: Ident i => Gr (InterIdentCtx i) () -> DepMonad (InterDepDAG i)
checkCycles g = case mkDAG g of
  Left c -> throwError $ "Cyclic dependency: " ++ depList g c
  Right dag -> return dag
  where
    depList :: Ident i => Gr (InterIdentCtx i) () -> [G.Node] -> String
    depList h = intercalate " -> " . map (maybe "" id . fmap (\(v, u, m) -> show u ++ " in " ++ show m ++ " " ++ identPretty v) . G.lab h)

mkDepsProgram :: Ident i => Program i -> DepMonad (InterProgDeps i)
mkDepsProgram p = do
  let consts = progConstantDefinitions p
  nodeDeps <- mkDepsMapNodes consts (declsNode $ progDecls p)

  let vars = (declsVarMap $ progDecls p) `Map.union` (fmap (const Constant) consts)
  let (mes, (vs, progFlowDeps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (progFlow p) [] []) vars
  es <- mes
  dagProgDeps <- checkCycles progFlowDeps
  return $ InterProgDeps nodeDeps dagProgDeps vs es

mkDepsNode :: Ident i => Map i (Constant i) -> Node i -> DepMonad (InterNodeDeps i)
mkDepsNode consts node = do
  subDeps <- mkDepsMapNodes consts (declsNode $ nodeDecls node)

  let vars = varMap node `Map.union` (fmap (const Constant) consts)
  let (mes, (vs, deps)) = G.run G.empty $ runReaderT (runErrorT $ mkDepsNodeParts (nodeFlow node) (nodeOutputDefs node) (Map.toList $ nodeAutomata node)) vars
  es <- mes
  dagDeps <- checkCycles deps
  return $ InterNodeDeps subDeps dagDeps vs es

mkDepsMapNodes :: Ident i => Map i (Constant i) -> Map i (Node i) -> DepMonad (Map i (InterNodeDeps i))
mkDepsMapNodes consts = mapM (mkDepsNode consts)

type DepGraphM i = ErrorT String (ReaderT (VarMap i) (NodeMapM (InterIdentCtx i) () Gr))

mkDepsNodeParts :: Ident i => Flow i -> [InstantDefinition i] -> [(Int, Automaton i)] -> DepGraphM i (InstantMap i)
mkDepsNodeParts f o a = do
  e1 <- mkDepsFlow GlobalMode f
  e2 <- foldlM (mkDepsInstant GlobalMode) e1 o
  e3s <- mapM mkDepsAutomaton a
  return $ foldl Map.union e2 e3s

-- | Calculates the dependencies of the definitions
--    and the state changes and gives back a map
--    from variables to the defining statement.
mkDepsFlow :: Ident i => Mode i -> Flow i -> DepGraphM i (InstantMap i)
mkDepsFlow m (Flow d s) = do
  e1 <- foldlM (mkDepsInstant m) Map.empty d
  foldlM (mkDepsState m) e1 s

-- | Inserts a dependency from the assigned variables to each
--    variable used in the statement on the rhs. Additionally
--    adds each assigned variable to the given statement map
--    so that it maps to the rhs.
--    The variables are being put in the requested mode.
mkDepsInstant :: Ident i => Mode i -> InstantMap i -> InstantDefinition i -> DepGraphM i (InstantMap i)
mkDepsInstant m boundExprs i@(InstantExpr x e) =
  do u <- varUsage x
     let xu = (x, u, m)
     let ds = getDeps $ untyped e
     void $ insDeps ds xu
     return $ Map.insert xu i boundExprs
mkDepsInstant m boundExprs i@(NodeUsage x _ es) =
  do u <- varUsage x
     let xu = (x, u, m)
     let ds = concat $ map (getDeps . untyped) es
     void $ insDeps ds xu
     return $ Map.insert xu i boundExprs

mkDepsState :: Ident i => Mode i -> InstantMap i -> StateTransition i -> DepGraphM i (InstantMap i)
mkDepsState m boundExprs (StateTransition x e) = do
  let xu = (x, StateOut, m)
  let ds = getDeps $ untyped e
  insDeps ds xu
  return $ Map.insert xu (InstantExpr x e) boundExprs

mkDepsAutomaton :: Ident i => (Int, Automaton i) -> DepGraphM i (InstantMap i)
mkDepsAutomaton (autom, (Automaton locs _ edges)) = do
  im <- (fmap Map.unions) $ mapM (mkDepsLocation autom) locs
  mapM_ (mkDepsEdge (map fst $ Map.toList im)) edges
  return im
  where
    -- Insert a dependency for each variable used in some
    -- location to each variable used in the conditions
    -- of the edges of an automaton. This ensures that no
    -- condition depends on a variable that could change
    -- the condition after a transition.
    mkDepsEdge :: Ident i => [InterIdentCtx i] -> Edge i -> DepGraphM i ()
    mkDepsEdge vs (Edge _ _ e) = do
      let ds = getDeps $ untyped e
      mapM_ (insDeps ds) vs

    mkDepsLocation :: Ident i => Int -> Location i -> DepGraphM i (InstantMap i)
    mkDepsLocation a (Location l flow) = mkDepsFlow (LocationMode a l) flow

varUsage :: Ident i => i -> DepGraphM i VarUsage
varUsage v = do
  vars <- lift ask
  case Map.lookup v vars of
    Just u -> return u
    Nothing -> throwError $ "Unknown variable " ++ identPretty v ++ " in " ++ show vars

insVar :: Ident i => InterIdentCtx i -> DepGraphM i ()
insVar = void . insMapNodeM'

insVars :: Ident i => [InterIdentCtx i] -> DepGraphM i ()
insVars = void . insMapNodesM'

-- | Inserts a dependency from the first to the
--    second context.
insDep :: Ident i => InterIdentCtx i -> InterIdentCtx i -> DepGraphM i ()
insDep from = lift2 . insMapEdgeM' . (from, ,())
  where lift2 = lift . lift

-- | Inserts a dependency to each given identifier
--  from /x/ to the given variable /v/. /x/ is treated
--  as non-state-local variable, since we don't bother
--  where it is written, but only that it is readable.
insDeps :: Ident i => [i] -> InterIdentCtx i -> DepGraphM i ()
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
insGlobLocDeps :: Ident i => InterIdentCtx i -> DepGraphM i ()
insGlobLocDeps (_, _, GlobalMode) = return ()
insGlobLocDeps v@(x, u, _) = do
    let vG = (x, u, GlobalMode)
    insVar vG
    insDep vG v

getDepsPattern :: Ident i => Pattern i -> [i]
getDepsPattern (Pattern h e) = (getDeps $ untyped e) \\ (getVarsHead h)
  where
    getVarsHead (EnumPat _) = []
    getVarsHead (ProdPat xs) = xs

getDeps :: Ident i => GExpr i (Constant i) (Atom i) (Expr i) -> [i]
getDeps (AtExpr (AtomVar ident)) = [ident]
getDeps (AtExpr _) = []
getDeps (LogNot e) = getDeps $ untyped e
getDeps (Expr2 _ e1 e2) = (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (Ite c e1 e2) = (getDeps $ untyped c) ++ (getDeps $ untyped e1) ++ (getDeps $ untyped e2)
getDeps (ProdCons (Prod es)) = concat $ map (getDeps . untyped) es
getDeps (Match e pats) = (getDeps $ untyped e) ++ (concat $ map getDepsPattern pats)
getDeps (ArrayCons (Array es)) = concat $ map (getDeps . untyped) es
getDeps (Project x _) = [x]
getDeps (Update x _ e) = x : (getDeps $ untyped e)
