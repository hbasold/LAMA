{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
module TransformAutomata (trStateEquation) where

import Development.Placeholders

import Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.GenShow ()
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.String (fromString)
import Data.Tuple (swap)
import Data.Foldable (foldlM)
import Data.Monoid
import Data.Maybe (maybeToList)

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad (when, liftM)
import Control.Monad.Trans.Class
import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow ((&&&), (***), first, second)
import Control.Monad.Error (MonadError(..))
import Control.Monad.Reader (MonadReader)

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import VarGen
import TransformMonads
import TrEquation
import TransformCommon
import TransformSimple (trSimpleEquation)

data LocationData = LocationData
                    { stName :: L.SimpIdent
                    , stInitial :: Bool
                    , stFinal :: Bool
                    , stTrEquation :: TrEquation L.Flow
                    } deriving Show

data EdgeData = EdgeData
                { edgeCondition :: L.Expr
                , edgeType :: S.TargetType
                , edgeActions :: Maybe S.Actions
                } deriving Show

type TrLocation = LNode LocationData
type TrEdge = LEdge EdgeData
type StateGr = Gr LocationData EdgeData

-- | FIXME: we ignore restart completely atm!
-- This should be respected in the following way:
-- for a state which has some initialisation from "->" or "last"
-- we generate two copies. One contains for the corresponding flow
-- only the initialisation and the other copy only contains the flow
-- without initialisation. A "restart" transition enters the first copy
-- and a "resume" transition the second. Implicit self transitions are
-- "resume" transitions. For an initial state the initialisation copy
-- is the new initial state.
buildStateGraph :: [S.State] -> TrackUsedNodes (StateGr, L.Flow, L.StateInit)
buildStateGraph sts =
  do extracted <- extractLocations $ zip [0..] sts
     let (locs, defaultFlows) =
           unzip $ map (fst &&& (fst *** id)) extracted
         locs' = putDefaultFlows defaultFlows locs
         nodeMap = Map.fromList $ map (swap . second stName) locs'
     (es, condFlow, condInits) <- lift $ extractEdges nodeMap sts
     return (mkGraph locs' es, condFlow, condInits)
  where
    -- Given a list of flows which should _not_ be put into the given
    -- node, this puts into every other given flow except the excluded.
    putDefaultFlows :: [(Node, L.Flow)] -> [TrLocation] -> [TrLocation]
    putDefaultFlows defaultFlows = map (putDefaultFlow defaultFlows)

    putDefaultFlow defaultFlows (n, locData) =
      let flow = trEqRhs $ stTrEquation locData
          flow' = foldl (\f (n', defFlow) ->
                          if n /= n' then concatFlows f defFlow else f)
                  flow defaultFlows
      in (n, locData { stTrEquation = (stTrEquation locData) { trEqRhs = flow' } })

-- | Extracts all locations from the given states together with a default
-- flow to be placed in every other location.
extractLocations :: [(Node, S.State)] -> TrackUsedNodes [(TrLocation, L.Flow)]
extractLocations = mapM extractLocation

extractLocation :: (Node, S.State) -> TrackUsedNodes (TrLocation, L.Flow)
extractLocation (n, s) =
  do eq <- extractDataDef (S.stateData s)
     let flow = fmap fst eq
         defaultFlow = snd $ trEqRhs eq
     return ((n, LocationData
                (fromString $ S.stateName s)
                (S.stateInitial s) (S.stateFinal s)
                flow),
             defaultFlow)

extractEdges :: Map L.SimpIdent Node -> [S.State] -> TransM ([TrEdge], L.Flow, L.StateInit)
extractEdges nodes sts =
  do strong <- extractEdges' nodes S.stateUnless sts
     weak <- extractEdges' nodes S.stateUntil sts
     ((conds, inits), weak') <- liftM (first unzip) . liftM unzip $ mapM rewriteWeak weak
     let weak'' = concat $ map (strongAfterWeak strong) weak'
     return (strong ++ weak'', L.Flow [] conds, Map.fromList inits)
  where
    extractEdges' :: Map L.SimpIdent Node -> (S.State -> [S.Transition]) -> [S.State] -> TransM [TrEdge]
    extractEdges' nodeMap getter =
      liftM concat
      . foldlM (\es s -> liftM (:es)
                         . mapM (extract nodeMap (fromString $ S.stateName s))
                         $ getter s) []

    extract nodeMap from (S.Transition c act (S.TargetFork forkType to)) =
      do fromNode <- lookupErr ("Unknown state " ++ L.identString from) from nodeMap
         toNode <- lookupErr ("Unknown state " ++ to) (fromString to) nodeMap
         (fromNode, toNode, ) <$> (EdgeData <$> trExpr' c <*> pure forkType <*> pure act)
    extract nodeMap from (S.Transition c act (S.ConditionalFork _ _)) = $notImplemented

    -- Rewrites a weak transition such that the condition
    -- is moved into a state transition and the new condition
    -- just checks the corresponding variable.
    -- This ensures that the condition is checked in the next state.
    rewriteWeak (from, to, eData) =
      do c <- liftM fromString $ newVar "cond"
         let cond = L.StateTransition c $ edgeCondition eData
         return ((cond, (c, L.mkConst $ L.boolConst True)),
                 (from, to, eData { edgeCondition = L.mkAtomVar c }))

    -- Rewrites a weak transition and builds a transitive transition
    -- if there is a strong transition going out of the state into
    -- which the weak transition leads.
    -- s_1   >-- c_1 -->   s_2   -- c_2 -->>   s_3
    -- This means semantically that if at time n c_1 holds, the transition
    -- to s_2 is deferred to time n+1. But if then c_2 holds, the transition
    -- to s_3 is taken without activating s_2. So we build:
    -- s_1  -- pre c_1 and not c_2 -->>  s_2
    --  \                                 / c_2
    --   \-- pre c_1 and c_2 -->> s_3 <<-/
    --
    -- Here >--> stands for a weak and -->> stands for a strong transition
    -- with the annotation of the corresponding condition. pre c_1 should
    -- be initialised with false.
    strongAfterWeak strong (from, to, eData) =
      let followUps = filter (\(h, _, _) -> h == to) strong
          (c', transEdges) = foldr (addEdge $ edgeCondition eData) (edgeCondition eData, []) followUps
      in (from, to, eData { edgeCondition = c' }) : transEdges
      where
        addEdge c1 (_, t, ed@(EdgeData{ edgeCondition = c2 })) (c1', es) =
          (L.mkExpr2 L.And c1' (L.mkLogNot c2),
           (from, t, ed { edgeCondition = L.mkExpr2 L.And c1 c2 } ) : es)

-- | We translate all equations for the current state. If
-- there occurs another automaton, a node containing that
-- automaton is generated. We try to keep the variables
-- here as local as possible. That means we keep variables
-- declared in the states of the subautomaton local to the
-- generated node.
-- Gives back the flow to be placed in the current state and
-- one that has to placed in all other states.
extractDataDef :: S.DataDef -> TrackUsedNodes (TrEquation (L.Flow, L.Flow))
extractDataDef (S.DataDef sigs vars eqs) =
  do (localVars, localsDefault, localsInit) <- lift $ trVarDecls vars
     -- Fixme: we ignore last and default in states for now
     when (not (null localsDefault) || not (null localsInit)) ($notImplemented)
     -- Rename variables because they will be declared at node level and that
     -- may lead to conflicts with variables from other states.
     varNames <- newVarNames localVars
     let varMap = Map.fromList $ zip (map (L.identString . L.varIdent) localVars) (map L.identString varNames)
         localVars' = map (renameVar (varMap !)) localVars
         eqs' = everywhere (mkT $ rename varMap) eqs
     trEqs <- localScope (\sc -> sc { scopeLocals = scopeLocals sc `mappend` (mkVarMap localVars) })
              $ mapM trEquation eqs'
     let trEq = foldlTrEq (\(gf1, sf1) (gf2, sf2) ->
                            (maybe gf1 (concatFlows gf1) gf2,
                             maybe sf1 (concatFlows sf1) sf2))
                (L.Flow [] [], L.Flow [] []) trEqs
         (localVars'', stateVars) = separateVars (trEqInits trEq) localVars'
     return $ trEq { trEqLocalVars = (trEqLocalVars trEq) ++ localVars''
                   , trEqStateVars = (trEqStateVars trEq) ++ stateVars }
  where
    newVarNames :: MonadVarGen m => [L.Variable] -> m [L.SimpIdent]
    newVarNames = mapM (liftM fromString . newVar . L.identString . L.varIdent)

    rename :: Map String String -> S.Expr -> S.Expr
    rename r e@(S.IdExpr (S.Path [x])) = case Map.lookup x r of
      Nothing -> e
      Just x' -> S.IdExpr $ S.Path [x']
    rename _ e = e

    renameVar r v = L.Variable (fromString . r . L.identString $ L.varIdent v) (L.varType v)

-- | Translates an equation inside a state. This may
-- produce a flow to be executed in that state and one
-- that has to be pushed to all other states.
trEquation :: S.Equation -> TrackUsedNodes (TrEquation (Maybe L.Flow, Maybe L.Flow))
trEquation (S.SimpleEquation lhsIds expr) =
  fmap (Just &&& const Nothing) <$> trSimpleEquation lhsIds expr
trEquation (S.AssertEquation S.Assume _name expr) =
  lift $ trExpr' expr >>= \pc -> return $ TrEquation (Nothing, Nothing) [] [] Map.empty [] [pc]
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine name sts) ret returnsAll) =
  do autom <- trStateEquation sts ret returnsAll
     liftM (fmap $ Just *** Just) $ mkSubAutomatonNode name autom
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented

-- | Creates a node which contains the given automaton together with a connecting
-- flow for the current state and a default flow to be placed in all parallel states.
mkSubAutomatonNode :: (MonadReader Environment m, MonadVarGen m, MonadError String m) =>
                      Maybe String -> TrEquation L.Automaton -> m (TrEquation (L.Flow, L.Flow))
mkSubAutomatonNode n eq =
  do name <- case n of
       Nothing -> liftM fromString $ newVar "SubAutomaton"
       Just n' -> return $ fromString n'
     let (deps, written) = getAutomDeps $ trEqRhs eq
     scope <- askScope
     inp <- mkInputs scope deps
     outp <- mkOutputs scope written
     let automNode =
           L.Node inp outp
           (L.Declarations (Map.fromList $ trEqSubAutom eq) (trEqLocalVars eq) (trEqStateVars eq))
           (L.Flow [] []) []
           (Map.singleton 0 $ trEqRhs eq)
           (trEqInits eq)
           (foldl (L.mkExpr2 L.And) (L.constAtExpr $ L.boolConst True) $ trEqPrecond eq)
     (connects, retVar) <- connectNode name inp outp
     return $
       (baseEq (L.Flow connects [], defaultFlow retVar)) {
         trEqLocalVars = maybeToList retVar,
         trEqSubAutom = [(name, automNode)] }
  where
    mkVars :: MonadError String m =>
             Map L.SimpIdent (L.Type L.SimpIdent) -> [L.SimpIdent] -> m [L.Variable]
    mkVars vs = mapM $ \i ->
      lookupErr ("Not in scope: " ++ L.identPretty i) i vs >>= \t ->
      return $ L.Variable i t

    mkInputs sc = mkVars (scopeInputs sc `mappend` scopeLocals sc) . Set.toList
    mkOutputs sc = mkVars (scopeOutputs sc `mappend` scopeLocals sc) . Set.toList

    connectNode :: (MonadError String m, MonadVarGen m) =>
                   L.SimpIdent -> [L.Variable] -> [L.Variable] -> m ([L.InstantDefinition], Maybe L.Variable)
    connectNode nodeName inp outp =
      let params = map (L.mkAtomVar . L.varIdent) inp
          retType = L.mkProductT (map L.varType outp)
      in do mkLocalAssigns (map L.varIdent outp) (Right (nodeName, params, retType))

    defaultFlow :: Maybe L.Variable -> L.Flow
    defaultFlow Nothing = L.Flow [] []
    defaultFlow (Just v) = L.Flow [L.InstantExpr (L.varIdent v) (defaultValue $ L.varType v)] []

defaultValue :: L.Type L.SimpIdent -> L.Expr
defaultValue (L.GroundType L.BoolT) = L.constAtExpr $ L.boolConst False
defaultValue (L.GroundType L.IntT) = L.constAtExpr $ L.mkIntConst 0
defaultValue (L.GroundType L.RealT) = L.constAtExpr $ L.mkRealConst 1
defaultValue (L.GroundType (L.SInt n)) = L.constAtExpr . L.Fix $ L.SIntConst n 0
defaultValue (L.GroundType (L.UInt n)) = L.constAtExpr . L.Fix $ L.UIntConst n 0
defaultValue (L.EnumType _) = error "no default value for enums available atm"
defaultValue (L.ProdType ts) = L.Fix . L.ProdCons . L.Prod $ map defaultValue ts
       
-- | FIXME: make Natural an instance of Typeable, Data and
-- with that everything in LAMA. Next generalise Expr to
-- a view and with that be able to generalise getDeps and
-- use everything from syb.
--
-- Gives back the used inputs and the written outputs.
getAutomDeps :: L.Automaton -> (Set L.SimpIdent, Set L.SimpIdent)
getAutomDeps a =
  let (locInp, locOutp) = (mconcat *** mconcat) . unzip . map getLocDeps $ L.automLocations a
      edgeDeps = mconcat . map getEdgeDeps $ L.automEdges a
  in (locInp `mappend` edgeDeps, locOutp)
  where
    getLocDeps :: L.Location -> (Set L.SimpIdent, Set L.SimpIdent)
    getLocDeps (L.Location _ flow) = getFlowDeps flow
    getEdgeDeps (L.Edge _ _ cond) = getDeps $ L.unfix cond
    getFlowDeps (L.Flow defs trans) =
      let (i1, o1) = unzip $ map getInstDefDeps defs
          (i2, o2) = unzip $ map getTransDeps trans
      in (mconcat *** mconcat) $ (i1 ++ i2, o1 ++ o2)
    getInstDefDeps (L.InstantExpr x e) = (getDeps $ L.unfix e, Set.singleton x)
    getInstDefDeps (L.NodeUsage x _ es) = (mconcat $ map (getDeps . L.unfix) es, Set.singleton x)
    getTransDeps (L.StateTransition x e) = (getDeps $ L.unfix e, Set.singleton x)

    getDeps :: L.GExpr L.SimpIdent L.Constant L.Atom L.Expr -> Set L.SimpIdent
    getDeps (L.AtExpr (L.AtomVar ident)) = Set.singleton ident
    getDeps (L.AtExpr _) = Set.empty
    getDeps (L.LogNot e) = getDeps $ L.unfix e
    getDeps (L.Expr2 _ e1 e2) = (getDeps $ L.unfix e1) `mappend` (getDeps $ L.unfix e2)
    getDeps (L.Ite c e1 e2) = (getDeps $ L.unfix c) `mappend` (getDeps $ L.unfix e1) `mappend` (getDeps $ L.unfix e2)
    getDeps (L.ProdCons (L.Prod es)) = mconcat $ map (getDeps . L.unfix) es
    getDeps (L.Match e pats) = (getDeps $ L.unfix e) `mappend` (mconcat $ map getDepsPattern pats)
    getDeps (L.Project x _) = Set.singleton x

    getDepsPattern :: L.Pattern -> Set L.SimpIdent
    getDepsPattern (L.Pattern _ e) = (getDeps $ L.unfix e)

-- | Returns the generated top level automaton and the nodes generated
-- for the nested state machines.
-- FIXME: we have to write all variables which have been written in one state in all other states.
--        There are generally two kinds: local variables and state variables. The first ones are
--        declared in a Scade state but have to be pulled out so now they have to get assigned some
--        arbitrary value in every other state. The second kind are variables which are
--        used in a "last 'x" construct. They are specified by a default behaviour (possibly
--        given by the user).
-- FIXME: support pre/last
trStateEquation :: [S.State] -> [String] -> Bool -> TrackUsedNodes (TrEquation L.Automaton)
trStateEquation sts ret returnsAll =
  do (stGr, condFlow, condInits) <- buildStateGraph sts
     mkAutomaton stGr

mkAutomaton :: MonadError String m => StateGr -> m (TrEquation L.Automaton)
mkAutomaton gr =
  let ns = labNodes gr
      (locs, inits, eq) =
        foldr (\l (ls, i, eq') ->
                let (l', i', eq'') = mkLocation l
                in (l':ls, i `mappend` (First i'), mergeEq eq' eq''))
        ([], First Nothing, baseEq ()) ns
      grEdges = labEdges gr
      automEdges = map (mkEdge gr) grEdges
  in case getFirst inits of
    Nothing -> throwError "No initial state given"
    Just i -> let autom = L.Automaton locs i automEdges
              in return $ eq { trEqRhs = autom }
  where
    mkLocation :: TrLocation -> (L.Location, Maybe L.SimpIdent, TrEquation ())
    mkLocation (_, locData) =
      (L.Location (stName locData) (trEqRhs $ stTrEquation locData),
       if stInitial locData then Just $ stName locData else Nothing,
       mergeEq (baseEq ()) (fmap (const ()) $ stTrEquation locData))

    mergeEq :: TrEquation () -> TrEquation () -> TrEquation ()
    mergeEq e1 e2 = foldlTrEq (const $ const ()) () [e1, e2]

    mkEdge :: StateGr -> LEdge EdgeData -> L.Edge
    mkEdge gr (h, t, EdgeData { edgeCondition = cond
                              , edgeType = eType
                              , edgeActions = actions }) =
      let (Just LocationData { stName = hName }) = lab gr h
          (Just LocationData { stName = tName }) = lab gr t
      in L.Edge hName tName cond