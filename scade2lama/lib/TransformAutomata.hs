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
import Data.String (fromString)
import Data.Tuple (swap)
import Data.Foldable (foldlM)
import Data.Monoid

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad (when, liftM)
import Control.Monad.Trans.Class
import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow (first, second)
import Control.Monad.Error (MonadError(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L

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
  do ls <- extractLocations $ zip [0..] sts
     let nodeMap = Map.fromList $ map (swap . second stName) ls
     (es, condFlow, condInits) <- lift $ extractEdges nodeMap sts
     return (mkGraph ls es, condFlow, condInits)

extractLocations :: [(Node, S.State)] -> TrackUsedNodes [TrLocation]
extractLocations = mapM extractLocation

extractLocation :: (Node, S.State) -> TrackUsedNodes TrLocation
extractLocation (n, s) =
  do flow <- extractDataDef (S.stateData s)
     return (n, LocationData
                (fromString $ S.stateName s)
                (S.stateInitial s) (S.stateFinal s)
                flow)

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
      ((nodeMap ! from), (nodeMap ! (fromString to)), )
      <$> (EdgeData <$> trExpr' c <*> pure forkType <*> pure act )
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
extractDataDef :: S.DataDef -> TrackUsedNodes (TrEquation L.Flow)
extractDataDef (S.DataDef sigs vars eqs) =
  do (localVars, localsDefault, localsInit) <- lift $ trVarDecls vars
     -- Fixme: we ignore last and default in states for now
     when (not (null localsDefault) || not (null localsInit)) ($notImplemented)
     -- Rename variables because they will be declared at node level and that
     -- may lead to conflicts with variables from other states.
     varNames <- newVarNames localVars
     let varMap = Map.fromList $ zip (map (L.identString . L.varIdent) localVars) (map L.identString varNames)
         localVars' = map (renameVar (varMap !)) localVars
         eqs' = everywhere (mkT $ rename (varMap !)) eqs
     trEqs <- mapM trEquation eqs'
     let trEq = foldlTrEq (\f1 -> maybe f1 (concatFlows f1)) (L.Flow [] []) trEqs
         (localVars'', stateVars) = separateVars (trEqInits trEq) localVars
     return $ trEq { trEqLocalVars = (trEqLocalVars trEq) ++ localVars''
                   , trEqStateVars = (trEqStateVars trEq) ++ stateVars }
  where
    newVarNames :: MonadVarGen m => [L.Variable] -> m [L.SimpIdent]
    newVarNames = mapM (liftM fromString . newVar . L.identString . L.varIdent)

    rename :: (String -> String) -> S.Expr -> S.Expr
    rename r e@(S.IdExpr (S.Path [x])) = S.IdExpr $ S.Path [r x]
    rename _ e = e

    renameVar r v = L.Variable (fromString . r . L.identString $ L.varIdent v) (L.varType v)

trEquation :: S.Equation -> TrackUsedNodes (TrEquation (Maybe L.Flow))
trEquation (S.SimpleEquation lhsIds expr) =
  fmap Just <$> trSimpleEquation lhsIds expr
trEquation (S.AssertEquation S.Assume _name expr) =
  lift $ trExpr' expr >>= \pc -> return $ TrEquation Nothing [] [] Map.empty [] [pc]
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine name sts) ret returnsAll) = $notImplemented
--  do autom <- trStateEquation sts ret returnsAll
--     let node = mkSubAutomatonNode name autom
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented

{-
mkSubAutomatonNode :: MonadVarGen m => Maybe String -> TrEquation L.Automaton -> m (TrEquation TrEqCont)
mkSubAutomatonNode n eq =
  do name <- case n of
       Nothing -> liftM fromString $ newVar "SubAutomaton"
       Just n' -> fromString n'
     let readDeps = everything (++) (mkQ [] getDeps) $ trEqRhs eq
     return undefined
-- Fixme: create flow which uses this node.
-}

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
      (locs, init, eq) = foldr (\l (ls, i, eq') ->
                                 let (l', i', eq'') = mkLocation l
                                 in (l':ls, i `mappend` (First i'), mergeEq eq' eq''))
                         ([], First Nothing, baseEq ()) ns
      es = labEdges gr
  in case getFirst init of
    Nothing -> throwError "No initial state given"
    Just i -> let autom = undefined
              in return $ eq { trEqRhs = autom }
  where
    mkLocation :: TrLocation -> (L.Location, Maybe L.SimpIdent, TrEquation ())
    mkLocation (_, locData) =
      (L.Location (stName locData) (trEqRhs $ stTrEquation locData),
       if stInitial locData then Just $ stName locData else Nothing,
       mergeEq (baseEq ()) (fmap (const ()) $ stTrEquation locData))

    mergeEq :: TrEquation () -> TrEquation () -> TrEquation ()
    mergeEq e1 e2 = foldlTrEq (const $ const ()) () [e1, e2]

-- trStateMachine :: S.StateMachine -> a

{-

trStateMachine :: S.StateMachine -> TrackUsedNodes L.Automaton
trStateMachine (S.StateMachine _name states) =
  do let stateMap = mkStateMap $ states
     (locations, assignedVars) <- extractLocs $ states
     (edges, condFlow, condInits) <- extractEdges stateMap $ states
     initial <- extractInitial $ states
     return $ L.Automaton (writeAllVars locations assignedVars) initial edges
  where
    mkStateMap = Map.fromList . fmap (S.stateName &&& id)

-- | Extract locations together with their data flow and returns a set of
-- variables that are accessed using the last construct 
extractLocs :: [S.State] -> TrackUsedNodes ([L.Location], [(L.SimpIdent, L.Expr)])
extractLocs = undefined

extractInitial :: [S.State] -> TrackUsedNodes L.LocationId
extractInitial sts = case find S.stateInitial sts of
  Nothing -> throwError $ "You want your state machine to start somewhere, right? Give an initial state"
  Just s -> return . fromString $ S.stateName s

-- | FIXME: we ignore restart completely atm!
extractEdges :: Map String S.State -> [S.State] -> TrackUsedNodes ([L.Edge], L.Flow, L.StateInit)
extractEdges stateMap sts =
  do strong <- extractEdges' S.stateUnless sts
     weak <- extractEdges' S.stateUntil sts
     ((conds, inits), weak') <- liftM (first unzip) . liftM unzip $ mapM rewriteWeak weak
     let weak'' = concat $ map (strongAfterWeak strong) weak'
     return (strong ++ weak'', L.Flow [] conds, Map.fromList inits)
  where
    extractEdges' :: (S.State -> [S.Transition]) -> [S.State] -> TrackUsedNodes [L.Edge]
    extractEdges' getter =
      liftM concat
      . foldlM (\es s -> liftM (:es)
                         . mapM (extract (fromString $ S.stateName s))
                         $ getter s) []

    -- FIXME: here is restart ignored (forkType)
    extract from (S.Transition c Nothing (S.TargetFork forkType to)) =
      L.Edge from (fromString to) <$> trExpr' c
    extract from _ = $notImplemented

    -- Rewrites a weak transition such that the condition
    -- is moved into a state transition and the new condition
    -- just checks the corresponding variable.
    -- This ensures that the condition is checked in the next state.
    rewriteWeak (L.Edge from to ce) =
      do c <- liftM fromString $ newVar "cond"
         let cond = L.StateTransition c ce
         return ((cond, (c, L.mkConst $ L.boolConst True)),
                 L.Edge from to $ L.mkAtomVar c)

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
    strongAfterWeak strong (L.Edge from to c1) =
      let followUps = filter (\e@(L.Edge h _  _) -> h == to) strong
          (c1', transEdges) = foldr addEdge (c1, []) followUps
      in (L.Edge from to c1') : transEdges
      where
        addEdge (L.Edge _ t c2) (c1'', es) =
          (L.mkExpr2 L.And c1'' (L.mkLogNot c2),
           L.Edge from t (L.mkExpr2 L.And c1 c2) : es)

-- | Defines all variables by 
writeAllVars :: [L.Location] -> [L.SimpIdent] -> [L.Location]
writeAllVars = undefined

-}