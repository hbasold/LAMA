{-# LANGUAGE TemplateHaskell #-}
module TransformAutomata (trStateEquation) where

import Development.Placeholders

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (fromString)

import Data.Tuple (swap)

import Control.Monad.Trans.Class
import Control.Arrow ((***), (&&&), first, second)

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L

import TransformMonads
import TrEquation
import TransformSimple (trSimpleEquation)

data LocationData = LocationData
                    { stName :: L.SimpIdent
                    , stInitial :: Bool
                    , stFinal :: Bool
                    , stNodes :: [L.Node]
                    , stLocalVars :: [L.Variable]
                    , stStateVars :: [L.Variable] -- [(L.Variable, L.ConstExpr)]
                    , stFlow :: L.Flow
                    } deriving Show

data EdgeData = EdgeData
                { edgeCondition :: L.Expr
                , edgeType :: S.TargetType
                , edgeActions :: Maybe S.Actions
                }

type TrLocation = LNode LocationData
type TrEdge = LEdge EdgeData
type StateGr = Gr LocationData EdgeData

buildStateGraph :: [S.State] -> TrackUsedNodes StateGr
buildStateGraph sts =
  do ls <- extractLocations $ zip [0..] sts
     let nodeMap = Map.fromList $ map (swap . second stName) ls
     es <- lift $ extractEdges nodeMap sts
     return $ mkGraph ls es

extractLocations :: [(Node, S.State)] -> TrackUsedNodes [TrLocation]
extractLocations = mapM extractLocation

extractLocation :: (Node, S.State) -> TrackUsedNodes TrLocation
extractLocation (n, s) =
  do (nodes, localVars, stateVars, flow) <- extractDataDef (S.stateData s)
     return (n, LocationData
                (fromString $ S.stateName s)
                (S.stateInitial s) (S.stateFinal s)
                nodes localVars stateVars flow)

extractEdges :: Map L.SimpIdent Node -> [S.State] -> TransM [TrEdge]
extractEdges = undefined

extractDataDef :: S.DataDef -> TrackUsedNodes ([L.Node], [L.Variable], [L.Variable], L.Flow)
extractDataDef (S.DataDef sigs vars eqs) =
  do eqs' <- mapM trEquation eqs
     return undefined

trEquation :: S.Equation -> TrackUsedNodes (TrEquation TrEqCont)
trEquation = undefined

-- | Returns the generated top level automaton and the nodes generated
-- for the nested state machines.
trStateEquation :: S.StateMachine -> [String] -> Bool -> TrackUsedNodes (TrEquation L.Automaton)
trStateEquation sm ret returnsAll = $notImplemented

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