{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
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
import Data.Set (Set, (\\))
import Data.String (fromString)
import Data.Tuple (swap)
import Data.Foldable (foldlM)
import Data.Traversable (mapAccumL)
import Data.Monoid
import Data.Maybe (maybeToList, catMaybes)
import Data.List (partition, unzip4)

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad (when, liftM)
import Control.Monad.Trans.Class
import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow ((&&&), (***), second)
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
                    { stName :: L.LocationId
                    , stInitial :: Bool
                    , stFinal :: Bool
                    , stTrEquation :: TrEquation L.Flow
                    } deriving Show

data EdgeType = Weak | Strong deriving (Eq, Ord, Show)

data EdgeData = EdgeData
                { edgeCondition :: L.Expr
                , edgeType :: EdgeType
                , edgeTargetType :: S.TargetType
                , edgeActions :: Maybe S.Actions
                } deriving Show

mapCondition :: (L.Expr -> L.Expr) -> EdgeData -> EdgeData
mapCondition f ed = ed { edgeCondition = f $ edgeCondition ed }

type TrLocation = LNode LocationData
type TrEdge = LEdge EdgeData
type StateContext = Context LocationData EdgeData
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
buildStateGraph :: [S.State] -> TrackUsedNodes (StateGr, Map L.SimpIdent L.Expr, L.Flow)
buildStateGraph sts =
  do (locs, (defaultFlows, globalFlow)) <- extractLocations $ zip [0..] sts
     let nodeMap = Map.fromList $ map (swap . second stName) locs
     es <- lift $ extractEdges nodeMap sts
     return (mkGraph locs es, defaultFlows, globalFlow)

-- | Extracts all locations from the given states together with a default
-- flow and a flow which has to placed in the surrounding scope.
extractLocations :: [(Node, S.State)] -> TrackUsedNodes ([TrLocation], (Map L.SimpIdent L.Expr, L.Flow))
extractLocations = liftM (second ((mconcat *** mconcat) . unzip) . unzip) . mapM extractLocation

extractLocation :: (Node, S.State) -> TrackUsedNodes (TrLocation, (Map L.SimpIdent L.Expr, L.Flow))
extractLocation (n, S.State{..}) =
  do eq <- extractDataDef stateData
     let flow = fmap fst eq
         (defaultFlow, surroundingFlow) = snd $ trEqRhs eq
     return ((n, LocationData
                (fromString stateName)
                stateInitial stateFinal
                flow),
             (defaultFlow, surroundingFlow))

-- | Extracts the edges from a given set of Scade states. This may result in
-- an additional data flow to be placed outside of the automaton which
-- calculates the conditions for weak transitions.
extractEdges :: Map L.LocationId Node -> [S.State] -> TransM [TrEdge]
extractEdges stateNodeMap sts =
  do strong <- extractEdges' stateNodeMap S.stateUnless Strong sts
     weak <- extractEdges' stateNodeMap S.stateUntil Weak sts
     return $ strong ++ weak
  where
    extractEdges' :: Map L.LocationId Node -> (S.State -> [S.Transition]) -> EdgeType -> [S.State] -> TransM [TrEdge]
    extractEdges' nodeMap getter eType =
      liftM concat
      . foldlM (\es s -> liftM (:es)
                         . mapM (extract nodeMap eType (fromString $ S.stateName s))
                         $ getter s) []

    extract nodeMap eType from (S.Transition c act (S.TargetFork forkType to)) =
      do fromNode <- lookupErr ("Unknown state " ++ L.identString from) from nodeMap
         toNode <- lookupErr ("Unknown state " ++ to) (fromString to) nodeMap
         (fromNode, toNode, ) <$> (EdgeData <$> trExpr' c <*> pure eType <*> pure forkType <*> pure act)
    extract nodeMap eType from (S.Transition c act (S.ConditionalFork _ _)) = $notImplemented

-- | We translate all equations for the current state. If
-- there occurs another automaton, a node containing that
-- automaton is generated. We try to keep the variables
-- here as local as possible. That means we keep variables
-- declared in the states of the subautomaton local to the
-- generated node.
-- Gives back the flow to be placed in the current state and
-- default expressions.
extractDataDef :: S.DataDef -> TrackUsedNodes (TrEquation (L.Flow, (Map L.SimpIdent L.Expr, L.Flow)))
extractDataDef S.DataDef { S.dataSignals, S.dataLocals, S.dataEquations } =
  do (localVars, localsDefault, localsInit) <- lift $ trVarDecls dataLocals
     -- Fixme: we ignore last and default in states for now
     when (not (null localsDefault) || not (null localsInit)) ($notImplemented)
     -- Rename variables because they will be declared at node level and that
     -- may lead to conflicts with variables from other states.
     varNames <- newVarNames localVars
     let varMap = Map.fromList $ zip (map (L.identString . L.varIdent) localVars) (map L.identString varNames)
         localVars' = map (renameVar (varMap !)) localVars
         eqs' = everywhere (mkT $ rename varMap) dataEquations
     trEqs <- localScope (\sc -> sc { scopeLocals = scopeLocals sc `mappend` (mkVarMap localVars) })
              $ mapM trEquation eqs'
     let trEq = foldlTrEq (\(stateFlow, (default1, globalFlow)) (stateFlow2, (default2, globalFlow2)) ->
                            (maybe stateFlow (mappend stateFlow) stateFlow2,
                             (default1 `mappend` default2,
                              maybe globalFlow (mappend globalFlow) globalFlow2)))
                (mempty, (Map.empty, mempty)) trEqs
         (localVars'', stateVars) = separateVars (trEqAsState trEq) localVars'
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
-- produce a flow to be executed in that state,
-- a set of default values and a flow which has to
-- be put in the surrounding scope.
trEquation :: S.Equation -> TrackUsedNodes (TrEquation (Maybe L.Flow, (Map L.SimpIdent L.Expr, Maybe L.Flow)))
trEquation (S.SimpleEquation lhsIds expr) =
  do let validLhsIds = getValidIds lhsIds

     lhsDefaults <- getDefaults validLhsIds
     let hasDefault = Map.keysSet lhsDefaults
     (lastExprs, lastStateVars, lastStateTrans, lastStateInits) <- getLasts hasDefault validLhsIds

     -- Translate the equation
     eq <- trSimpleEquation lhsIds expr

     -- Put everything into the equation
     let lhsDefaults' = lhsDefaults `mappend` lastExprs
     let eq' = eq { trEqStateVars = trEqStateVars eq ++ lastStateVars
                  , trEqInits = trEqInits eq `mappend` lastStateInits }
         eq'' = fmap (\(Left x) -> x) eq' -- FIXME: generate initialisation states
     return $ fmap (Just &&& const (lhsDefaults', Just $ L.Flow [] lastStateTrans)) eq''
  where
    getValidIds = foldr (\x xs -> case x of
                            S.Named x' -> (fromString x') : xs
                            S.Bottom -> xs) []

trEquation (S.AssertEquation S.Assume _name expr) =
  lift $ trExpr' expr >>= \pc -> return $ (baseEq $ (Nothing, (Map.empty, Nothing))) { trEqPrecond = [pc] }
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine name sts) ret returnsAll) =
  do autom <- trStateEquation sts ret returnsAll
     liftM (fmap $ Just *** (id &&& const Nothing)) $ mkSubAutomatonNode name autom
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented

-- | Get default equations for all variables on the lhs
-- if they are available
getDefaults :: MonadReader Environment m => [L.SimpIdent] -> m (Map L.SimpIdent L.Expr)
getDefaults xs =
  do defaultExprs <- liftM scopeDefaults $ askScope
     return
       . Map.fromList
       . catMaybes
       . map (\x -> fmap (x,) $ Map.lookup x defaultExprs)
       $ xs

-- | Get last expressions for the variables on the lhs
-- if they are available and are not shadowe by a default
-- expression.
getLasts :: (MonadReader Environment m, MonadVarGen m, MonadError String m) =>
            Set L.SimpIdent -> [L.SimpIdent]
            -> m (Map L.SimpIdent L.Expr, [L.Variable], [L.StateTransition], Map L.SimpIdent L.ConstExpr)
getLasts hasDefault xs =
  do lastInitExprs <- liftM scopeLastInits $ askScope
     let canHaveLast = filter (not . (flip Set.member hasDefault)) xs
         lhsLastInitExprs = catMaybes
                            . map (\x -> fmap (x,) $ Map.lookup x lastInitExprs)
                            $ canHaveLast
     liftM (\(defs, vs, trans, inits) -> (Map.fromList defs, vs, trans, Map.fromList inits))
       . liftM unzip4
       $ mapM mkLast lhsLastInitExprs
  where
    -- Creates a variable and a flow which transports the value of
    -- a given variable x to the next cycle. This is then used to
    -- generate a default expression which represents the semantics of
    -- partially defined variables.
    mkLast :: (MonadReader Environment m, MonadVarGen m, MonadError String m) =>
              (L.SimpIdent, Either L.ConstExpr L.Expr)
              -> m ((L.SimpIdent, L.Expr), L.Variable, L.StateTransition, (L.SimpIdent, L.ConstExpr))
    mkLast (x, initExpr) =
      do x_1 <- liftM fromString . newVar . (++ "_last") $ L.identString x
         t <- lookupWritable x
         let x_1Var = L.Variable x_1 t
             trans = L.StateTransition x_1 $ L.mkAtomVar x
         initConst <- case initExpr of
           Left c -> return c
           Right _ -> throwError $ "Non constant last currently non supported"
         let transInit = (x_1, initConst)
         return ((x, L.mkAtomVar x_1), x_1Var, trans, transInit)

-- | Creates a node which contains the given automaton together with a connecting
-- flow for the current state and default expressions.
mkSubAutomatonNode :: (MonadReader Environment m, MonadVarGen m, MonadError String m) =>
                      Maybe String -> TrEquation (L.Automaton, L.Flow) -> m (TrEquation (L.Flow, Map L.SimpIdent L.Expr))
mkSubAutomatonNode n eq =
  do name <- case n of
       Nothing -> liftM fromString $ newVar "SubAutomaton"
       Just n' -> return $ fromString n'
     let (autom, condFlow) = trEqRhs eq
         (automDeps, automWritten) = getAutomDeps autom
         (condDeps, _condWritten) = getFlowDeps condFlow
         localVars = trEqLocalVars eq
         stateVars = trEqStateVars eq
         nodeInternal = Set.fromList . map L.varIdent $ localVars ++ stateVars
         deps = (automDeps `mappend` condDeps) \\ nodeInternal
         written = automWritten \\ nodeInternal
     scope <- askScope
     inp <- mkInputs scope deps
     outp <- mkOutputs scope written
     let automNode =
           L.Node
           (L.Declarations (Map.fromList $ trEqSubAutom eq) inp localVars stateVars)
           outp
           condFlow
           (Map.singleton 0 autom)
           (trEqInits eq)
           (foldl (L.mkExpr2 L.And) (L.constAtExpr $ L.boolConst True) $ trEqPrecond eq)
     (connects, retVar) <- connectNode name inp outp

     -- consider defaults and lasts for the written variables of the
     -- subautomaton.
     outpDefaults <- getDefaults $ Set.toList written
     let hasDefault = Map.keysSet outpDefaults
     (lastExprs, lastStateVars, lastStateTrans, lastStateInits) <- getLasts hasDefault $ Set.toList written
     let outpDefaults' = outpDefaults `mappend` lastExprs

     return $
       (baseEq (L.Flow connects lastStateTrans, defaultExpr retVar `mappend` outpDefaults')) {
         trEqLocalVars = maybeToList retVar,
         trEqStateVars = lastStateVars,
         trEqInits = lastStateInits,
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
      in do mkLocalAssigns (map (Just . L.varIdent) outp) (Right (nodeName, params, retType))

    defaultExpr :: Maybe L.Variable -> Map L.SimpIdent L.Expr
    defaultExpr Nothing = Map.empty
    defaultExpr (Just v) = Map.singleton (L.varIdent v) (defaultValue $ L.varType v)

defaultValue :: L.Type L.SimpIdent -> L.Expr
defaultValue (L.GroundType L.BoolT) = L.constAtExpr $ L.boolConst False
defaultValue (L.GroundType L.IntT) = L.constAtExpr $ L.mkIntConst 0
defaultValue (L.GroundType L.RealT) = L.constAtExpr $ L.mkRealConst 1
defaultValue (L.GroundType (L.SInt n)) = L.constAtExpr . L.Fix $ L.SIntConst n 0
defaultValue (L.GroundType (L.UInt n)) = L.constAtExpr . L.Fix $ L.UIntConst n 0
defaultValue (L.EnumType _) = error "no default value for enums available atm"
defaultValue (L.ProdType ts) = L.Fix . L.ProdCons . L.Prod $ map defaultValue ts
       
-- | TODO: make Natural an instance of Typeable, Data and
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

getFlowDeps :: L.Flow -> (Set L.SimpIdent, Set L.SimpIdent)
getFlowDeps (L.Flow defs trans) =
  let (i1, o1) = unzip $ map getInstDefDeps defs
      (i2, o2) = unzip $ map getTransDeps trans
  in (mconcat *** mconcat) $ (i1 ++ i2, o1 ++ o2)
  where
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
  where
    getDepsPattern :: L.Pattern -> Set L.SimpIdent
    getDepsPattern (L.Pattern _ body) = (getDeps $ L.unfix body)
getDeps (L.Project x _) = Set.singleton x

-- | Returns the generated top level automaton and the nodes generated
-- for the nested state machines.
-- FIXME: we have to write all variables which have been written in one state in all other states.
--        There are generally two kinds: local variables and state variables. The first ones are
--        declared in a Scade state but have to be pulled out so now they have to get assigned some
--        arbitrary value in every other state. The second kind are variables which are
--        used in a "last 'x" construct. They are specified by a default behaviour (possibly
--        given by the user).
-- FIXME: support pre/last
trStateEquation :: [S.State] -> [String] -> Bool -> TrackUsedNodes (TrEquation (L.Automaton, L.Flow))
trStateEquation sts ret returnsAll =
  do (stGr, defaultExprs1, globalFlow) <- buildStateGraph sts
     (stGr', condFlow, defaultExprs2) <- rewriteWeak stGr
     let stGr'' = strongAfterWeak stGr'
     autom <- mkAutomaton stGr'' (defaultExprs1 `mappend` defaultExprs2)
     return $ fmap (,globalFlow `mappend` condFlow) autom

-- | Rewrites a weak transition such that the condition
-- is moved into a state transition and the new condition
-- just checks the corresponding variable.
-- This ensures that the condition is checked in the next state.
rewriteWeak :: MonadVarGen m => StateGr
               -> m (StateGr, L.Flow, Map L.SimpIdent L.Expr)
rewriteWeak = (uncurry $ foldlM go)
              . ((, mempty, Map.empty) &&& Gr.nodes)
  where
    go (gr, L.Flow [] ts, defaultExprs) currNode =
      do let (Just c, gr') = Gr.match currNode gr
         (c', ts', defaultExprs') <- rewriteWeaks c
         return (c' & gr', L.Flow [] (ts' ++ ts),
                 defaultExprs `mappend` defaultExprs')
    go (_, L.Flow _ _, _) _ = error "produced unexpectedly non-state flow"

    rewriteWeaks :: MonadVarGen m => StateContext
                    -> m (StateContext, [L.StateTransition], Map L.SimpIdent L.Expr)
    rewriteWeaks c@(predSts, st, stData, succSts) =
      let (weakSucc, strongSucc) = partition (\(eData, _) -> edgeType eData == Weak) succSts
          strongPred = filter (\(eData, _) -> edgeType eData == Strong) predSts
      in case weakSucc of
        [] -> return (c, [], Map.empty)
        _ -> do (activateWeak, stData', stateTrans, defaultExprs) <- createWeakActivation st stData strongPred
                (weakSucc', conds, condVars, inits) <- liftM unzip4 $ mapM (rewriteWeak' activateWeak) weakSucc
                let trEq'  = stTrEquation stData'
                    trEq'' = trEq' { trEqStateVars = trEqStateVars trEq' ++ condVars
                                   , trEqInits = trEqInits trEq' `mappend` (mconcat inits)
                                   }
                    stData'' = stData' { stTrEquation = trEq'' }
                    succSts' = weakSucc' ++ strongSucc
                return ((predSts, st, stData'', succSts'),
                        stateTrans ++ conds, defaultExprs)

    -- Creates a condition to activate weak transitions of a given state.
    -- This may lead to the creation of a variable that is true iff
    -- the state is active. The corresponding data flow is integrated
    -- into the state but defaults and state transitions for this variable
    -- are also created and given back.
    createWeakActivation st stData strongPred =
      case strongPred of
        [] -> return (L.constAtExpr $ L.boolConst True, stData, [], Map.empty)
        _ -> do let stN = L.identString $ stName stData
                inSt <- liftM fromString . newVar $ "inState" ++ stN -- true if st is currently active
                wasSt <- liftM fromString . newVar $ "wasState" ++ stN-- true if st was active in last cycle
                let entryCond = mkEntryCond st wasSt strongPred
                    inStFlow = L.Flow [L.InstantExpr inSt $ L.constAtExpr $ L.boolConst True] []
                    wasStEq = L.StateTransition wasSt $ L.mkAtomVar inSt
                    trEq = stTrEquation stData
                    trEq' = trEq { trEqRhs = (trEqRhs trEq) `mappend` inStFlow
                                 , trEqLocalVars = trEqLocalVars trEq ++ [L.Variable inSt L.boolT]
                                 , trEqStateVars = trEqStateVars trEq ++ [L.Variable wasSt L.boolT]
                                 , trEqInits = trEqInits trEq
                                               `mappend` Map.singleton wasSt (L.mkConst . L.boolConst $ stInitial stData)
                                 }
                    stData' = stData { stTrEquation = trEq' }
                return (entryCond, stData', [wasStEq],
                        Map.singleton inSt (L.constAtExpr $ L.boolConst False))

    -- Creates a condition which is true if a state has not been
    -- entered this cycle through a strong transition.
    -- That means that weak transitions going out of this state
    -- can be taken.
    mkEntryCond :: Node -> L.SimpIdent -> Adj EdgeData -> L.Expr
    mkEntryCond st wasSt strongPred =
      let (incoming, selfTrans) = partition (\(_, st') -> st' /= st) strongPred -- filter out self transitions
          -- if any condition on an incoming transition is true
          -- the system must already have been in /st/.
          incomingTaken = case incoming of
            [] -> L.constAtExpr $ L.boolConst True
            _ -> let oneStrongActive =
                       foldl1 (L.mkExpr2 L.Or)
                       . map (edgeCondition . fst)
                       $ incoming
                 in L.mkExpr2 L.Implies oneStrongActive (L.mkAtomVar wasSt)

          -- if any condition on a self transition is true
          -- then the last state must not be /st/
          selfTransTaken = case selfTrans of
            [] -> L.constAtExpr $ L.boolConst True
            _ -> let oneStrongActive =
                       foldl1 (L.mkExpr2 L.Or)
                       . map (edgeCondition . fst)
                       $ selfTrans
                 in L.mkExpr2 L.Implies oneStrongActive $ L.mkLogNot (L.mkAtomVar wasSt)

      in L.mkExpr2 L.And incomingTaken selfTransTaken

    rewriteWeak' activateWeak (eData, to) =
      do c <- liftM fromString $ newVar "cond"
         let cond = L.StateTransition c $ L.mkExpr2 L.And (edgeCondition eData) activateWeak
         return ((eData { edgeCondition = L.mkAtomVar c }, to),
                 cond, L.Variable c L.boolT, Map.singleton c (L.mkConst $ L.boolConst False))

-- | Builds a transitive transition
-- if there is a strong transition going out of the state into
-- which a weak transition leads.
-- s_1   -- c_1 -->o   s_2   o-- c_2 -->   s_3
-- This means semantically that if at time n c_1 holds, the transition
-- to s_2 is deferred to time n+1. But if then c_2 holds, the transition
-- to s_3 is taken without activating s_2. So we build:
-- s_1  o-- pre c_1 and not c_2  -->  s_2
--  o                                  o
--   \                                / c_2
--    \-- pre c_1 and c_2 --> s_3 <--/
--
-- Here -->o stands for a weak and o--> stands for a strong transition
-- with the annotation of the corresponding condition. pre c_1 should
-- be initialised with false.
-- Notice that we don't rewrite the transition condition as we expect
-- that to be done in /rewriteWeak/.
strongAfterWeak :: StateGr -> StateGr
strongAfterWeak =
  (uncurry Gr.insEdges) . (uncurry $ foldl go) . (([], ) &&& Gr.nodes)
  where
    go :: ([TrEdge], StateGr) -> Node -> ([TrEdge], StateGr)
    go (es, gr) currNode =
      let (Just c, gr') = Gr.match currNode gr
          (c', es') = strongAfterWeak' c
      in (es' ++ es, c' & gr')

    strongAfterWeak' :: StateContext -> (StateContext, [TrEdge])
    strongAfterWeak' (predSts, s2, stData, succSts) =
      let (weakIns, strongIns) = partition (\(eData, _) -> edgeType eData == Weak) predSts
          strongOuts = filter (\(eData, _) -> edgeType eData == Strong) succSts
          (transEdges, weakIns') = mapAccumL (mkTransEdges strongOuts) [] weakIns
      in ((weakIns' ++ strongIns, s2, stData, succSts), transEdges)

    -- we are in node s2
    mkTransEdges strongOuts transEdges (weakInData, s3) =
      let weakInCond = edgeCondition weakInData
          oneStrongActive = foldl1 (L.mkExpr2 L.Or) . map (edgeCondition . fst) $ strongOuts
          weakInCond' = L.mkExpr2 L.And weakInCond (L.mkLogNot oneStrongActive)
          transEdges' = map (\(ed, s1) -> (s1, s3, mapCondition (L.mkExpr2 L.And weakInCond) ed)) strongOuts
      in (transEdges ++ transEdges', (weakInData { edgeCondition = weakInCond' }, s3))

-- | Builds an automaton out of the given state graph.
-- FIXME: respect priorities
mkAutomaton :: MonadError String m => StateGr -> Map L.SimpIdent L.Expr -> m (TrEquation L.Automaton)
mkAutomaton gr defaultExprs =
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
    Just i -> let autom = L.Automaton locs i automEdges defaultExprs
              in return $ eq { trEqRhs = autom }
  where
    mkLocation :: TrLocation -> (L.Location, Maybe L.LocationId, TrEquation ())
    mkLocation (_, locData) =
      (L.Location (stName locData) (trEqRhs $ stTrEquation locData),
       if stInitial locData then Just $ stName locData else Nothing,
       mergeEq (baseEq ()) (fmap (const ()) $ stTrEquation locData))

    mergeEq :: TrEquation () -> TrEquation () -> TrEquation ()
    mergeEq e1 e2 = foldlTrEq (const $ const ()) () [e1, e2]

    mkEdge :: StateGr -> LEdge EdgeData -> L.Edge
    mkEdge g (h, t, EdgeData { edgeCondition = cond
                              , edgeActions = actions }) =
      let (Just LocationData { stName = hName }) = lab g h
          (Just LocationData { stName = tName }) = lab g t
      in case actions of
        Nothing -> L.Edge hName tName cond
        Just acts -> case acts of
          S.ActionEmission [] -> L.Edge hName tName cond
          S.ActionEmission _ -> $notImplemented
          S.ActionDef (S.DataDef [] [] []) -> L.Edge hName tName cond
          S.ActionDef _ -> $notImplemented