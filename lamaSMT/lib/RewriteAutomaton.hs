{-# LANGUAGE TemplateHaskell #-}
module RewriteAutomaton (mkAutomatonEquations) where

import Development.Placeholders

import Data.String (IsString(..))
import qualified Data.Map as Map
import Data.Map (Map, (!))

import Control.Arrow ((&&&))

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Types

-- | Transforms an automaton into a set of equations
-- which represent the edges and the data flow
-- inside the locations.
mkAutomatonEquations :: Ident i => String -> Automaton i
                        -> (Map (TypeAlias i) (EnumDef i), Declarations i, Flow i, StateInit i)
mkAutomatonEquations automName a =
  let enumName = fromString $ automName ++ "States"
      stateT = EnumType enumName
      (s, s_1) = mkStateVars automName
      (enum, locNames, eqs) = mkEq automName stateT s $ automLocations a
      sEqs = mkTransitionEq locNames stateT s s_1 $ automEdges a
      i = mkStateInitEq locNames stateT s_1 $ automInitial a
      (sVar, s_1Var) = (Variable s stateT, Variable s_1 stateT)
  in (Map.singleton enumName enum,
      Declarations Map.empty [sVar] [s_1Var],
      mergeFlows eqs sEqs,
      i)

-- | Generate names of two variable which represent
-- the state of the automaton (s, s_1). Where
-- s represents the current state which is calculated
-- at the beginning of a clock cycle. s_1 saves this
-- state for the next cycle.
mkStateVars :: Ident i => String -> (i, i)
mkStateVars n =
  (fromString $ n ++ "State",
   fromString $ n ++ "State_1")

-- | Creates two equations for the edges. The first calculates
-- the next location (s). This is a chain of ite for each state surrounded
-- by a match on the last location (s_1). The definition of s_1 is just
-- the saving of s for the next cycle.
mkTransitionEq :: Ord i => Map (LocationId i) i -> Type i -> i -> i -> [Edge i] -> Flow i
mkTransitionEq locNames stateT s s_1 es =
  -- We use foldr to enforce that transition that occur later in the
  -- source get a lower priority.
  let stateDef = mkMatch locNames stateT s_1
                 . Map.toList
                 $ foldr addEdge Map.empty es
      stateTr = StateTransition s_1 (mkTyped (AtExpr $ AtomVar s) stateT)
  in Flow [InstantExpr s stateDef] [stateTr]
  where
     addEdge (Edge h t c) m =
       Map.alter
       (extendStateExpr stateT (locConsExpr locNames stateT h) (locConsExpr locNames stateT t) c)
       h m

     -- | Build up the expression which calculates the next
     -- state for each given state. This is a chain of ite's for
     -- each state.
     extendStateExpr :: Type i -> Expr i -> Expr i -> Expr i -> Maybe (Expr i) -> Maybe (Expr i)
     extendStateExpr sT h t c Nothing = Just $ mkTyped (Ite c t h) sT
     extendStateExpr _ _ t c (Just e) = Just $ preserveType (Ite c t) e

-- | Creates the initialisation of s_1 based on the initial location.
mkStateInitEq :: Ord i => Map (LocationId i) i -> Type i -> i -> LocationId i -> StateInit i
mkStateInitEq locNames stateT s_1 initLoc =
  Map.singleton s_1 (locConsConstExpr locNames stateT initLoc)

-- | Create equations for the data flow inside the loctions.
-- This is a match on the current location evaluating to
-- the corresponding expression.
-- Extracts all location names thereby and makes a mapping from
-- the location names in the source to the mangled names.
mkEq :: Ident i => String -> Type i -> i -> [Location i] -> (EnumDef i, Map (LocationId i) i, Flow i)
mkEq automName stateT s locs =
  let locNames = Map.fromList . map (id &&& locationName automName) . map getLocId $ locs
      (defExprs, stateExprs) = extractExprs locs
      defExprs' = fmap (mkMatch locNames stateT s) defExprs
      stateExprs' = fmap (mkMatch locNames stateT s) stateExprs
  in (EnumDef . map EnumCons $ Map.elems locNames,
      locNames,
      Flow (mkInstantDefs defExprs') (mkTransitions stateExprs'))
  where
    getLocId (Location i _) = i

-- Extracts the the expressions for each variable seperated into
-- local definitons and state transitions.
extractExprs :: Ord i => [Location i]
                -> (Map i [(LocationId i, Expr i)], Map i [(LocationId i, Expr i)])
extractExprs = foldl addLocExprs (Map.empty, Map.empty)
  where
    addLocExprs (defExprs, stateExprs) (Location l flow) =
      (foldl (\defs inst -> putInstant l inst defs) defExprs $ flowDefinitions flow,
       foldl (\transs trans -> putTrans l trans transs) stateExprs $ flowTransitions flow)

    putDef d Nothing = Just $ [d]
    putDef d (Just ds) = Just $ d : ds

    putInstant l (InstantExpr x e) = Map.alter (putDef (l, e)) x
    putInstant l (NodeUsage x n es) = $notImplemented

    putTrans l (StateTransition x e) = Map.alter (putDef (l, e)) x

-- | Build match expression (pattern matches on last state s_1)
mkMatch :: Ord i => Map (LocationId i) i -> Type i -> i -> [(LocationId i, Expr i)] -> Expr i
mkMatch locNames stateT s_1 locExprs = mkTyped (Match (mkVarExpr stateT s_1) (mkPattern locExprs)) stateT
  where mkPattern = foldl (\pats (h, e) -> (Pattern (EnumPat $ EnumCons (locNames ! h)) e) : pats) []

mkInstantDefs :: Map i (Expr i) -> [InstantDefinition i]
mkInstantDefs = map (uncurry InstantExpr) . Map.toList

mkTransitions :: Map i (Expr i) -> [StateTransition i]
mkTransitions = map (uncurry StateTransition) . Map.toList

-- | Create the name for a location (original name
-- prefixed by the automaton name).
locationName :: Ident i => String -> i -> i
locationName automName sName = fromString $ automName ++ identString sName

-- | Create the enum constructor for a given location name.
locConsExpr :: Ord i => Map (LocationId i) i -> Type i -> LocationId i -> Expr i
locConsExpr locNames t loc = mkTyped (AtExpr . AtomEnum $ EnumCons (locNames ! loc)) t

-- | Create the enum constructor for a given location name as constant.
locConsConstExpr :: Ord i => Map (LocationId i) i -> Type i -> LocationId i -> ConstExpr i
locConsConstExpr locNames t loc = mkTyped (ConstEnum $ EnumCons (locNames ! loc)) t

-- | Create a variable expression
mkVarExpr :: Type i -> i -> Expr i
mkVarExpr t s = mkTyped (AtExpr $ AtomVar s) t

mergeFlows :: Flow i -> Flow i -> Flow i
mergeFlows (Flow d1 s1) (Flow d2 s2) = Flow (d1 ++ d2) (s1 ++ s2)