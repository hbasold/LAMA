{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

{-| Feeding LAMA programs to the SMT solver -}

module Transform where

import Development.Placeholders

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Types
import Language.SMTLib2 as SMT
import Language.SMTLib2.Internals (declareType, SMTExpr(Var))
import Data.Unit
import Data.String (IsString(..))
import Data.Array as Arr

import Data.Natural
import NatInstance
import qualified Data.Set as Set
import Data.Set (Set, union, unions)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.List as List
import Data.List (zip4)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Foldable (foldlM, foldrM)
import Data.Monoid

import Control.Monad.Trans.Class
import Control.Monad.State (StateT(..), MonadState(..), gets)
import Control.Monad.Error (ErrorT(..), MonadError(..))
import Control.Monad.Reader (ReaderT(..), ask, asks)
import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow ((&&&), second)

import SMTEnum
import LamaSMTTypes
import Definition
import TransformEnv
import Internal.Monads

-- | Gets an "undefined" value for a given type of expression.
-- The expression itself is not further analysed.
-- FIXME: Make behaviour configurable, i.e. bottom can be some
-- default value or a left open stream
-- (atm it does the former).
getBottom :: TypedExpr -> TypedExpr
getBottom (BoolExpr _)     = BoolExpr $ constant False
getBottom (IntExpr _)      = IntExpr  $ constant 0xdeadbeef
getBottom (RealExpr _)     = RealExpr . constant $ fromInteger 0xdeadbeef
getBottom (EnumExpr e) = EnumExpr e --evtl. TODO
getBottom (ProdExpr strs)  = ProdExpr $ fmap getBottom strs

-- | Transforms a LAMA program into a set of formulas which is
-- directly declared and a set of defining functions. Those functions
-- can be used to define a cycle by giving it the point in time.
-- Additionally gives back an environment which contains all declared
-- variables together with their defining stream. So if the defining
-- function (see above) is called for a cycle the corresponding stream
-- gets a value at that time (after getting the model).
lamaSMT :: Ident i =>
           NatImplementation -> EnumImplementation -> Program i
           -> ErrorT String SMT (ProgDefs, Env i)
lamaSMT natImpl' enumImpl' =
  flip runStateT (emptyEnv natImpl' enumImpl')
  . declProgram

-- | Declare the formulas which define a LAMA program.
declProgram :: Ident i => Program i -> DeclM i ProgDefs
declProgram p =
  do preamble
     putConstants (progConstantDefinitions p)
     declareEnums (progEnumDefinitions p)
     (declDefs, _) <- declareDecls Nothing Set.empty (progDecls p)
     flowDefs <- declareFlow Nothing (progFlow p)
     assertInits (progInitial p)
     precondDef <- declarePrecond Nothing (progAssertion p)
     invarDef <- declareInvariant Nothing (progInvariant p)
     return $ ProgDefs (declDefs ++ flowDefs) precondDef invarDef

-- | Declares common types etc.
-- At the moment just Natural is defined.
preamble :: DeclM i ()
preamble =
  gets natImpl >>= liftSMT . declareType (undefined :: Natural)

declareEnums :: Ident i => Map (TypeAlias i) (EnumDef i) -> DeclM i ()
declareEnums es =
  do anns <- (fmap Map.fromList . mapM declareEnum $ Map.toList es)
     let consAnns = foldl (\consAnns' (x, EnumDef conss) ->
                            insEnumConstrs (anns Map.! x) consAnns' conss)
                    Map.empty
                    $ Map.toList es
     putEnumAnn anns
     putEnumConsAnn consAnns
  where
    insEnumConstrs ann = foldl (\consAnns cons -> Map.insert cons ann consAnns)

declareEnum :: Ident i =>
               (TypeAlias i, EnumDef i) -> DeclM i (i, SMTAnnotation SMTEnum)
declareEnum (t, EnumDef cs) =
  let t' = fromString $ identString t
      cs' = map (fromString . identString) cs
  in do ann <- gets enumImpl >>= \impl -> return $ mkSMTEnumAnn impl t' cs'
        liftSMT (declareType (undefined :: SMTEnum) ann) >> return (t, ann)

declareDecls :: Ident i =>
                Maybe (TypedExpr)
                -> Set i
                -> Declarations i
                -> DeclM i ([Definition], Map i (Node i))
declareDecls activeCond excludeNodes d =
  do let (excluded, toDeclare)
           = Map.partitionWithKey (\n _ -> n `Set.member` excludeNodes)
             $ declsNode d
     defs <- mapM (uncurry $ declareNode activeCond) $ Map.toList toDeclare
     inp <- declareVars $ declsInput d
     locs <- declareVars $ declsLocal d
     states <- declareVars $ declsState d
     modifyVars $ mappend (inp `mappend` locs `mappend` states)
     return (concat defs, excluded)

declareVars :: Ident i => [Variable i] -> DeclM i (Map i (TypedExpr))
declareVars = fmap (Map.fromList) . declareVarList

declareVarList :: Ident i => [Variable i] -> DeclM i ([(i, TypedExpr)])
declareVarList = mapM declareVar

declareVar :: Ident i => Variable i -> DeclM i ((i, TypedExpr))
declareVar (Variable x t) =
  do v    <- typedVar (identString x) t
     addVar v
     return (x, v)
  where
    typedVar :: Ident i =>
                String
                -> Type i
                -> DeclM i (TypedExpr)
    typedVar v (GroundType BoolT)
      = liftSMT $ fmap BoolExpr $ varNamed v
    typedVar v (GroundType IntT)
      = liftSMT $ fmap IntExpr $ varNamed v
    typedVar v (GroundType RealT)
      = liftSMT $ fmap RealExpr $ varNamed v
    typedVar v (GroundType _) = $notImplemented
    typedVar v (EnumType et)
      = do etAnn <- lookupEnumAnn et
           liftSMT $ fmap EnumExpr $ varNamedAnn v etAnn
    typedVar v (ProdType ts) =
      do vs <- mapM (typedVar (v ++ "_comp")) ts
         return (ProdExpr $ listArray (0, (length vs) - 1) vs)
{-
-- | Declares a stream of type Enum, including possible extra constraints on it.
enumVar :: MonadSMT m
           => SMTAnnotation Natural -> SMTAnnotation SMTEnum
           -> m (Stream SMTEnum, [Definition])
enumVar argAnn ann@(EnumTypeAnn _ _ _) = liftSMT (funAnn argAnn ann) >>= return . (, [])
enumVar argAnn ann@(EnumBitAnn size _ biggestCons) =
  do v <- liftSMT (funAnn argAnn ann)
     constr <- liftSMT $
               defFunAnn argAnn unit $
               \t -> bvule (toBVExpr (v `app` t)) (constantAnn biggestCons size)
     return (v, [SingleDef constr])
-}

-- | Declares a node and puts the interface variables into the environment.
-- Here it becomes crucial that a node is used at most once in a program, since
-- otherwise there would rise conflicting definitions for the inputs.
-- 
-- Nodes used inside a location of an automaton get some special handling. First
-- the automata are analysed to find out which nodes are used inside a location
-- (using getNodesInLocations). Then all nodes _except_ those found before are
-- declared. The other nodes are deferred to be declared in the corresponding
-- location (see declareAutomaton and declareLocations).
declareNode :: Ident i =>
               Maybe (TypedExpr) -> i -> Node i -> DeclM i [Definition]
declareNode active nName nDecl =
  do (interface, defs) <- localVarEnv (const emptyVarEnv) $
                          declareNode' active nDecl
     modifyNodes $ Map.insert nName interface
     return defs
  where
    declareNode' :: Ident i =>
                    Maybe (TypedExpr) -> Node i
                    -> DeclM i (NodeEnv i, [Definition])
    declareNode' activeCond n =
      do let automNodes =
               mconcat . map getNodesInLocations . Map.elems $ nodeAutomata n
         (declDefs, undeclaredNodes) <-
           declareDecls activeCond automNodes $ nodeDecls n
         outDecls <- declareVarList $ nodeOutputs n
         ins <- mapM (lookupVar . varIdent) . declsInput $ nodeDecls n
         let outs = Map.fromList outDecls
         modifyVars $ Map.union (Map.fromList outDecls)
         flowDefs <- declareFlow activeCond $ nodeFlow n
         automDefs <-
           fmap concat .
           mapM (declareAutomaton activeCond undeclaredNodes) .
           Map.toList $ nodeAutomata n
         assertInits $ nodeInitial n
         precondDef <- declarePrecond activeCond $ nodeAssertion n
         varDefs <- gets varEnv
         return (NodeEnv ins outs varDefs,
                 declDefs ++ flowDefs ++ automDefs ++ [precondDef])

-- | Extracts all nodes which are used inside some location.
getNodesInLocations :: Ident i => Automaton i -> Set i
getNodesInLocations = mconcat . map getUsedLoc . automLocations
  where
    getUsedLoc :: Ident i => Location i -> Set i
    getUsedLoc (Location _ flow) = mconcat . map getUsed $ flowDefinitions flow
    getUsed (NodeUsage _ n _) = Set.singleton n
    getUsed _ = Set.empty

-- | Creates definitions for instant definitions. In case of a node usage this
-- may produce multiple definitions. If 
declareInstantDef :: Ident i =>
                     Maybe (TypedExpr)
                     -> InstantDefinition i
                     -> DeclM i [Definition]
declareInstantDef activeCond inst@(InstantExpr x e) =
  do (res, []) <- trInstant (error "no activation condition") inst
     xVar <- lookupVar x
     let args = getArgSet e
     argsE <- mapM lookupVar $ Set.toList args
     argsN <- mapM getN argsE
     def <- declareConditionalAssign
            activeCond (getBottom xVar) xVar args argsN False res
     return [def]
declareInstantDef activeCond inst@(NodeUsage x n _) =
  do (outp, inpDefs) <- trInstant activeCond inst
     xVar            <- lookupVar x
     nEnv            <- lookupNode n
     outN            <- mapM getN $ nodeEnvOut nEnv
     outpDef         <- declareConditionalAssign
                        activeCond (getBottom xVar) xVar (Map.keysSet $ nodeEnvOut nEnv) (Map.elems outN) False outp
     return $ inpDefs ++ [outpDef]

-- | Translates an instant definition into a function which can be
-- used to further refine this instant (e.g. wrap it into an ite).
-- This may also return definitions of the parameters of a node.
-- The activation condition is only used for the inputs of a node.
trInstant :: Ident i => Maybe (TypedExpr) -> InstantDefinition i -> DeclM i (Env i -> [(i, TypedExpr)] -> TypedExpr, [Definition])
trInstant _ (InstantExpr _ e) = return (runTransM $ trExpr e, [])
trInstant inpActive (NodeUsage _ n es) =
  do nEnv <- lookupNode n
     let esTr = map (runTransM . trExpr) es
         y    = runTransM $ trOutput $ nodeEnvOut nEnv
         ins = map (Set.toList . getArgSet) es
     insE <- mapM (mapM lookupVar) ins
     insN <- mapM (mapM getN) insE
     inpDefs  <- mapM (\(x, n, e, eTr) ->
                        declareConditionalAssign
                        inpActive (getBottom x) x (getArgSet e) n False eTr)
                 $ zip4 (nodeEnvIn nEnv) insN es esTr
     return (y, inpDefs)

trOutput :: Ident i => Map i (TypedExpr) -> TransM i (TypedExpr)
trOutput map = do
                 s <- ask
                 outList <- mapM (trOutput' s) (Map.toList map)
                 return $ mkProdExpr outList
               where
                 trOutput' s (i, te) = case lookup i (fst s) of
                                       Nothing -> throwError $ "No argument (output) binding for " ++ identPretty i
                                       Just n -> return n

-- | Creates a declaration for a state transition.
-- If an activation condition c is given, the declaration boils down to
-- x' = (ite c e x) where e is the defining expression. Otherwise it is just
-- x' = e.
declareTransition :: Ident i =>
                     Maybe (TypedExpr)
                     -> StateTransition i
                     -> DeclM i Definition
declareTransition activeCond (StateTransition x e) =
  do xVar     <- lookupVar x
     let e'      = runTransM $ trExpr e
         args    = getArgSet e
     argsE <- mapM lookupVar $ Set.toList args
     argsN <- mapM getN argsE
     declareConditionalAssign activeCond (getBottom xVar) xVar args argsN True e'

-- | Creates a declaration for an assignment. Depending on the
-- activation condition the given expression or a default expression
-- is used (generated by genDefault). Additionally the position in the
-- stream of /x/ which will be defined, can be specified by modPos
-- (see declareDef).
declareConditionalAssign :: Ident i =>
                            Maybe (TypedExpr)
                            -> TypedExpr
                            -> TypedExpr
                            -> Set i
                            -> [Int]
                            -> Bool
                            -> (Env i -> [(i, TypedExpr)] -> TypedExpr)
                            -> DeclM i Definition
declareConditionalAssign activeCond defaultExpr x al ns succ ef =
  case activeCond of
    Nothing -> declareDef x al ns succ ef
    Just c  ->
      declareDef x al ns succ (\env t -> liftIte c (ef env t) defaultExpr)

-- | Creates a definition for a given variable. Whereby a function to
-- manipulate the stream position at which it is defined is used (normally
-- id or succ' to define instances or state transitions).
-- The second argument /x/ is the stream to be defined and the last
-- argument (/ef/) is a function that generates the defining expression.
declareDef :: Ident i => TypedExpr -> Set i -> [Int] -> Bool ->
              (Env i -> [(i, TypedExpr)] -> TypedExpr) -> DeclM i Definition
declareDef x as ns succ ef =
  do env         <- get
     let defType = varDefType x
     xN          <- getN x
     ann         <- getTypedAnnotation $ [xN] ++ ns
     d           <- defFunc defType ann
                    $ \a -> liftRel (.==.) (head a) $ ef env $ zip ((Set.toList as) ++ [error "Last argument must not be evaluated!"]) (tail a)
     return $ ensureDefinition ([xN] ++ ns) succ d
  where
    varDefType (ProdExpr ts) = ProdType . fmap varDefType $ Arr.elems ts
    varDefType _               = boolT

getTypedAnnotation :: Ident i => [Int] -> DeclM i [TypedAnnotation]
getTypedAnnotation ns = mapM getTypedAnnotation' ns
  where
    getTypedAnnotation' n =
      do vars    <- gets varList
         eAnn <- gets enumAnn
         return $ getTypedAnnCases $ vars !! n
           where getTypedAnnCases var =
                   case var of
                     BoolExpr _ -> BoolAnnotation ()
                     IntExpr _ -> IntAnnotation ()
                     RealExpr _ -> RealAnnotation ()
                     EnumExpr (Var _ k) -> EnumAnnotation k
                     ProdExpr k -> ProdAnnotation $ fmap getTypedAnnCases k

declareFlow :: Ident i => Maybe (TypedExpr) -> Flow i -> DeclM i [Definition]
declareFlow activeCond f =
  do defDefs        <- fmap concat
                       . mapM (declareInstantDef activeCond)
                       $ flowDefinitions f
     transitionDefs <- mapM (declareTransition activeCond) $ flowTransitions f
     return $ defDefs ++ transitionDefs

-- | Declares an automaton by
-- * defining an enum for the locations
-- * defining two variables which hold the active location (see mkStateVars)
-- * ordering the data flow from the locations by the defined variables (see
--    extractAssigns)
-- * defining formulas for each variables (see declareLocations)
-- * defining the variables for the active location by using the edge
--    conditions (mkTransitionEq)
-- * asserting the initial location
declareAutomaton :: Ident i =>
                    Maybe (TypedExpr)
                    -> Map i (Node i)
                    -> (Int, Automaton i)
                    -> DeclM i [Definition]
declareAutomaton activeCond localNodes (_, a) =
  do automIndex <- nextAutomatonIndex
     let automName = "Autom" ++ show automIndex
         enumName  = fromString $ automName ++ "States"
         stateT    = EnumType enumName
         locNames  =
           Map.fromList
           . map (id &&& (locationName automName . runLocationId))
           $ map getLocId (automLocations a)
         locCons   = fmap EnumCons locNames
         enum      = EnumDef $ Map.elems locCons
         actName   = "act" ++ automName
         actId     = fromString actName
         selName   = "sel" ++ automName
         selId     = fromString selName
     declareEnums $ Map.singleton enumName enum
     (act, sel) <- mkStateVars actName selName enumName
     modifyVars ( `Map.union` Map.fromList
                  [(actId, act),
                   (selId, sel)
                  ]
                )
     locDefs <- (flip runReaderT (locCons, localNodes))
                $ declareLocations activeCond act
                (automDefaults a) (automLocations a)
     {-edgeDefs <- mkTransitionEq activeCond stateT locCons actId selId
                 $ automEdges a
     assertInit (selId, locConsConstExpr locCons stateT $ automInitial a)
   -}return $ locDefs-- ++ edgeDefs

  where
    getLocId (Location i _) = i

    -- | Create the name for a location (original name
    -- prefixed by the automaton name).
    locationName :: Ident i => String -> i -> i
    locationName automName sName = fromString $ automName ++ identString sName

{-
    -- | Create the enum constructor for a given location name as constant.
    locConsConstExpr :: Ord i =>
                        Map (LocationId i) (EnumConstr i)
                        -> Type i
                        -> LocationId i
                        -> ConstExpr i
    locConsConstExpr locNames t loc
      = mkTyped (ConstEnum ((Map.!) locNames loc)) t
-}

-- | Generate names of two variable which represent
-- the state of the automaton (s, sel). Where
-- s represents the current state which is calculated
-- at the beginning of a clock cycle. sel saves this
-- state for the next cycle.
mkStateVars :: Ident i =>
               String
               -> String
               -> i
               -> DeclM i (TypedExpr, TypedExpr)
mkStateVars actName selName stateEnum =
  do stEnumAnn <- lookupEnumAnn stateEnum
     act <- liftSMT $ fmap EnumExpr $ varNamedAnn actName stEnumAnn
     addVar act
     sel <- liftSMT $ fmap EnumExpr $ varNamedAnn selName stEnumAnn
     addVar sel
     return (act, sel)

-- | Extracts the the expressions for each variable seperated into
-- local definitons and state transitions.
extractAssigns :: Ord i =>
                  [Location i]
                  -> (Map i [(LocationId i, InstantDefinition i)],
                      Map i [(LocationId i, StateTransition i)])
extractAssigns = foldl addLocExprs (Map.empty, Map.empty)
  where
    addLocExprs (defExprs, stateExprs) (Location l flow) =
      (foldl (\defs inst -> putInstant l inst defs) defExprs
                 $ flowDefinitions flow,
       foldl (\transs trans -> putTrans l trans transs) stateExprs
                 $ flowTransitions flow)

    putDef d Nothing   = Just $ [d]
    putDef d (Just ds) = Just $ d : ds

    putInstant l inst@(InstantExpr x _) = Map.alter (putDef (l, inst)) x
    putInstant l inst@(NodeUsage x _ _) = Map.alter (putDef (l, inst)) x

    putTrans l trans@(StateTransition x _) = Map.alter (putDef (l, trans)) x

-- | Transports the mapping LocationId -> EnumConstr which was defined
-- beforehand and the undeclared nodes which are used in one of the
-- locations of the automata to be defined.
type AutomTransM i =
  ReaderT (Map (LocationId i) (EnumConstr i), Map i (Node i)) (DeclM i)

lookupLocName :: Ident i => LocationId i -> AutomTransM i (EnumConstr i)
lookupLocName l
  = asks fst >>= lookupErr ("Unknown location " ++ identPretty l) l

lookupLocalNode :: Ident i => i -> AutomTransM i (Node i)
lookupLocalNode n
  = asks snd >>= lookupErr ("Unknow local node " ++ identPretty n) n

-- | Declares the data flow inside the locations of an automaton.
declareLocations :: Ident i =>
                    Maybe (TypedExpr)
                    -> TypedExpr
                    -> Map i (Expr i)
                    -> [Location i]
                    -> AutomTransM i [Definition]
declareLocations activeCond s defaultExprs locations =
  let (defs, trans) = extractAssigns locations
      -- add defaults for nowhere defined variables
      defs'         = defs `Map.union` (fmap (const []) defaultExprs)
  in do instDefs    <- fmap concat
                       . mapM (declareLocDefs activeCond defaultExprs)
                       $ Map.toList defs'
        --transDefs   <- mapM (declareLocTransitions activeCond)
        --               $ Map.toList trans
        return $ instDefs-- ++ transDefs
  where
    declareLocDefs :: Ident i =>
                      Maybe (TypedExpr)
                      -> Map i (Expr i)
                      -> (i, [(LocationId i, InstantDefinition i)])
                      -> AutomTransM i [Definition]
    declareLocDefs active defaults (x, locs) =
      do defaultExpr    <- getDefault defaults x locs
         (res, inpDefs) <- declareLocDef active s defaultExpr locs
         xVar           <- lookupVar x
         let xBottom    = getBottom xVar
             args       = (\(_,InstantExpr _ e) -> getArgSet e) $ head locs
         argsE          <- mapM lookupVar $ Set.toList args
         argsN          <- lift $ mapM getN (argsE ++ [s])
         def            <-
           lift $ declareConditionalAssign active xBottom xVar args argsN False res
         return $ inpDefs ++ [def]

{-
    declareLocTransitions :: Ident i =>
                             Maybe (TypedExpr)
                             -> (i, [(LocationId i, StateTransition i)])
                             -> AutomTransM i Definition
    declareLocTransitions active (x, locs) =
      do res         <- trLocTransition s locs
         xStream     <- lookupVar x
         natAnn      <- gets natImpl
         let succAnn = succ' natAnn
             xApp    = appStream xStream
         def         <-
           lift $ declareConditionalAssign active succAnn xApp xStream res
         return def
-}

    getDefault defaults x locs =
      do fullyDefined <- isFullyDefined locs
         if fullyDefined
           then return Nothing
           else fmap Just
                $ lookupErr (identPretty x ++ " not fully defined") x defaults

    isFullyDefined locDefs =
      do locNames <- asks fst
         return $ (Map.keysSet locNames) == (Set.fromList $ map fst locDefs)

declareLocDef :: Ident i =>
                 Maybe (TypedExpr)
                 -> TypedExpr
                 -> Maybe (Expr i)
                 -> [(LocationId i, InstantDefinition i)]
                 -> AutomTransM i (Env i -> [(i, TypedExpr)] -> TypedExpr, [Definition])
declareLocDef activeCond s defaultExpr locs =
  do (innerPat, locs') <- case defaultExpr of
       Nothing -> case locs of
         (l:ls) -> (, ls) <$> uncurry (trLocInstant activeCond) l
         _      -> error "Empty automaton not allowed"
       Just e  -> return ((runTransM $ trExpr e, []), locs)
     foldlM (\(f, defs) (l, inst)
             -> trLocInstant activeCond l inst >>= \(res, defs') ->
             mkLocationMatch s f l res >>=
             return . (, defs ++ defs'))
       innerPat locs'
  where
    trLocInstant :: Ident i =>
                    Maybe (TypedExpr)
                    -> LocationId i
                    -> InstantDefinition i
                    -> AutomTransM i (Env i -> [(i, TypedExpr)] -> TypedExpr, [Definition])
    trLocInstant _ _ inst@(InstantExpr _ _) =
      lift $ trInstant (error "no activation condition required") inst
    trLocInstant active l inst@(NodeUsage _ n _) = error ("Not yet implemented")
      {-do (locActive, activeDef) <- mkLocationActivationCond active s l
         node                   <- lookupLocalNode n
         nodeDefs               <- lift $ declareNode (Just locActive) n node
         (r, inpDefs)           <- lift $ trInstant (Just locActive) inst
         return (r, [activeDef] ++ nodeDefs ++ inpDefs)

trLocTransition :: Ident i =>
                   SMTFunction [TypedExpr] SMTEnum
                   -> [(LocationId i, StateTransition i)]
                   -> AutomTransM i (Env i -> [(i, TypedExpr)] -> TypedExpr)
trLocTransition s locs =
  let (innerPat, locs') = case locs of
        (l:ls) -> (trLocTrans $ snd l, ls)
        _      -> error "Empty automaton not allowed."
  in foldlM (\f -> uncurry (mkLocationMatch s f)
                   . second trLocTrans)
     innerPat locs'
  where
    trLocTrans (StateTransition _ e) = runTransM $ trExpr e
-}

mkLocationMatch :: Ident i =>
                   TypedExpr
                   -> (Env i -> [(i, TypedExpr)] -> TypedExpr)
                   -> LocationId i
                   -> (Env i -> [(i, TypedExpr)] -> TypedExpr)
                   -> AutomTransM i (Env i -> [(i, TypedExpr)] -> TypedExpr)
mkLocationMatch (EnumExpr s) f l lExpr =
  do lCons <- lookupLocName l
     lEnum <- lift $ trEnumConsAnn lCons <$> lookupEnumConsAnn lCons
     return
       (\env t -> liftIte
                  (BoolExpr $ (unEnum $ snd $ last t) .==. lEnum)
                  (lExpr env t)
                  (f env t))

-- | Creates a variable which is true iff the given activation
-- condition is true and the the given location is active.
mkLocationActivationCond :: Ident i =>
                            Maybe (TypedExpr)
                            -> TypedExpr
                            -> LocationId i
                            -> AutomTransM i (TypedExpr, Definition)
mkLocationActivationCond activeCond (EnumExpr s) l =
  do lCons <- lookupLocName l
     lEnum <- lift $ trEnumConsAnn lCons <$> lookupEnumConsAnn lCons
     let cond = \_env t -> BoolExpr $ s .==. lEnum
     activeVar <- liftSMT $ fmap BoolExpr $ var
     def <- lift $ declareConditionalAssign activeCond
            (BoolExpr $ constant False) activeVar Set.empty [] False cond
     return (activeVar, def)

{-
-- | Creates two equations for the edges. The first calculates
-- the next location (act). This is a chain of ite for each state surrounded
-- by a match on the last location (sel). The definition of sel is just
-- the saving of act for the next cycle.
mkTransitionEq :: Ident i =>
                  Maybe (TypedExpr)
                  -> Type i
                  -> Map (LocationId i) (EnumConstr i)
                  -> i
                  -> i
                  -> [Edge i]
                  -> DeclM i [Definition]
mkTransitionEq activeCond locationEnumTy locationEnumConstrs act sel es =
  -- we reuse the translation machinery by building a match expression and
  -- translating that.
  -- We use foldr to enforce that transition that occur later in the
  -- source get a lower priority.
  do stateDef <- declareInstantDef activeCond
                 . InstantExpr act
                 . mkMatch
                   locationEnumConstrs
                   locationEnumTy
                   sel
                   (mkTyped (AtExpr $ AtomVar sel) locationEnumTy)
                 . Map.toList
                 $ foldr addEdge Map.empty es
     stateTr <- declareTransition activeCond
                $ StateTransition
                  sel
                  (mkTyped (AtExpr $ AtomVar act) locationEnumTy)
     return $ stateDef ++ [stateTr]
  where
     addEdge (Edge h t c) m =
       Map.alter
       (extendStateExpr locationEnumTy
        (locConsExpr locationEnumConstrs locationEnumTy h)
        (locConsExpr locationEnumConstrs locationEnumTy t) c)
       h m

     -- | Build up the expression which calculates the next
     -- state for each given state. This is a chain of ite's for
     -- each state.
     extendStateExpr :: Type i
                        -> Expr i
                        -> Expr i
                        -> Expr i
                        -> Maybe (Expr i)
                        -> Maybe (Expr i)
     extendStateExpr sT h t c Nothing = Just $ mkTyped (Ite c t h) sT
     extendStateExpr _ _ t c (Just e) = Just $ preserveType (Ite c t) e

     -- | Build match expression (pattern matches on last state sel)
     mkMatch :: Ord i =>
                Map (LocationId i) (EnumConstr i)
                -> Type i
                -> i
                -> Expr i
                -> [(LocationId i, Expr i)]
                -> Expr i
     mkMatch locCons locationT sel' defaultExpr locExprs =
       mkTyped (
         Match (mkTyped (AtExpr $ AtomVar sel') locationT)
         $ (mkPattern locExprs) ++ (mkDefaultPattern defaultExpr))
       locationT
       where
         mkPattern
           = foldl (\pats (h, e) ->
                     (Pattern (EnumPattern ((Map.!) locCons h)) e) : pats)
             []
         mkDefaultPattern e = [Pattern BottomPattern e]

     -- | Create the enum constructor for a given location name.
     locConsExpr :: Ord i =>
                    Map (LocationId i) (EnumConstr i)
                    -> Type i
                    -> LocationId i
                    -> Expr i
     locConsExpr locNames t loc
       = mkTyped (AtExpr $ AtomEnum ((Map.!) locNames loc)) t
-}

assertInits :: Ident i => StateInit i -> DeclM i ()
assertInits = mapM_ assertInit . Map.toList

assertInit :: Ident i => (i, ConstExpr i) -> DeclM i ()
assertInit (x, e) =
  do x' <- lookupVar x
     e' <- trConstExpr e
     let def = liftRel (.==.) x' e'
     liftSMT $ liftAssert def

-- | Creates a definition for a precondition p. If an activation condition c
-- is given, the resulting condition is (=> c p).
declarePrecond :: Ident i => Maybe (TypedExpr) -> Expr i -> DeclM i Definition
declarePrecond activeCond e =
  do env      <- get
     let args = getArgSet e
     argsE    <- mapM lookupVar $ Set.toList args
     argsN    <- mapM getN argsE
     ann      <- getTypedAnnotation argsN
     d        <- case activeCond of
       Nothing -> defFunc boolT ann $ \a -> runTransM (trExpr e) env (zip (Set.toList $ args) a)
       Just c -> defFunc boolT ann $
                 \a -> (flip (flip runTransM env) (zip (Set.toList $ args) a))
		       (trExpr e >>= \e' ->
                         return $ liftBool2 (.=>.) c e')
     return $ ensureDefinition argsN False d

declareInvariant :: Ident i =>
                    Maybe (TypedExpr) -> Expr i -> DeclM i Definition
declareInvariant = declarePrecond

trConstExpr :: Ident i => ConstExpr i -> DeclM i (TypedExpr)
trConstExpr (untyped -> Const c)
  = return $ trConstant c
trConstExpr (untyped -> ConstEnum x)
  = lookupEnumConsAnn x >>= return . EnumExpr . trEnumConsAnn x
trConstExpr (untyped -> ConstProd (Prod cs)) =
  ProdExpr . listArray (0, length cs - 1) <$> mapM trConstExpr cs

type TransM i = ReaderT ([(i, TypedExpr)], Env i) (Either String)

{-
doAppStream :: TypedStream i -> TransM i (TypedExpr)
doAppStream s = askStreamPos >>= return . appStream s
-}

-- beware: uses error
runTransM :: TransM i a -> Env i -> [(i, TypedExpr)] -> a
runTransM m e a = case runReaderT m (a, e) of
  Left err -> error err
  Right r -> r

lookupVar' :: Ident i => i -> TransM i (TypedExpr)
lookupVar' x =
  do vs <- asks $ vars . varEnv . snd
     case Map.lookup x vs of
       Nothing -> throwError $ "Unknown variable " ++ identPretty x
       Just x' -> return x'

lookupEnumConsAnn' :: Ident i =>
                      (EnumConstr i) -> TransM i (SMTAnnotation SMTEnum)
lookupEnumConsAnn' t
  = asks (enumConsAnn . snd)
    >>= lookupErr ("Unknown enum constructor " ++ identPretty t) t

{-
askStreamPos :: TransM i StreamPos
askStreamPos = asks fst
-}

getArgSet :: Ident i => Expr i -> Set i
getArgSet expr = case untyped expr of
  AtExpr (AtomConst c)  -> Set.empty
  AtExpr (AtomVar x)    -> Set.singleton x
  AtExpr (AtomEnum x)   -> Set.empty
  LogNot e              -> getArgSet e
  Expr2 op e1 e2        -> Set.union (getArgSet e1) (getArgSet e2)
  Ite c e1 e2           -> Set.unions [getArgSet c, getArgSet e1, getArgSet e2]
  ProdCons (Prod es)    -> foldr (Set.union . getArgSet) Set.empty es
  Project x i           -> Set.singleton x
  Match e pats -> Set.unions $ [getArgSet e] ++ map (\(Pattern _ x) -> getArgSet x) pats

-- we do no further type checks since this
-- has been done beforehand.
trExpr :: Ident i => Expr i -> TransM i (TypedExpr)
trExpr expr = case untyped expr of
  AtExpr (AtomConst c) -> return $ trConstant c
  AtExpr (AtomVar x)   -> do
                            s <- ask
                            case lookup x (fst s) of
                              Nothing -> throwError $ "No argument binding for " ++ identPretty x
                              Just n -> return n
  AtExpr (AtomEnum x)  -> EnumExpr <$> trEnumCons x
  LogNot e             -> lift1Bool not' <$> trExpr e
  Expr2 op e1 e2       -> applyOp op <$> trExpr e1 <*> trExpr e2
  Ite c e1 e2          -> liftIte <$> trExpr c <*> trExpr e1 <*> trExpr e2
  ProdCons (Prod es)   -> (ProdExpr . listArray (0, (length es) - 1))
                          <$> mapM trExpr es
  Project x i          ->
    do (ProdExpr s) <- lookupVar' x
       return $ (s ! fromEnum i)
  Match e pats         -> trExpr e >>= flip trPattern pats

trPattern :: Ident i => TypedExpr -> [Pattern i] -> TransM i (TypedExpr)
trPattern e@(EnumExpr _) = trEnumMatch e
trPattern _ = error "Cannot match on non enum expression"

trEnumMatch :: Ident i => TypedExpr -> [Pattern i] -> TransM i (TypedExpr)
trEnumMatch x pats =
  -- respect order of patterns here by putting the last in the default match
  -- and bulding the expression bottom-up:
  -- (match x {P_1.e_1, ..., P_n.e_n})
  -- ~> (ite P_1 e_1 (ite ... (ite P_n-1 e_n-1 e_n) ...))
  do innermostPat <- fmap snd . trEnumPattern x $ last pats
     foldrM (chainPatterns x) innermostPat (init pats)
  where
    chainPatterns c p ifs =
      trEnumPattern c p >>= \(cond, e) ->
      return $ liftIte cond e ifs
    trEnumPattern c (Pattern h e) = (,) <$> trEnumHead c h <*> trExpr e
    trEnumHead c (EnumPattern e) =
      trEnumCons e >>= \y ->
      return $ liftRel (.==.) c (EnumExpr y)
    trEnumHead _ BottomPattern = return . BoolExpr $ constant True

trEnumConsAnn :: Ident i =>
                 EnumConstr i -> SMTAnnotation SMTEnum -> SMTExpr SMTEnum
trEnumConsAnn x = constantAnn (SMTEnum . fromString $ identString x)

trEnumCons :: Ident i => EnumConstr i -> TransM i (SMTExpr SMTEnum)
trEnumCons x = lookupEnumConsAnn' x >>= return . trEnumConsAnn x

applyOp :: BinOp -> TypedExpr -> TypedExpr -> TypedExpr
applyOp Or      e1 e2 = liftBoolL or'  [e1, e2]
applyOp And     e1 e2 = liftBoolL and' [e1, e2]
applyOp Xor     e1 e2 = liftBoolL xor  [e1, e2]
applyOp Implies e1 e2 = liftBool2 (.=>.) e1 e2
applyOp Equals  e1 e2 = prodAll $ liftRel (.==.) e1 e2
applyOp Less    e1 e2 = liftOrd (.<.) e1 e2
applyOp LEq     e1 e2 = liftOrd (.<=.) e1 e2
applyOp Greater e1 e2 = liftOrd (.>.) e1 e2
applyOp GEq     e1 e2 = liftOrd (.>=.) e1 e2
applyOp Plus    e1 e2 = liftArithL plus [e1, e2]
applyOp Minus   e1 e2 = liftArith minus e1 e2
applyOp Mul     e1 e2 = liftArithL mult [e1, e2]
applyOp RealDiv e1 e2 = liftReal2 divide e1 e2
applyOp IntDiv  e1 e2 = liftInt2 div' e1 e2
applyOp Mod     e1 e2 = liftInt2 mod' e1 e2
