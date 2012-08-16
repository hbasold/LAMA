{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Transform (transform) where

import Development.Placeholders

import Prelude hiding (mapM)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (fromString)
import qualified  Data.Set as Set
import qualified Data.ByteString.Char8 as BS
import Data.List.Split (splitOn)
import Data.Maybe (maybeToList)
import Data.Traversable (mapM)
import Data.Monoid

import Control.Monad.Trans.Class
import Control.Monad (when, liftM)
import Control.Monad.State (gets)

import Control.Arrow (first)
import Control.Applicative ((<$>))
import Control.Monad.Writer (WriterT(..))
import Control.Monad.Error (MonadError(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import ExtractPackages
import TrEquation
import TransformCommon
import TransformMonads
import TransformSimple
import TransformAutomata

-- | Gets the definition for a node. This may trigger
-- the translation of the node.
getNode :: S.Path -> TransM (L.SimpIdent, L.Node)
getNode = getUserOperator $ \o ->
  do let n = fromString $ S.userOpName o
     nodeTranslated <- packageHasNode n
     when (not nodeTranslated) (trOpDecl o)
     liftM (n,) $ lookupNode n
  where
    lookupNode nName = gets nodes >>= lookupErr ("Unknown node " ++ L.identPretty nName) nName

trOpDecl :: S.Declaration -> TransM ()
trOpDecl (S.UserOpDecl {
             S.userOpKind = kind
             , S.userOpImported = isImported
             , S.userOpInterface = ifStatus
             , S.userOpName = name
             , S.userOpSize = size
             , S.userOpParams = params
             , S.userOpReturns = returns
             , S.userOpNumerics = numerics
             , S.userOpContent = content }) =
  do inputs <- liftM concat . (liftM $ map (\(x,_,_) -> x)) $ mapM trVarDecl params -- inputs have no default/last
     (outputs, outpDefault, outpLastInit) <- trVarDecls returns
     addDefaults $ Map.fromList outpDefault
     addLastInits $ Map.fromList outpLastInit
     node <- mkNode inputs outputs content
     declareNode (fromString name) node
  where
    mkNode :: [L.Variable] -> [L.Variable] -> S.DataDef -> TransM L.Node
    mkNode inp outp (S.DataDef { S.dataSignals = sigs, S.dataLocals = locals, S.dataEquations = equations }) = do
      (localVars, localsDefault, localsInit) <- trVarDecls locals
      addDefaults $ Map.fromList localsDefault
      addLastInits $ Map.fromList localsInit
      let -- create new output variables (x -> x_out) ...
          outp' = map (updateVarName $ flip BS.append $ BS.pack "_out") outp
          -- use old output variables as local variables ...
          localVars' = localVars ++ outp
          -- and assign the corresponding value to them (x_out = x)
          outputDefs = foldr
                       (\(x, x') ds -> (L.InstantExpr (L.varIdent x') $ L.mkAtomVar (L.varIdent x)) : ds )
                       [] $ zip outp outp'
      (eqs, usedNodes) <-
        liftM (first extract)
        . localScope (const $ Scope (mkVarMap inp) (mkVarMap outp) (mkVarMap localVars))
        . runWriterT
        $ mapM trEquation equations
      let (flow, automata) = trEqRhs eqs
          (localVars'', stateVars) = separateVars (trEqAsState eqs) localVars'
          precondition = foldl (L.mkExpr2 L.And) (L.constAtExpr $ L.boolConst True) (trEqPrecond eqs)

      -- check if defaults and last inits have been used up
      remainingDefaults <- gets defaults
      remainingLastInits <- gets lastInits
      when (not (Map.null remainingDefaults)) (throwError $ "Unused defaults: " ++ show remainingDefaults)
      when (not (Map.null remainingLastInits)) (throwError $ "Unused lasts: " ++ show remainingLastInits)

      -- FIXME: respect multiple points of usages!
      subNodes <- Map.fromList <$> mapM getNode (Set.toList usedNodes)
      return $ L.Node inp outp'
        (L.Declarations (subNodes `Map.union` (Map.fromList $ trEqSubAutom eqs))
         (localVars'' ++ trEqLocalVars eqs) (stateVars ++ trEqStateVars eqs))
        flow
        outputDefs automata (trEqInits eqs) precondition

    extract :: [TrEquation TrEqCont] -> TrEquation (L.Flow, Map Int L.Automaton)
    extract = foldlTrEq mergeEq (L.Flow [] [], Map.empty)
      where
        mergeEq (f1, a1) (SimpleEq f2) =
          (f1 `mappend` f2, a1)
        -- we don't care if variables have been declared inside a state,
        -- we declare them outside nevertheless.
        mergeEq (f1, a1) (AutomatonEq a2 _ condFlow) =
          let a = if Map.null a1
                  then Map.singleton 0 a2
                  else Map.insert ((fst $ Map.findMin a1) + 1) a2 a1
          in (f1 `mappend` condFlow, a)
        mergeEq r NonExecutable = r

trOpDecl _ = undefined

mkPath :: String -> S.Path
mkPath = S.Path . splitOn "::"

transform :: String -> Package -> Either String L.Program
transform topNode ps =
  case runTransM (getNode $ mkPath $ topNode) ps of
    Left e -> Left e
    Right ((topNodeName, n), decls) ->
      do constants <- gatherConstants ps
         (flowLocals, flowStates, flowInit, topFlow) <- mkFreeFlow (topNodeName, n)
         return $ L.Program
           (mkEnumDefs $ types decls) constants
           (L.Declarations (Map.singleton topNodeName n) flowLocals flowStates)
           topFlow flowInit
           (L.constAtExpr $ L.boolConst True) (L.constAtExpr $ L.boolConst True)
  where
    mkFreeFlow :: (L.SimpIdent, L.Node) -> Either String ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkFreeFlow (x, n) =
      let inp = map L.mkAtomVar . map L.varIdent $ L.nodeInputs n
          outpType = L.mkProductT . map L.varType $ L.nodeOutputs n
          outpIds = map (Just . L.varIdent) $ L.nodeOutputs n
      in do (a, decl) <- mkLocalAssigns outpIds (Right (x, inp, outpType))
            let locs = (L.nodeInputs n) ++ (L.nodeOutputs n) ++ (maybeToList decl)
            let sts = []
            let stInit = Map.empty
            let flow = L.Flow a []
            return (locs, sts, stInit, flow)
    
    mkEnumDefs :: Map L.SimpIdent (Either Type L.EnumDef) -> Map TypeAlias L.EnumDef
    mkEnumDefs = Map.fromAscList . foldr (\(x, t) tds -> either (const tds) (\td -> (x,td):tds) t) [] . Map.toAscList

    gatherConstants :: MonadError String m => Package -> m (Map L.SimpIdent L.Constant)
    gatherConstants p =
      do pConsts <- mkConstDefs $ pkgConsts p
         subConsts <- liftM mconcat . mapM gatherConstants . Map.elems $ pkgSubPackages p
         return $ pConsts `mappend` subConsts

    mkConstDefs :: MonadError String m => [S.ConstDecl] -> m (Map L.SimpIdent L.Constant)
    mkConstDefs = liftM Map.fromList . mapM trConstDecl

-- | Gives back either a set of definitions which is
-- a single assignment in case the given equation is a
-- simple expression. If the given equation is the using
-- of a node with multiple return values this set of
-- definitions consists of the call to the node and
-- a projection for each variable. In that case also
-- a set of intermediate variables to be declared is returned.
trEquation :: S.Equation -> TrackUsedNodes (TrEquation TrEqCont)
trEquation (S.SimpleEquation lhsIds expr) =
  fmap SimpleEq <$> trSimpleEquation lhsIds expr
trEquation (S.AssertEquation S.Assume _name expr) =
  lift $ trExpr' expr >>= \pc ->  return $ (baseEq NonExecutable) { trEqPrecond = [pc] }
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine _name sts) ret returnsAll) =
  fmap (uncurry $ flip AutomatonEq []) <$> trStateEquation sts ret returnsAll
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented