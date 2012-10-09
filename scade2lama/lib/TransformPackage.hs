{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module TransformPackage (transformPackage) where

import Development.Placeholders

import Prelude hiding (mapM)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (fromString)
import qualified Data.ByteString.Char8 as BS
import Data.List.Split (splitOn)
import Data.Maybe (maybeToList)
import Data.Traversable (mapM)
import Data.Monoid

import Control.Monad.Trans.Class
import Control.Monad (when, liftM)
import Control.Monad.State (gets)

import Control.Arrow ((|||))
import Control.Applicative ((<$>))
import Control.Monad.Writer (WriterT(..))
import Control.Monad.Error (MonadError(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import Lookup
import ExtractPackages
import TrEquation
import TransformCommon
import TransformMonads
import TransformSimple
import TransformAutomata
import VarGen

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
             S.userOpKind
             , S.userOpImported
             , S.userOpInterface
             , S.userOpName
             , S.userOpSize
             , S.userOpParams
             , S.userOpReturns
             , S.userOpNumerics
             , S.userOpContent }) =
  do inputs <- liftM concat . (liftM $ map (\(x,_,_) -> x)) $ mapM trVarDecl userOpParams -- inputs have no default/last
     (outputs, outpDefault, outpLastInit) <- trVarDecls userOpReturns
     node <- mkNode inputs outputs
             (Map.fromList outpDefault) (Map.fromList outpLastInit)
             userOpContent
     declareNode (fromString userOpName) node
  where
    mkNode :: [L.Variable] -> [L.Variable]
              -> Map L.SimpIdent L.Expr -> Map L.SimpIdent (Either L.ConstExpr L.Expr)
              -> S.DataDef -> TransM L.Node
    mkNode inp outp outpDefault outpLastInit (S.DataDef { S.dataSignals
                                                        , S.dataLocals
                                                        , S.dataEquations }) = do
      (localVars, localsDefault, localsInit) <- trVarDecls dataLocals
      let -- create new output variables (x -> x_out) ...
          outp' = map (updateVarName $ flip BS.append $ BS.pack "_out") outp
          -- use old output variables as local variables ...
          localVars' = localVars ++ outp
          -- and assign the corresponding value to them (x_out = x)
          outputDefs = foldr
                       (\(x, x') ds -> (L.InstantExpr (L.varIdent x') $ L.mkAtomVar (L.varIdent x)) : ds )
                       [] $ zip outp outp'
      (eqs, usedNodes) <-
        localScope (const $ Scope (mkVarMap inp) (mkVarMap outp) (mkVarMap localVars)
                    (Map.fromList localsDefault `mappend` outpDefault)
                    (Map.fromList localsInit `mappend` outpLastInit))
        . runWriterT
        $ mapM trEquation dataEquations
      eq <- mkEqInitAutom $ extract eqs
      let (flow, automata) = trEqRhs eq
          flow' = flow { L.flowDefinitions = L.flowDefinitions flow ++ outputDefs }
          (localVars'', stateVars) = separateVars (trEqAsState eq) localVars'
          precondition = foldl (L.mkExpr2 L.And) (L.constAtExpr $ L.boolConst True) (trEqPrecond eq)

      subNodes <- mapM (liftM snd . getNode) usedNodes
      return $ L.Node
        (L.Declarations (subNodes `Map.union` (Map.fromList $ trEqSubAutom eq))
         inp (localVars'' ++ trEqLocalVars eq) (stateVars ++ trEqStateVars eq))
        outp'
        flow' automata (trEqInits eq) precondition

    extract :: [TrEquation TrEqCont] -> TrEquation (L.Flow, (L.Flow, L.Flow), Map Int L.Automaton)
    extract = foldlTrEq mergeEq (mempty, (mempty, mempty), Map.empty)
      where
        mergeEq (f1, initF, a1) (SimpleEq f2) =
          (f1 `mappend` f2, initF, a1)
        mergeEq (f1, (i1, def1), a1) (InitEq (i2, def2)) =
          (f1, (i1 `mappend` i2, def1 `mappend` def2), a1)
        -- we don't care if variables have been declared inside a state,
        -- we declare them outside nevertheless.
        mergeEq (f1, initF, a1) (AutomatonEq a2 _ condFlow) =
          let a = if Map.null a1
                  then Map.singleton 1 a2
                  else Map.insert ((fst $ Map.findMin a1) + 1) a2 a1
          in (f1 `mappend` condFlow, initF, a)
        mergeEq r NonExecutable = r

    mkEqInitAutom :: MonadVarGen m => TrEquation (L.Flow, (L.Flow, L.Flow), Map Int L.Automaton)
                     -> m (TrEquation (L.Flow, Map Int L.Automaton))
    mkEqInitAutom eq =
      do dummy <- liftM fromString $ newVar "dummy"
         initLoc <- liftM fromString $ newVar "init"
         running <- liftM fromString $ newVar "running"
         return $ fmap (mkInitAutom dummy initLoc running) eq
      where
        mkInitAutom dummy initLoc running (f, (i, def), a)
          -- only add an automaton if there actually is an initialising flow
          | i == mempty && def == mempty = (f, a)
          | otherwise =
            let locations = [L.Location dummy i,
                             L.Location initLoc i,
                             L.Location running def ]
                autom = L.Automaton locations dummy
                        [L.Edge dummy initLoc (L.constAtExpr $ L.boolConst True),
                         L.Edge initLoc running (L.constAtExpr $ L.boolConst True)] Map.empty
            in (f, Map.insert 0 autom a)


trOpDecl _ = undefined

mkPath :: String -> S.Path
mkPath = S.Path . splitOn "::"

transformPackage :: String -> Package -> VarGen (Either String L.Program)
transformPackage topNode ps = do
  r <- runTransM (getNode $ mkPath $ topNode) ps
  case r of
    Left e -> return $ Left e
    Right ((topNodeName, n), decls) -> return $
      do constants <- gatherConstants ps
         (flowInputs, flowLocals, flowStates, flowInit, topFlow) <- mkFreeFlow (topNodeName, n)
         return $ L.Program
           (mkEnumDefs $ types decls) constants
           (L.Declarations (Map.singleton topNodeName n) flowInputs flowLocals flowStates)
           topFlow flowInit
           (L.constAtExpr $ L.boolConst True) (L.constAtExpr $ L.boolConst True)
  where
    mkFreeFlow :: (L.SimpIdent, L.Node) -> Either String ([L.Variable], [L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkFreeFlow (x, n) =
      let inp = map L.mkAtomVar . map L.varIdent . L.declsInput $ L.nodeDecls n
          outpType = L.mkProductT . map L.varType $ L.nodeOutputs n
          outpIds = map (Just . L.varIdent) $ L.nodeOutputs n
      in do (a, decl) <- mkLocalAssigns outpIds (Right (x, inp, outpType))
            let locs = (L.nodeOutputs n) ++ (maybeToList decl)
            let sts = []
            let stInit = Map.empty
            let flow = L.Flow a []
            return (L.declsInput $ L.nodeDecls n, locs, sts, stInit, flow)
    
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
  fmap (SimpleEq ||| InitEq) <$> trSimpleEquation lhsIds expr
trEquation (S.AssertEquation S.Assume _name expr) =
  lift $ trExpr' expr >>= \pc ->  return $ (baseEq NonExecutable) { trEqPrecond = [pc] }
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine _name sts) ret returnsAll) =
  fmap (uncurry $ flip AutomatonEq []) <$> trStateEquation sts ret returnsAll
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented