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

import Control.Monad.Trans.Class
import Control.Monad (when, liftM, MonadPlus(..))
import Control.Monad.State (gets)
import Control.Monad.Error (MonadError(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Arrow (first)
import Control.Applicative ((<$>))
import Control.Monad.Writer (WriterT(..))

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
getNode (S.Path p) =
  let pkgName = init p
      n = last p
      n' = fromString n
  in do r <- runMaybeT $ (tryFrom askGlobalPkg pkgName n n') `mplus` (tryFrom askCurrentPkg pkgName n n')
        case r of
          Nothing -> throwError $ "Unknown operator " ++ n
          Just nDecl -> return nDecl
  where
    tryFrom :: TransM Package -> [String] -> String -> L.SimpIdent -> MaybeT TransM (L.SimpIdent, L.Node)
    tryFrom asker pkgName n n' =
      lift asker >>= \startPkg ->
      (localPkg $ const startPkg)
      . openPackage pkgName $
      do nodeTranslated <- packageHasNode n'
         pkg <- fmap pkgUserOps askCurrentPkg
         when (not nodeTranslated) (
           case Map.lookup n pkg of
             Nothing -> mzero
             Just o -> lift $ trOpDecl o
           )
         liftM (n',) $ lookupNode n'

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
     (outputs, outpDefault, outpLastInit) <- liftM unzip3 $ mapM trVarDecl returns
     addDefaults . Map.fromList $ concat outpDefault
     addLastInits . Map.fromList $ concat outpLastInit
     node <- mkNode inputs (concat outputs) content
     declareNode (fromString name) node
  where
    mkNode :: [L.Variable] -> [L.Variable] -> S.DataDef -> TransM L.Node
    mkNode inp outp (S.DataDef { S.dataSignals = sigs, S.dataLocals = locals, S.dataEquations = equations }) = do
      (localVars, localsDefault, localsInit) <- liftM unzip3 $ mapM trVarDecl locals
      addDefaults . Map.fromList $ concat localsDefault
      addLastInits . Map.fromList $ concat localsInit
      let -- create new output variables (x -> x_out) ...
          outp' = map (updateVarName $ flip BS.append $ BS.pack "_out") outp
          -- and assign the corresponding value to them (x_out = x)
          outputDefs = foldr
                       (\(x, x') ds -> (L.InstantExpr (L.varIdent x') $ L.mkAtomVar (L.varIdent x)) : ds )
                       [] $ zip outp outp'
      ((flow, newLocalVars, newStateVars, stateInits, automata, subAutomataNodes, precondition), usedNodes) <-
        liftM (first extract) . runWriterT $ mapM trEquation equations
      let (localVars', stateVars) = separateVars stateInits (concat localVars)
      -- FIXME: respect multiple points of usages!
      subNodes <- Map.fromList <$> mapM getNode (Set.toList usedNodes)
      return $ L.Node inp outp'
        (L.Declarations (subNodes `Map.union` subAutomataNodes)
         (localVars' ++ newLocalVars) (stateVars ++ newStateVars))
        flow
        outputDefs automata stateInits precondition

    extract :: [TrEquation TrEqCont] ->
               (L.Flow, [L.Variable], [L.Variable], L.StateInit, Map Int L.Automaton, Map L.SimpIdent L.Node, L.Expr)
    extract = foldl merge (L.Flow [] [], [], [], Map.empty, Map.empty, Map.empty, L.constAtExpr $ L.boolConst True)
      where
        merge (f1, l1, s1, i1, a1, n1, p) (TrEquation eq l2 s2 i2 n2) =
          mergeEq (f1, l1 ++ l2, s1 ++ s2,
                   i1 `Map.union` i2, a1,
                   n1 `Map.union` (Map.fromList n2), p) eq

        mergeEq (f1, l1, s1, i1, a1, n1, p) (SimpleEq f2) =
          (concatFlows f1 f2, l1, s1, i1, a1, n1, p)
        -- we don't care about the name of an automaton or if variables have
        -- been declared inside a state, we declare them outside nevertheless.
        mergeEq (f1, l1, s1, i1, a1, n1, p) (AutomatonEq _ a2 _) =
          let a = if Map.null a1
                  then Map.singleton 0 a2
                  else Map.insert ((fst $ Map.findMin a1) + 1) a2 a1
          in (f1, l1, s1, i1, a, n1, p)
        mergeEq (f1, l1, s1, i1, a1, n1, p) (PrecondEq e) =
          let p' = L.mkExpr2 L.And p e
          in (f1, l1, s1, i1, a1, n1, p')

    separateVars :: L.StateInit -> [L.Variable] -> ([L.Variable], [L.Variable])
    separateVars i =
      foldr (\v (ls, sts) ->
              if (L.varIdent v `Map.member` i)
              then (ls, v : sts) else (v : ls, sts))
      ([], [])

trOpDecl _ = undefined

mkPath :: String -> S.Path
mkPath = S.Path . splitOn "::"

transform :: String -> [S.Declaration] -> Either String L.Program
transform topNode ds =
  let ds' = extractPackages ds
  in case runTransM (getNode $ mkPath $ topNode) ds' of
    Left e -> Left e
    Right ((topNodeName, n), decls) ->
      do (flowLocals, flowStates, flowInit, topFlow) <- mkFreeFlow (topNodeName, n)
         return $ L.Program
           (mkEnumDefs $ types decls) (mkConstDefs $ constants decls)
           (L.Declarations (Map.singleton topNodeName n) flowLocals flowStates)
           topFlow flowInit
           (L.constAtExpr $ L.boolConst True) (L.constAtExpr $ L.boolConst True)
  where
    mkFreeFlow :: (L.SimpIdent, L.Node) -> Either String ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkFreeFlow (x, n) =
      let inp = map L.mkAtomVar . map L.varIdent $ L.nodeInputs n
          outpType = L.mkProductT . map L.varType $ L.nodeOutputs n
          outpIds = map L.varIdent $ L.nodeOutputs n
      in do (a, decl) <- mkLocalAssigns outpIds (Right (x, inp, outpType))
            let locs = (L.nodeInputs n) ++ (L.nodeOutputs n) ++ (maybeToList decl)
            let sts = []
            let stInit = Map.empty
            let flow = L.Flow a []
            return (locs, sts, stInit, flow)
    
    mkEnumDefs :: Map L.SimpIdent (Either Type L.EnumDef) -> Map TypeAlias L.EnumDef
    mkEnumDefs = Map.fromAscList . foldr (\(x, t) tds -> either (const tds) (\td -> (x,td):tds) t) [] . Map.toAscList
    
    mkConstDefs :: [S.ConstDecl] -> Map L.SimpIdent L.Constant
    mkConstDefs = Map.fromList . map trConstDecl

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
  liftM PrecondEq (lift $ trExpr' expr) >>= \pc -> return $ TrEquation pc [] [] Map.empty []
trEquation (S.AssertEquation S.Guarantee _name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation (S.StateMachine name sts) ret returnsAll) =
  fmap (flip (AutomatonEq name) []) <$> trStateEquation sts ret returnsAll
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented