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

import Control.Monad (when, liftM)
import Control.Monad.State (gets)
import Control.Monad.Error (MonadError(..))
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
  in tryFrom askGlobalPkg pkgName n n' `catchError` (const $ tryFrom askCurrentPkg pkgName n n')
  where
    tryFrom asker pkgName n n' =
      asker >>= \startPkg ->
      (localPkg $ const startPkg)
      . openPackage pkgName $
      do nodeTranslated <- packageHasNode n'
         pkg <- fmap pkgUserOps askCurrentPkg
         when (not nodeTranslated)
           (lookupErr ("Unknown operator " ++ n) n pkg >>= trOpDecl)
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
      ((flow, newLocalVars, newStateVars, stateInits, automata, subAutomataNodes), usedNodes) <-
        liftM (first extract) . runWriterT $ mapM trEquation equations
      let (localVars', stateVars) = separateVars stateInits (concat localVars)
      -- FIXME: respect multiple points of usages!
      subNodes <- Map.fromList <$> mapM getNode (Set.toList usedNodes)
      return $ L.Node inp outp'
        (L.Declarations (subNodes `Map.union` subAutomataNodes)
         (localVars' ++ newLocalVars) (stateVars ++ newStateVars))
        flow
        outputDefs automata stateInits

    extract :: [TrEquation TrEqCont] ->
               (L.Flow, [L.Variable], [L.Variable], L.StateInit, Map Int L.Automaton, Map L.SimpIdent L.Node)
    extract = foldl merge (L.Flow [] [], [], [], Map.empty, Map.empty, Map.empty)
      where
        merge (f1, l1, s1, i1, a1, n1) (TrEquation (SimpleEq f2) l2 s2 i2 n2) =
          (concatFlows f1 f2, l1 ++ l2, s1 ++ s2,
           i1 `Map.union` i2, a1,
           n1 `Map.union` (Map.fromList n2))
        merge (f1, l1, s1, i1, a1, n1) (TrEquation (AutomatonEq a2) l2 s2 i2 n2)
          | Map.null a1 = (f1, l1 ++ l2, s1 ++ s2, i1 `Map.union` i2,
                           Map.singleton 0 a2,
                           n1 `Map.union` (Map.fromList n2))
          | otherwise = (f1, l1 ++ l2, s1 ++ s2, i1 `Map.union` i2,
                         Map.insert ((fst $ Map.findMin a1) + 1) a2 a1,
                         n1 `Map.union` (Map.fromList n2))

    concatFlows :: L.Flow -> L.Flow -> L.Flow
    concatFlows (L.Flow d1 s1) (L.Flow d2 s2) = L.Flow (d1 ++ d2) (s1 ++ s2)

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
trEquation (S.AssertEquation aType name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation sm ret returnsAll) =
  fmap AutomatonEq <$> trStateEquation sm ret returnsAll
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented