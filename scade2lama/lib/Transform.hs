{-# LANGUAGE TemplateHaskell #-}

module Transform (transform) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (catMaybes)
import Data.String (fromString)
import Data.Either (partitionEithers, either)
import Data.List ((\\))
import qualified Data.ByteString.Char8 as BS

import Control.Monad.State
import Control.Monad.Error (MonadError(..))
import Control.Arrow ((***), (&&&))
import Control.Applicative (Applicative(..), (<$>))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import qualified FlattenListExpr as FlattenList
import qualified RewriteTemporal as Temporal
import qualified RewriteOperatorApp as OpApp
import qualified UnrollTemporal as Unroll

updateVarName :: (BS.ByteString -> BS.ByteString) -> L.Variable -> L.Variable
updateVarName f (L.Variable (L.SimpIdent x) t) = L.Variable (L.SimpIdent $ f x) t

type Type = L.Type L.SimpIdent
type TypeAlias = L.TypeAlias L.SimpIdent

data Decls = Decls { types :: Map TypeAlias (Either Type L.TypeDef), constants :: [S.ConstDecl], packages :: Map String [S.Declaration] }
emptyDecls :: Decls
emptyDecls = Decls Map.empty [] Map.empty

type TransM = StateT Decls (Either String)

lookupErr :: (MonadError e m, Ord k) => e -> Map k v -> k -> m v
lookupErr err m k = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

transform :: [S.Declaration] -> Either String L.Program
transform ds =
  let ds' = rewrite ds
  in case runStateT (mapM trDeclaration ds') emptyDecls of
    Left e -> Left e
    Right (nodes, decls) ->
      let nodesMap = Map.fromList $ catMaybes nodes
          (flowLocals, flowStates, flowInit, topFlow) = mkTopFlow nodesMap
      in Right $ L.Program
        (mkTypeDefs $ types decls) (mkConstDefs $ constants decls)
        (L.Declarations nodesMap flowStates flowLocals)
        topFlow flowInit
        (L.constAtExpr $ L.boolConst True) (L.constAtExpr $ L.boolConst True)
  where
    mkTopFlow :: Map L.SimpIdent L.Node -> ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkTopFlow = mergeFlows . foldl (\fs n -> mkFreeFlow n : fs) [] . Map.toList
    
    mkFreeFlow :: (L.SimpIdent, L.Node) -> ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkFreeFlow (x, n) =
      let scopedInp = map (updateVarName $ BS.append (BS.snoc (L.identBS x) '_')) $ L.nodeInputs n
          scopedOutp = map (updateVarName $ BS.append (BS.snoc (L.identBS x) '_')) $ L.nodeOutputs n
          locs = scopedInp ++ scopedOutp
          sts = []
          stInit = Map.empty
          use = L.mkNodeUsage x $ map (L.mkAtomVar . L.varIdent) scopedInp
          flow = L.Flow [L.InstantDef (map L.varIdent scopedOutp) use] []
      in (locs, sts, stInit, flow)
    
    mergeFlows :: [([L.Variable], [L.Variable], L.StateInit, L.Flow)] -> ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mergeFlows
      = foldl
          (\(l, s, i, f) (l', s', i', f') -> (l' ++ l, s' ++ s, i `Map.union` i', mergeFlow f f'))
          ([], [], Map.empty, L.Flow [] [])
    
    mergeFlow :: L.Flow -> L.Flow -> L.Flow
    mergeFlow (L.Flow def tr) (L.Flow def' tr') = L.Flow (def' ++ def) (tr' ++ tr)
    
    mkTypeDefs :: Map L.SimpIdent (Either Type L.TypeDef) -> Map TypeAlias L.TypeDef
    mkTypeDefs = Map.fromAscList . foldr (\(x, t) tds -> either (const tds) (\td -> (x,td):tds) t) [] . Map.toAscList
    
    mkConstDefs :: [S.ConstDecl] -> Map L.SimpIdent L.Constant
    mkConstDefs = Map.fromList . map trConstDecl
    
    rewrite = Unroll.rewrite . OpApp.rewrite . Temporal.rewrite . FlattenList.rewrite

trDeclaration :: S.Declaration -> TransM (Maybe (L.SimpIdent, L.Node))
trDeclaration (S.OpenDecl path) = $notImplemented
trDeclaration (S.TypeBlock decls) =
  let tds = Map.fromList $ map trTypeDecl decls
  in modify (\ds -> ds { types = types ds `Map.union` tds }) >> return Nothing
trDeclaration (S.PackageDecl vis name decls) = $notImplemented
trDeclaration op@(S.UserOpDecl {}) = fmap Just $ trOpDecl op
trDeclaration (S.ConstBlock consts) = $notImplemented

trOpDecl :: S.Declaration -> TransM (L.SimpIdent, L.Node)
trOpDecl (S.UserOpDecl {
            S.userOpKind = kind
            , S.userOpImported = isImported
            , S.userOpInterface = ifStatus
            , S.userOpName = name
            , S.userOpSize = size
            , S.userOpParams = params
            , S.userOpReturns = returns
            , S.userOpNumerics = numerics
            , S.userOpContent = content }) = do
  node <- mkNode (concat $ map trVarDecl params) (concat $ map trVarDecl returns) content
  return (fromString name, node)
  where
    mkNode :: [L.Variable] -> [L.Variable] -> S.DataDef -> TransM L.Node
    mkNode inp outp (S.DataDef { S.dataSignals = sigs, S.dataLocals = locs, S.dataEquations = equations }) =
      let locs' = Map.fromList $ map (L.varIdent &&& id) $ concat $ map trVarDecl locs
          outpAsLoc = Map.fromList $ map (L.varIdent &&& id) outp
          vars = locs' `Map.union` outpAsLoc
          -- create new output variables (x -> x_out) ...
          outp' = map (updateVarName $ flip BS.append $ BS.pack "_out") outp
          -- and assign the corresponding value to them (x_out = x)
          outputDefs = foldr (\(x, x') ds -> (L.InstantDef [L.varIdent x'] $ L.mkInstantExpr $ L.mkAtomVar (L.varIdent x)) : ds ) [] $ zip outp outp'
          subNodes = Map.empty
          automata = Map.empty
      in do
        ((definitions, transitions), stateInits) <- liftM ((partitionEithers *** concat) . unzip) $ mapM trEquation equations
        let inits = Map.fromList stateInits
        stateVars <- mapM (\x -> lookupErr ("Unknown variable " ++ show x) vars x) $ Map.keys inits
        let localVars = Map.elems vars \\ stateVars
        return $ L.Node inp outp'
          (L.Declarations subNodes stateVars localVars)
          (L.Flow definitions transitions)
          outputDefs automata inits
trOpDecl _ = undefined

-- | Gives back either 
trEquation :: S.Equation -> TransM (Either L.InstantDefinition L.StateTransition, [(L.SimpIdent, L.ConstExpr)])
trEquation (S.SimpleEquation lhsIds expr) = do
  let ids = map trLhsId lhsIds
  (inst, stateInit) <- trExpr expr
  case stateInit of
    Nothing -> return (Left $ L.InstantDef ids inst, [])
    Just init -> case ids of
      [x] -> case inst of
        (L.Fix (L.InstantExpr expr')) -> return (Right $ L.StateTransition x expr', [(x, init)])
        _ -> throwError $ "Cannot use not state equation"
      _ -> throwError $ "Cannot pattern match in state equation"
trEquation (S.AssertEquation aType name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation sm return returnsAll) = $notImplemented
trEquation (S.ClockedEquation name block return returnsAll) = $notImplemented

trVarDecl :: S.VarDecl -> [L.Variable]
trVarDecl (S.VarDecl xs ty defaultVal lastVal) =
  let xs' = map trVarId xs
      ty' = trTypeExpr ty
  in map (flip L.Variable ty') xs'

trTypeDecl :: S.TypeDecl -> (TypeAlias, Either Type L.TypeDef)
trTypeDecl = $notImplemented

trConstDecl :: S.ConstDecl -> (L.SimpIdent, L.Constant)
trConstDecl = $notImplemented

trVarId :: S.VarId -> L.SimpIdent
trVarId (S.VarId x clock probe) = fromString x

trLhsId :: S.LHSId -> L.SimpIdent
trLhsId (S.Named x) = fromString x
trLhsId S.Bottom = $notImplemented

trTypeExpr :: S.TypeExpr -> Type
trTypeExpr S.TypeBool = L.boolT
trTypeExpr S.TypeInt = L.intT
trTypeExpr S.TypeReal = L.realT
trTypeExpr S.TypeChar = $notImplemented
trTypeExpr (S.TypePower ty expr) = $notImplemented
trTypeExpr (S.TypePath path) = $notImplemented
trTypeExpr (S.TypeVar x) = $notImplemented
trTypeExpr (S.TypeRecord fields) = $notImplemented -- [(String,TypeExpr)]
trTypeExpr (S.TypeEnum ctors) = $notImplemented -- [String]


-- | We require a very special structure (enforced by rewriting done
--    beforehand):
--    A temporal expression must be of the form "e1 -> pre e2" where
--    e1 and e2 are non-temporal expressions. The same must also
--    hold for the application of operators
trExpr :: S.Expr -> TransM (L.Instant, Maybe L.ConstExpr)
trExpr expr = case expr of 
    S.FBYExpr _ _ _ -> undefined
    S.LastExpr x -> $notImplemented
    S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)
      -> (L.mkInstantExpr *** Just) <$> ((,) <$> trExpr' e2 <*> trConstExpr e1)
    S.ApplyExpr op es -> $notImplemented
    normalExpr -> (L.mkInstantExpr &&& (const Nothing)) <$> trExpr' normalExpr
  where
    trExpr' :: S.Expr -> TransM L.Expr
    trExpr' (S.IdExpr (S.Path [x])) = pure $ L.mkAtomVar (fromString x)
    trExpr' (S.IdExpr path) = $notImplemented
    trExpr' (S.NameExpr name) = $notImplemented
    trExpr' (S.ConstIntExpr c) = $notImplemented
    trExpr' (S.ConstBoolExpr c) = L.constAtExpr <$> pure (L.boolConst c)
    trExpr' (S.ConstFloatExpr c) = $notImplemented
    trExpr' (S.ConstPolyIntExpr i s) = $notImplemented
    trExpr' (S.BinaryExpr op e1 e2) = L.mkExpr2 <$> pure (trBinOp op) <*> trExpr' e1 <*> trExpr' e2
    trExpr' (S.UnaryExpr S.UnNot e) = L.mkLogNot <$> trExpr' e
    trExpr' (S.UnaryExpr op e) = $notImplemented
    trExpr' (S.ListExpr es) = $notImplemented
    trExpr' (S.ArrayExpr es) = $notImplemented
    trExpr' (S.IfExpr c e1 e2) = L.mkIte <$> trExpr' c <*> trExpr' e1 <*> trExpr' e2
    trExpr' (S.ReverseExpr e) = $notImplemented
    trExpr' (S.CaseExpr e ps) = $notImplemented
    trExpr' (S.IndexExpr e1 e2) = $notImplemented
    trExpr' (S.DefaultIndexExpr e1 es e2) = $notImplemented
    trExpr' (S.StaticProjectionExpr e1 e2 e3) = $notImplemented
    trExpr' (S.AppendExpr e1 e2) = $notImplemented
    trExpr' (S.TransposeExpr e i1 i2) = $notImplemented
    trExpr' (S.TimesExpr e1 e2) = $notImplemented
    trExpr' _ = undefined -- s. trExpr

trConstExpr :: S.Expr -> TransM L.ConstExpr
trConstExpr (S.ConstIntExpr c) = $notImplemented
trConstExpr (S.ConstBoolExpr c) = L.mkConst <$> pure (L.boolConst c)
trConstExpr (S.ConstFloatExpr c) = $notImplemented
trConstExpr (S.ConstPolyIntExpr i s) = $notImplemented
trConstExpr e = throwError $ show e ++ " is not a constant."
 
trBinOp :: S.BinOp -> L.BinOp
trBinOp S.BinPlus = L.Plus
trBinOp S.BinMinus = L.Minus
trBinOp S.BinTimes = L.Mul
trBinOp S.BinDiv = L.IntDiv
trBinOp S.BinMod = L.Mod
trBinOp S.BinRDiv = L.RealDiv
trBinOp S.BinEquals = L.Equals
trBinOp S.BinDifferent = $notImplemented
trBinOp S.BinLesser = L.Less
trBinOp S.BinGreater = L.Greater
trBinOp S.BinLessEq = L.LEq
trBinOp S.BinGreaterEq = L.GEq
trBinOp S.BinAfter = undefined
trBinOp S.BinAnd = L.And
trBinOp S.BinOr = L.Or
trBinOp S.BinXor = L.Xor
trBinOp S.BinPower = $notImplemented

