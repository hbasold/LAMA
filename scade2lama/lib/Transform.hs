{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Transform (transform) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)

import Data.String (fromString)
import Data.Either (partitionEithers)
import Data.List ((\\))
import qualified  Data.Set as Set
import Data.Set (Set)
import qualified Data.ByteString.Char8 as BS
import Data.Ratio
import Data.List.Split (splitOn)

import Control.Monad.State
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Arrow ((***), (&&&))
import Control.Applicative (Applicative(..), (<$>))
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import qualified FlattenListExpr as FlattenList
import qualified RewriteTemporal as Temporal
import qualified RewriteOperatorApp as OpApp
import qualified UnrollTemporal as Unroll
import ExtractPackages as Extract

updateVarName :: (BS.ByteString -> BS.ByteString) -> L.Variable -> L.Variable
updateVarName f (L.Variable (L.SimpIdent x) t) = L.Variable (L.SimpIdent $ f x) t

type Type = L.Type L.SimpIdent
type TypeAlias = L.TypeAlias L.SimpIdent

data Decls = Decls {
     types :: Map TypeAlias (Either Type L.EnumDef),
     -- | Maps an identifier to the declared nodes in the current package
     nodes :: Map L.SimpIdent L.Node,
     packages :: Map L.SimpIdent Decls,
     constants :: [S.ConstDecl]
  } deriving Show
emptyDecls :: Decls
emptyDecls = Decls Map.empty Map.empty Map.empty []

type PackageEnv = Reader Package
type TransM = StateT Decls (ErrorT String PackageEnv)

runTransM :: TransM a -> Package -> Either String (a, Decls)
runTransM m = runReader $ runErrorT $ runStateT m emptyDecls

-- | Executes an action with a local state. The resulting state
-- is then combined with that befor using the given function
-- (comb newState oldState).
localState :: MonadState s m => (s -> s -> s) -> (s -> s) -> m a -> m a
localState comb f m =
  do curr <- get
     put $ f curr
     x <- m
     new <- get
     put $ comb new curr
     return x

updatePackage :: L.SimpIdent -> Decls -> Decls -> Decls
updatePackage n p ds = ds { packages = Map.adjust (const p) n $ packages ds }

createPackage :: L.SimpIdent -> TransM Decls
createPackage p = gets packages >>= return . Map.findWithDefault emptyDecls p

openPackage :: [String] -> TransM a -> TransM a
openPackage [] m = m
openPackage (p:ps) m =
  do currPkg <- ask
     case Map.lookup p (pkgSubPackages currPkg) of
       Nothing -> throwError $ "Unknown package " ++ p
       Just scadePkg ->
         let p' = fromString p
         in do pkg <- createPackage p'
               localState (updatePackage p') (const pkg) $
                 local (const scadePkg) m

-- | Checks if there is a node with the given name in the current package
packageHasNode :: L.SimpIdent -> TransM Bool
packageHasNode x = gets nodes >>= return . Map.member x

getNode :: S.Path -> TransM (L.SimpIdent, L.Node)
getNode (S.Path p) =
  let pkgName = init p
      n = last p
      n' = fromString n
  in openPackage pkgName $
     do nodeTranslated <- packageHasNode n'
        when (not nodeTranslated)
          (reader pkgUserOps >>= lookupErr ("Unknown operator" ++ n) n >>= trOpDecl)
        liftM (n',) $ lookupNode n'
  where
    lookupNode nName = gets nodes >>= lookupErr ("Unknown node" ++ L.identPretty nName) nName

resolveNodeName :: S.Path -> TransM L.SimpIdent
resolveNodeName (S.Path p) =
  let pkgName = init p
      n = last p
  in openPackage pkgName $
     do opExists <- packageHasOperator n
        if opExists then return $ fromString n
          else throwError $ "Unknown node " ++ n
  where
    packageHasOperator nName = reader pkgUserOps >>= return . Map.member nName

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

declareNode :: (MonadState Decls m) => L.SimpIdent -> L.Node -> m ()
declareNode x n = modify (\d -> d { nodes = Map.insert x n $ nodes d })

declarePackage :: (MonadState Decls m) => L.SimpIdent -> Decls -> m ()
declarePackage x p = modify (\d -> d { packages = Map.insert x p $ packages d })

addReqNode :: (MonadState Decls m) => L.SimpIdent -> S.Path -> m ()
addReqNode = undefined

mkPath :: String -> S.Path
mkPath = S.Path . splitOn "::"

transform :: String -> [S.Declaration] -> Either String L.Program
transform topNode ds =
  let ds' = Extract.extract $ rewrite ds
  in case runTransM (getNode $ mkPath $ topNode) ds' of
    Left e -> Left e
    Right ((topNodeName, n), decls) ->
      let (flowLocals, flowStates, flowInit, topFlow) = mkFreeFlow (topNodeName, n)
      in Right $ L.Program
         (mkEnumDefs $ types decls) (mkConstDefs $ constants decls)
         (L.Declarations (Map.singleton topNodeName n) flowLocals flowStates)
         topFlow flowInit
         (L.constAtExpr $ L.boolConst True) (L.constAtExpr $ L.boolConst True)
  where
    mkFreeFlow :: (L.SimpIdent, L.Node) -> ([L.Variable], [L.Variable], L.StateInit, L.Flow)
    mkFreeFlow (x, n) =
      let scopedInp = map (updateVarName $ BS.append (BS.snoc (L.identBS x) '_')) $ L.nodeInputs n
          scopedOutp = map (updateVarName $ BS.append (BS.snoc (L.identBS x) '_')) $ L.nodeOutputs n
          scopedOutpIdent = map L.varIdent scopedOutp
          outpVar = L.Variable
                    (L.SimpIdent $ L.identBS x `BS.append` BS.pack "_result")
                    (L.mkProductT $ map L.varType $ L.nodeOutputs n)
          locs = scopedInp ++ scopedOutp ++ [outpVar]
          projectExprs = map (L.Fix . L.InstantExpr . mkProdProject (L.varIdent outpVar) scopedOutpIdent) scopedOutpIdent
          projects = map (uncurry L.InstantDef) $ zip scopedOutpIdent projectExprs
          sts = []
          stInit = Map.empty
          use = L.mkNodeUsage x $ map (L.mkAtomVar . L.varIdent) scopedInp
          flow = L.Flow ([L.InstantDef (L.varIdent outpVar) use] ++ projects) []
      in (locs, sts, stInit, flow)
    
    mkEnumDefs :: Map L.SimpIdent (Either Type L.EnumDef) -> Map TypeAlias L.EnumDef
    mkEnumDefs = Map.fromAscList . foldr (\(x, t) tds -> either (const tds) (\td -> (x,td):tds) t) [] . Map.toAscList
    
    mkConstDefs :: [S.ConstDecl] -> Map L.SimpIdent L.Constant
    mkConstDefs = Map.fromList . map trConstDecl

    rewrite :: [S.Declaration] -> [S.Declaration]
    rewrite = FlattenList.rewrite .
              Temporal.rewrite .
              OpApp.rewrite .
              Unroll.rewrite

mkProdProject :: L.SimpIdent -> [L.SimpIdent] -> L.SimpIdent -> L.Expr
mkProdProject _ [] _ = undefined
mkProdProject from [_] _ = L.Fix $ L.AtExpr $ L.AtomVar from
mkProdProject from xs x
  = L.Fix $ L.Match
    (L.Fix $ L.AtExpr $ L.AtomVar from)
    [L.Pattern (L.ProdPat xs) (L.Fix $ L.AtExpr $ L.AtomVar x)]

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
            , S.userOpContent = content }) = do
  node <- mkNode (concat $ map trVarDecl params) (concat $ map trVarDecl returns) content
  declareNode (fromString name) node
  where
    mkNode :: [L.Variable] -> [L.Variable] -> S.DataDef -> TransM L.Node
    mkNode inp outp (S.DataDef { S.dataSignals = sigs, S.dataLocals = locs, S.dataEquations = equations }) =
      let locs' = Map.fromList $ map (L.varIdent &&& id) $ concat $ map trVarDecl locs
          outpAsLoc = Map.fromList $ map (L.varIdent &&& id) outp
          vars = locs' `Map.union` outpAsLoc
          -- create new output variables (x -> x_out) ...
          outp' = map (updateVarName $ flip BS.append $ BS.pack "_out") outp
          -- and assign the corresponding value to them (x_out = x)
          outputDefs = foldr
                       (\(x, x') ds -> (L.InstantDef (L.varIdent x') $ L.mkInstantExpr $ L.mkAtomVar (L.varIdent x)) : ds )
                       [] $ zip outp outp'
          automata = Map.empty
      in do
        (((definitions, transitions), stateInits), usedNodes) <-
          runWriterT $
            liftM ((partitionEithers *** concat) . unzip) $ mapM trEquation equations
        -- FIXME: respect multiple points of usages!??
        subNodes <- Map.fromList <$> mapM getNode (Set.toList usedNodes)
        let inits = Map.fromList stateInits
        stateVars <- mapM (\x -> lookupErr ("Unknown variable " ++ L.identPretty x) x vars) $ Map.keys inits
        let localVars = Map.elems vars \\ stateVars
        return $ L.Node inp outp'
          (L.Declarations subNodes localVars stateVars)
          (L.Flow definitions transitions)
          outputDefs automata inits

    usedNode (L.InstantDef _ (L.Fix (L.NodeUsage x _))) = Just x
    usedNode _ = Nothing

trOpDecl _ = undefined

-- | Extends TransM by a writer which tracks used nodes
type TrackUsedNodes = WriterT (Set S.Path) TransM

tellNode :: MonadWriter (Set S.Path) m => S.Path -> m ()
tellNode = tell . Set.singleton

-- | Gives back either 
trEquation :: S.Equation -> TrackUsedNodes (Either L.InstantDefinition L.StateTransition, [(L.SimpIdent, L.ConstExpr)])
trEquation (S.SimpleEquation lhsIds expr) = do
  let ids = map trLhsId lhsIds
  (inst, stateInit) <- trExpr expr
  case stateInit of
    Nothing -> case ids of
      [x] -> return (Left $ L.InstantDef x inst, [])
      _ -> $notImplemented
    Just sInit -> case ids of
      [x] -> case inst of
        (L.Fix (L.InstantExpr expr')) -> return (Right $ L.StateTransition x expr', [(x, sInit)])
        _ -> throwError $ "Cannot use not state equation"
      _ -> throwError $ "Cannot pattern match in state equation"
trEquation (S.AssertEquation aType name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation sm ret returnsAll) = $notImplemented
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented

trVarDecl :: S.VarDecl -> [L.Variable]
trVarDecl (S.VarDecl xs ty defaultVal lastVal) =
  let xs' = map trVarId xs
      ty' = trTypeExpr ty
  in map (flip L.Variable ty') xs'

trTypeDecl :: S.TypeDecl -> (TypeAlias, Either Type L.EnumDef)
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
--    hold for the application of operators.
--    Returns the instant which is a node application if needed.
--    The second part is the initialisation of a temporal
--    operator if one is given.
trExpr :: S.Expr -> TrackUsedNodes (L.Instant, Maybe L.ConstExpr)
trExpr expr = case expr of 
    S.FBYExpr _ _ _ -> undefined
    S.LastExpr x -> $notImplemented
    S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)
      -> (L.mkInstantExpr *** Just) <$> ((,) <$> trExpr' e2 <*> lift (trConstExpr e1))
    S.ApplyExpr op es -> do
      es' <- mapM trExpr' es
      app <- trOpApply op es'
      return (app, Nothing)
    normalExpr -> (L.mkInstantExpr &&& (const Nothing)) <$> trExpr' normalExpr
  where
    trExpr' :: S.Expr -> TrackUsedNodes L.Expr
    trExpr' (S.IdExpr (S.Path [x])) = pure $ L.mkAtomVar (fromString x)
    trExpr' (S.IdExpr path) = $notImplemented
    trExpr' (S.NameExpr name) = $notImplemented
    trExpr' (S.ConstIntExpr c) = L.constAtExpr <$> pure (L.mkIntConst c)
    trExpr' (S.ConstBoolExpr c) = L.constAtExpr <$> pure (L.boolConst c)
    trExpr' (S.ConstFloatExpr c) = L.constAtExpr <$> pure (L.mkRealConst $ approxRational c 0.01)
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

trOpApply :: S.Operator -> [L.Expr] -> TrackUsedNodes L.Instant
trOpApply (S.PrefixOp (S.PrefixPath p)) es =
          lift (resolveNodeName p) >>= \x -> return (L.mkNodeUsage x es) <* tellNode p
trOpApply _ _ = $notImplemented

trConstExpr :: S.Expr -> TransM L.ConstExpr
trConstExpr (S.ConstIntExpr c) = L.mkConst <$> pure (L.mkIntConst c)
trConstExpr (S.ConstBoolExpr c) = L.mkConst <$> pure (L.boolConst c)
trConstExpr (S.ConstFloatExpr c) = L.mkConst <$> pure (L.mkRealConst $ approxRational c 0.01)
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

