{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Transform (transform) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (fromString)

import Data.List (intercalate, unzip4)
import qualified  Data.Set as Set
import Data.Set (Set)
import qualified Data.ByteString.Char8 as BS
import Data.Ratio
import Data.List.Split (splitOn)
import Data.Maybe (maybeToList)

import Text.PrettyPrint (render)

import Control.Monad.State
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Arrow ((***), (&&&), first, second)
import Control.Applicative (Applicative(..), (<$>))
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Language.Scade.Syntax as S
import qualified Language.Scade.Pretty as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import VarGen
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

data ScadePackages = ScadePackages
                     { global :: Package
                     , current :: Package
                     } deriving Show

type PackageEnv = ReaderT ScadePackages VarGen
type TransM = StateT Decls (ErrorT String PackageEnv)

runTransM :: TransM a -> Package -> Either String (a, Decls)
runTransM m p = (flip evalVarGen 50)
                . (flip runReaderT (ScadePackages p p))
                . runErrorT
                . (flip runStateT emptyDecls)
                $ m

askGlobalPkg :: (MonadReader ScadePackages m) => m Package
askGlobalPkg = reader global

askCurrentPkg :: (MonadReader ScadePackages m) => m Package
askCurrentPkg = reader current

localPkg :: (MonadReader ScadePackages m) => (Package -> Package) -> m a -> m a
localPkg f = local (\ps -> ps { current = f $ current ps })

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

-- | Opens a package using the given reader action.
openPackage :: [String] -> TransM a -> TransM a
openPackage [] m = m
openPackage (p:ps) m =
  do scadePkg <- lookupErr ("Unknown package " ++ p) p =<< fmap pkgSubPackages askCurrentPkg
     let p' = fromString p
     pkg <- createPackage p'
     localState (updatePackage p') (const pkg)
       . localPkg (const scadePkg)
       $ openPackage ps m

-- | Checks if there is a node with the given name in the current package
packageHasNode :: L.SimpIdent -> TransM Bool
packageHasNode x = gets nodes >>= return . Map.member x

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

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

declareNode :: (MonadState Decls m) => L.SimpIdent -> L.Node -> m ()
declareNode x n = modify (\d -> d { nodes = Map.insert x n $ nodes d })

declarePackage :: (MonadState Decls m) => L.SimpIdent -> Decls -> m ()
declarePackage x p = modify (\d -> d { packages = Map.insert x p $ packages d })

mkPath :: String -> S.Path
mkPath = S.Path . splitOn "::"

transform :: String -> [S.Declaration] -> Either String L.Program
transform topNode ds =
  let ds' = Extract.extract ds
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
                       (\(x, x') ds -> (L.InstantExpr (L.varIdent x') $ L.mkAtomVar (L.varIdent x)) : ds )
                       [] $ zip outp outp'
          automata = Map.empty
      in do
        ((flow', localVars', stateVars', stateInits'), usedNodes) <-
          runWriterT $ liftM unzip4 $ mapM trEquation equations
        let flow = concatFlows flow'
            localVars = concat localVars'
            stateVars = concat stateVars'
            stateInits = Map.unions stateInits'
        -- FIXME: respect multiple points of usages!
        subNodes <- Map.fromList <$> mapM getNode (Set.toList usedNodes)
        return $ L.Node inp outp'
          (L.Declarations subNodes localVars stateVars)
          flow
          outputDefs automata stateInits

    usedNode (L.NodeUsage _ x _) = Just x
    usedNode _ = Nothing

    concatFlows :: [L.Flow] -> L.Flow
    concatFlows = foldl (\(L.Flow d1 s1) (L.Flow d2 s2) -> L.Flow (d1 ++ d2) (s1 ++ s2)) (L.Flow [] [])

trOpDecl _ = undefined

-- | Extends TransM by a writer which tracks used nodes
type TrackUsedNodes = WriterT (Set S.Path) TransM

tellNode :: MonadWriter (Set S.Path) m => S.Path -> m ()
tellNode = tell . Set.singleton

-- | Gives back either a set of definitions which is
-- a single assignment in case the given equation is a
-- simple expression. If the given equation is the using
-- of a node with multiple return values this set of
-- definitions consists of the call to the node and
-- a projection for each variable. In that case also
-- a set of intermediate variables to be declared is returned.
trEquation :: S.Equation
              -> TrackUsedNodes (L.Flow, [L.Variable], [L.Variable], L.StateInit)
trEquation (S.SimpleEquation lhsIds expr) = do
  let ids = map trLhsId lhsIds
  rhs <- trExpr expr
  case rhs of
    LocalExpr (expr', stateInit) -> case stateInit of
      -- Simple expression, no initialisation -> only do pattern matching
      Nothing -> mkLocalAssigns ids (Left expr') >>= \(a, v) -> return (L.Flow a [], maybeToList v, [], Map.empty)
      -- If we get a non-state expression with an initialisation, we
      -- introduce a stream that is true only in the first step and
      -- use that to derive the initialisation.
      Just i ->
        do init <- fmap fromString $ newVar "init"
           let expr'' = L.mkIte (L.mkAtomVar init) i expr'
               initTrans = L.StateTransition init (L.constAtExpr $ L.boolConst False)
               initInit = L.mkConst $ L.boolConst True
           (a, v) <- mkLocalAssigns ids (Left expr'')
           return (L.Flow a [initTrans], maybeToList v, [L.Variable init L.boolT], Map.singleton init initInit)
    StateExpr (expr', stateInit) -> case ids of
      [x] ->
        let i = fmap (x,) $ maybeToList stateInit
        in return (L.Flow [] [L.StateTransition x expr'], [], [], Map.fromList i)
      _ -> throwError $ "Cannot pattern match in state equation"
    NodeExpr rhs ->
      mkLocalAssigns ids (Right rhs) >>= \(a, v) ->
      return (L.Flow a [], maybeToList v, [], Map.empty)

trEquation (S.AssertEquation aType name expr) = $notImplemented
trEquation (S.EmitEquation body) = $notImplemented
trEquation (S.StateEquation sm ret returnsAll) = $notImplemented
trEquation (S.ClockedEquation name block ret returnsAll) = $notImplemented

-- | Creates the assignment for a local definitions
-- This includes all the projections for the lhs pattern,
-- if necessary. May return an intermediate variable to
-- be declared in case a pattern matching occurs.
mkLocalAssigns :: (MonadError String m) =>
                  [L.SimpIdent] -> Either L.Expr (L.SimpIdent, [L.Expr], L.Type L.SimpIdent)
                  -> m ([L.InstantDefinition], Maybe L.Variable)
mkLocalAssigns ids rhs =
  do (x, needsMatching) <- mkReturnId ids
     if needsMatching
       then case rhs of
         Left _ -> throwError $ "Pattern matching only for node expressions allowed"
         Right (n, exprs', retType) ->
           return
           ((L.NodeUsage x n exprs') : (mkProductProjections x ids),
            Just $ L.Variable x retType)
       else case rhs of
         Left expr' -> return ([L.InstantExpr x expr'], Nothing)
         Right (n, exprs', _) -> return ([L.NodeUsage x n exprs'], Nothing)

-- | Generates an identifier for the lhs of an
-- assignment. If the given list has only one element,
-- this is used and no further matching is required.
-- Otherwise matching is required (snd == True).
mkReturnId :: (MonadError String m) => [L.SimpIdent] -> m (L.SimpIdent, Bool)
mkReturnId [] = throwError $ "Empty lhs in assignment not allowed"
mkReturnId [x] = return (x, False)
mkReturnId xs = return (fromString . intercalate "_" $ map L.identString xs, True)

mkProductProjections :: L.SimpIdent -> [L.SimpIdent] -> [L.InstantDefinition]
mkProductProjections from = snd . foldl (mkProj from) (0, [])
  where
    mkProj x (i, defs) y =
      let project = L.mkProject x i
      in (succ i, L.InstantExpr y project : defs)

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


data EquationRhs =
  LocalExpr (L.Expr, Maybe L.Expr)
  -- ^ An expression for a local definition together with a possible initialisation
  | StateExpr (L.Expr, Maybe L.ConstExpr)
    -- ^ An expression for a state transition together with a possible initialisation
  | NodeExpr (L.SimpIdent, [L.Expr], L.Type L.SimpIdent)
    -- ^ Using of a node

-- | There are three supported types of temporal expressions whereby the
-- first is an optimization. We give the intended translation each of them.
-- 1. (initialised pre)
--   x = i -> pre e
--   ~> x' = e, x(0) = i
-- 2. (unmatched initialisation)
--   x = i -> e, e /= pre e_
--   ~> x = (ite init i e),
--      init' = false, init(0) = true
-- 3. (unmatched pre)
--   x = e, Pre(e) = {e_1, .., e_k} /= ∅
--   ~> x = e[x_1/e_1, .., x_k/e_k],
--      x_1' = e_1, x_1(0) = ⊥
--      ...
--      x_k' = e_k, x_k(0) = ⊥
-- ⊥ stands for an unknown value and is realised by just leaving it open.
-- If all accessed streams are well initialised, this should be fine.
--
-- Other temporal expressions like fby have to be unrolled beforehand.
trExpr :: S.Expr -> TrackUsedNodes EquationRhs
trExpr expr = case expr of 
    S.FBYExpr _ _ _ -> error "fby should have been resolved"
    S.LastExpr x -> $notImplemented
    S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)
      -> StateExpr . second Just
         <$> ((,) <$> trExpr' e2 <*> lift (trConstExpr e1))
    S.BinaryExpr S.BinAfter e1 e2 ->
      LocalExpr . second Just
      <$> ((,) <$> trExpr' e2 <*> trExpr' e1)
    S.UnaryExpr S.UnPre e ->
      StateExpr . (id &&& const Nothing) <$> trExpr' e
    S.ApplyExpr op es -> do
      es' <- mapM trExpr' es
      app <- trOpApply op es'
      return $ NodeExpr app
    normalExpr -> LocalExpr . (id &&& const Nothing) <$> trExpr' normalExpr
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
    trExpr' e@(S.UnaryExpr S.UnPre _) = error $ "pre should be erased in preprocessing " ++ (render $ S.prettyExpr 0 e)
    trExpr' (S.UnaryExpr S.UnNeg e) = $notImplemented
    trExpr' (S.UnaryExpr S.UnCastInt e) = $notImplemented
    trExpr' (S.UnaryExpr S.UnCastReal e) = $notImplemented
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
    trExpr' e = error $ "trExpr: should have been resolved in preprocessing: " ++ show e

trOpApply :: S.Operator -> [L.Expr] -> TrackUsedNodes (L.SimpIdent, [L.Expr], L.Type L.SimpIdent)
trOpApply (S.PrefixOp (S.PrefixPath p)) es =
          lift (getNode p) >>= \(x, n) -> return (x, es, nodeRetType n) <* tellNode p
  where nodeRetType = L.mkProductT . map L.varType . L.nodeOutputs
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
trBinOp S.BinAfter = error "After should no longer occur as single operator"
trBinOp S.BinAnd = L.And
trBinOp S.BinOr = L.Or
trBinOp S.BinXor = L.Xor
trBinOp S.BinPower = $notImplemented

