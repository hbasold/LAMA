{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module TransformCommon (
  concatFlows, updateVarName, declareNode, checkNode,
  trVarDecl, trVarDecls, separateVars, trConstDecl, mkLocalAssigns,
  trTypeExpr,
  EquationRhs(..), trExpr, trExpr', trConstExpr
  ) where

import Development.Placeholders

import Prelude hiding (mapM, sequence)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Data.List (intercalate)
import Data.Ratio
import Data.Maybe (catMaybes)
import Data.Traversable (mapM, sequence)

import qualified Data.ByteString.Char8 as BS
import Text.PrettyPrint (render)

import Control.Monad (liftM)
import Control.Monad.Trans.Class
import Control.Monad.State (MonadState(..), gets, modify)
import Control.Monad.Error (MonadError(..))
import Control.Arrow ((&&&), second)
import Control.Applicative (Applicative(..), (<$>))

import qualified Language.Scade.Syntax as S
import qualified Language.Scade.Pretty as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import ExtractPackages as Extract
import TransformMonads

concatFlows :: L.Flow -> L.Flow -> L.Flow
concatFlows (L.Flow d1 s1) (L.Flow d2 s2) = L.Flow (d1 ++ d2) (s1 ++ s2)

declareNode :: (MonadState Decls m) => L.SimpIdent -> L.Node -> m ()
declareNode x n = modify (\d -> d { nodes = Map.insert x n $ nodes d })

declarePackage :: (MonadState Decls m) => L.SimpIdent -> Decls -> m ()
declarePackage x p = modify (\d -> d { packages = Map.insert x p $ packages d })

updateVarName :: (BS.ByteString -> BS.ByteString) -> L.Variable -> L.Variable
updateVarName f (L.Variable (L.SimpIdent x) t) = L.Variable (L.SimpIdent $ f x) t

checkNode :: S.Path -> TransM (L.SimpIdent, L.Type L.SimpIdent)
checkNode = getUserOperator $ \o ->
  do let n = fromString $ S.userOpName o
     nodeTranslated <- packageHasNode n
     if nodeTranslated
       then (n,) . nodeRetType <$> lookupNode n
       else return (n, opRetType o)
  where
    lookupNode nName = gets nodes >>= lookupErr ("Unknown node " ++ L.identPretty nName) nName
    nodeRetType = L.mkProductT . map L.varType . L.nodeOutputs

    opRetType (S.UserOpDecl { S.userOpReturns = rets }) = L.mkProductT . concat $ map unrollTypes rets
      where
        unrollTypes (S.VarDecl { S.varNames = vars, S.varType = t }) =
          let t' = trTypeExpr t
          in map (const t') vars

-- | Translates a variable declaration into LAMA declarations
-- together with associative lists for default expressions and
-- last initialisations.
trVarDecl :: S.VarDecl -> TransM ([L.Variable], [(L.SimpIdent,  L.Expr)], [(L.SimpIdent, Either L.ConstExpr L.Expr)])
trVarDecl (S.VarDecl xs ty defaultExpr lastExpr) =
  let xs' = map trVarId xs
      ty' = trTypeExpr ty
  in do defaultExpr' <- liftM (maybe [] repeat) . sequence $ fmap trExpr' defaultExpr
        lastExpr' <- liftM (maybe [] repeat) . sequence $ fmap tryConst lastExpr
        return $ (map (flip L.Variable ty') xs',
                  zip xs' defaultExpr',
                  zip xs' lastExpr')

trVarDecls :: [S.VarDecl] -> TransM ([L.Variable], [(L.SimpIdent,  L.Expr)], [(L.SimpIdent, Either L.ConstExpr L.Expr)])
trVarDecls decls =
  do (vs, defs, is) <- liftM unzip3 $ mapM trVarDecl decls
     return (concat vs, concat defs, concat is)

separateVars :: Set.Set L.SimpIdent -> [L.Variable] -> ([L.Variable], [L.Variable])
separateVars asState =
  foldr (\v (ls, sts) ->
          if (L.varIdent v `Set.member` asState)
          then (ls, v : sts) else (v : ls, sts))
  ([], [])

trTypeDecl :: S.TypeDecl -> (TypeAlias, Either Type L.EnumDef)
trTypeDecl = $notImplemented

trConstDecl :: S.ConstDecl -> (L.SimpIdent, L.Constant)
trConstDecl = $notImplemented

trVarId :: S.VarId -> L.SimpIdent
trVarId (S.VarId x clock probe) = fromString x

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
  | StateExpr (L.Expr, Maybe (Either L.ConstExpr L.Expr))
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
-- TODO: maybe extend 2. to expressions where this operator is
--     somewhere deep in the expression (but: where do we get the
--     init variable from???)
trExpr :: S.Expr -> TrackUsedNodes EquationRhs
trExpr expr = context expr $ case expr of 
    S.FBYExpr _ _ _ -> error "fby should have been resolved"
    S.LastExpr x -> $notImplemented
    S.BinaryExpr S.BinAfter e1 (S.UnaryExpr S.UnPre e2)
      -> StateExpr . second Just
         <$> ((,) <$> trExpr' e2 <*> tryConst e1)
    S.BinaryExpr S.BinAfter e1 e2 ->
      LocalExpr . second Just
      <$> ((,) <$> (lift $ trExpr' e2) <*> (lift $ trExpr' e1))
    S.UnaryExpr S.UnPre e ->
      StateExpr . (id &&& const Nothing) <$> (lift $ trExpr' e)
    S.ApplyExpr op es -> do
      es' <- lift $ mapM trExpr' es
      app <- trOpApply op es'
      return $ NodeExpr app
    normalExpr -> LocalExpr . (id &&& const Nothing) <$> (lift $ trExpr' normalExpr)
  where
    context e m = m `catchError`
                  (\err -> throwError $ "Translation error in expression " ++ show e ++ ": " ++ err)

trExpr' :: (MonadError String m, Applicative m) => S.Expr -> m L.Expr
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
          lift (checkNode p) >>= \(x, t) -> return (x, es, t) <* tellNode p
trOpApply _ _ = $notImplemented

trConstExpr :: (MonadError String m, Applicative m) =>  S.Expr -> m L.ConstExpr
trConstExpr (S.ConstIntExpr c) = L.mkConst <$> pure (L.mkIntConst c)
trConstExpr (S.ConstBoolExpr c) = L.mkConst <$> pure (L.boolConst c)
trConstExpr (S.ConstFloatExpr c) = L.mkConst <$> pure (L.mkRealConst $ approxRational c 0.01)
trConstExpr (S.ConstPolyIntExpr i s) = $notImplemented
trConstExpr e = throwError $ show e ++ " is not a constant."

tryConst :: (MonadError String m, Applicative m) => S.Expr -> m (Either L.ConstExpr L.Expr)
tryConst e = (liftM Left $ trConstExpr e) `catchError` (const . liftM Right $ trExpr' e)
 
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

-- | Creates the assignment for a local definitions
-- This includes all the projections for the lhs pattern,
-- if necessary. May return an intermediate variable to
-- be declared in case a pattern matching occurs.
mkLocalAssigns :: (MonadError String m) =>
                  [Maybe L.SimpIdent] -> Either L.Expr (L.SimpIdent, [L.Expr], L.Type L.SimpIdent)
                  -> m ([L.InstantDefinition], Maybe L.Variable)
mkLocalAssigns ids rhs =
  do r <- mkReturnId ids
     case r of
       Nothing -> return ([], Nothing)
       Just (x, needsMatching) ->
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
mkReturnId :: (MonadError String m) => [Maybe L.SimpIdent] -> m (Maybe (L.SimpIdent, Bool))
mkReturnId [] = throwError $ "Empty lhs in assignment not allowed"
mkReturnId [x] = return $ fmap (, False) x
mkReturnId xs =
  let xs' = catMaybes xs
  in case xs' of
    [] -> return Nothing
    _ -> return $ Just (fromString . intercalate "_" $ map L.identString xs', True)

mkProductProjections :: L.SimpIdent -> [Maybe L.SimpIdent] -> [L.InstantDefinition]
mkProductProjections from = snd . foldl (mkProj from) (0, [])
  where
    mkProj _ (i, defs) Nothing = (succ i, defs)
    mkProj x (i, defs) (Just y) =
      let project = L.mkProject x i
      in (succ i, L.InstantExpr y project : defs)