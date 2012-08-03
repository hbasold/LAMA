{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module TransformSimple (trSimpleEquation) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.String (fromString)
import Data.Maybe (maybeToList)

import Control.Monad.Error (MonadError(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import VarGen
import TransformMonads
import TrEquation
import TransformCommon

trSimpleEquation :: [S.LHSId] -> S.Expr -> TrackUsedNodes (TrEquation L.Flow)
trSimpleEquation lhsIds expr = do
  let ids = map trLhsId lhsIds
  rhs <- trExpr expr
  case rhs of
    LocalExpr (expr', stateInit) -> case stateInit of
      -- Simple expression, no initialisation -> only do pattern matching
      Nothing -> mkLocalAssigns ids (Left expr') >>= \(a, v) ->
        return $ TrEquation (L.Flow a []) (maybeToList v)  [] Map.empty []
      -- If we get a non-state expression with an initialisation, we
      -- introduce a stream that is true only in the first step and
      -- use that to derive the initialisation.
      Just i ->
        do init <- fmap fromString $ newVar "init"
           let expr'' = L.mkIte (L.mkAtomVar init) i expr'
               initTrans = L.StateTransition init (L.constAtExpr $ L.boolConst False)
               initInit = L.mkConst $ L.boolConst True
           (a, v) <- mkLocalAssigns ids (Left expr'')
           return $ TrEquation (L.Flow a [initTrans])
             (maybeToList v) [L.Variable init L.boolT]
             (Map.singleton init initInit) []
    StateExpr (expr', stateInit) -> case ids of
      [x] ->
        let i = fmap (x,) $ maybeToList stateInit
        in return $ TrEquation (L.Flow [] [L.StateTransition x expr']) [] [] (Map.fromList i) []
      _ -> throwError $ "Cannot pattern match in state equation"
    NodeExpr rhs ->
      mkLocalAssigns ids (Right rhs) >>= \(a, v) ->
      return $ TrEquation (L.Flow a []) (maybeToList v) [] Map.empty []

trLhsId :: S.LHSId -> L.SimpIdent
trLhsId (S.Named x) = fromString x
trLhsId S.Bottom = $notImplemented