{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module TransformSimple (trSimpleEquation) where

import Development.Placeholders

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Data.Maybe (maybeToList)
import Data.Monoid

import Control.Monad (liftM)
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
        return $ (baseEq $ L.Flow a []) { trEqLocalVars = (maybeToList v) }
      -- If we get a non-state expression with an initialisation, we
      -- introduce a stream that is true only in the first step and
      -- use that to derive the initialisation.
      Just i ->
        do (expr'', initVar, initFlow, stateInits) <- mkInit i expr'
           (a, v) <- mkLocalAssigns ids (Left expr'')
           return $
             (baseEq $ (L.Flow a []) `mappend` initFlow) {
               trEqLocalVars = (maybeToList v)
               , trEqStateVars = [initVar]
               , trEqInits = stateInits }
    StateExpr (expr', stateInit) -> case ids of
      [Nothing] -> $notImplemented
      [Just x] ->
        -- There are several possibilities for initialisation:
        -- * no initialisation -> we generate nothing more
        -- * constant initialisation -> we use the system of LAMA
        -- * non-constant init -> we generate a guarded expression
        case stateInit of
          Nothing -> return $ (baseEq $ L.Flow [] [L.StateTransition x expr']) { trEqAsState = Set.singleton x }
          Just (Left i) -> return $
                           (baseEq $ L.Flow [] [L.StateTransition x expr']) {
                             trEqInits = Map.singleton x i
                             , trEqAsState = Set.singleton x }
          Just (Right ie) ->
            do (expr'', initVar, initFlow, stateInits) <- mkInit ie expr'
               return $
                 (baseEq $ (L.Flow [] [L.StateTransition x expr'']) `mappend` initFlow) {
                   trEqStateVars = [initVar]
                   , trEqInits = stateInits
                   , trEqAsState = Set.singleton x }
      _ -> throwError $ "Cannot pattern match in state equation"
    NodeExpr rhs ->
      mkLocalAssigns ids (Right rhs) >>= \(a, v) ->
      return $ (baseEq $ L.Flow a []) { trEqLocalVars = maybeToList v }
  where
    -- If we get a non-state expression with an initialisation, we
    -- introduce a stream that is true only in the first step and
    -- use that to derive the initialisation.
    mkInit :: MonadVarGen m => L.Expr -> L.Expr -> m (L.Expr, L.Variable, L.Flow, L.StateInit)
    mkInit i expr =
      do init <- liftM fromString $ newVar "init"
         let expr' = L.mkIte (L.mkAtomVar init) i expr
             initTrans = L.StateTransition init (L.constAtExpr $ L.boolConst False)
             initInit = L.mkConst $ L.boolConst True
         return (expr', L.Variable init L.boolT, L.Flow [] [initTrans], Map.singleton init initInit)


trLhsId :: S.LHSId -> Maybe L.SimpIdent
trLhsId (S.Named x) = Just $ fromString x
trLhsId S.Bottom = Nothing