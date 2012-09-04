{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module TransformSimple (trSimpleEquation) where

import Development.Placeholders

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Data.Maybe (maybeToList)
import Control.Monad.Error (MonadError(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L

import TransformMonads
import TrEquation
import TransformCommon

-- | Translates a simple assignment. This returns either a simple flow
-- or an automaton if the equation needs some initialisation.
trSimpleEquation :: [S.LHSId] -> S.Expr -> TrackUsedNodes (TrEquation (Either L.Flow (L.Flow, L.Flow)))
trSimpleEquation lhsIds expr = do
  let ids = map trLhsId lhsIds
  rhs <- trExpr expr
  case rhs of
    LocalExpr (expr', stateInit) -> case stateInit of
      -- Simple expression, no initialisation -> only do pattern matching
      Nothing -> mkLocalAssigns ids (Left expr') >>= \(a, v) ->
        return $ (baseEq $ Left $ L.Flow a []) { trEqLocalVars = (maybeToList v) }

      -- If we get a non-state expression with an initialisation, we
      -- introduce an automaton which has three states:
      -- one state which is initial and has a epsilon transition to
      -- a state which initialises the variable. The last state contains
      -- the corresponding flow. We call them "dummy", "init" and "running".
      Just i ->
        do (defsI, v1) <- mkLocalAssigns ids (Left i)
           (defsExpr, v2) <- mkLocalAssigns ids (Left expr')
           return $ (baseEq $ Right (L.Flow defsI [], L.Flow defsExpr [])){
             trEqLocalVars = maybeToList v1 ++ maybeToList v2 }
    StateExpr (expr', stateInit) -> case ids of
      [Nothing] -> $notImplemented
      [Just x] ->
        -- There are several possibilities for initialisation:
        -- * no initialisation -> we generate nothing more
        -- * constant initialisation -> we use the system of LAMA
        -- * non-constant init -> we generate an initialisation automaton
        case stateInit of
          Nothing -> return $ (baseEq $ Left $ L.Flow [] [L.StateTransition x expr']) { trEqAsState = Set.singleton x }
          Just (Left i) -> return $
                           (baseEq $ Left $ L.Flow [] [L.StateTransition x expr']) {
                             trEqInits = Map.singleton x i
                             , trEqAsState = Set.singleton x }
          Just (Right ie) ->
            let initFlow = L.Flow [] [L.StateTransition x ie]
                defFlow = L.Flow [] [L.StateTransition x expr']
            in return $ (baseEq $ Right (initFlow, defFlow)) { trEqAsState = Set.singleton x }
      _ -> throwError $ "Cannot pattern match in state equation"
    NodeExpr rhs ->
      mkLocalAssigns ids (Right rhs) >>= \(a, v) ->
      return $ (baseEq $ Left $ L.Flow a []) { trEqLocalVars = maybeToList v }

trLhsId :: S.LHSId -> Maybe L.SimpIdent
trLhsId (S.Named x) = Just $ fromString x
trLhsId S.Bottom = Nothing