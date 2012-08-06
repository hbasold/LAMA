{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module RewriteClockedEquation where

import Development.Placeholders

import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad (liftM)
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.Writer (MonadWriter(..), WriterT(..))
import Control.Arrow ((|||), (+++))
import Control.Wrapping

import Language.Scade.Syntax as S

import Options
import VarGen

rewrite :: (MonadReader Options m, MonadVarGen m) => [Declaration] -> m [Declaration]
rewrite decls =
  do asAutom <- asks optClockAsAutomaton
     let tr = if asAutom
              then everywhereM (mkM toSM)
              else everywhereM (mkM toIf)
     tr decls

toSM :: MonadVarGen m => Equation -> m Equation
toSM (ClockedEquation name block ret returnsAll) =
  let block' = (flattenIf +++ id) block
  in do block'' <- faninM (ifBlockSM name) (matchBlockSM name) block'
        return $ StateEquation block'' ret returnsAll
toSM e = return e

flattenIf :: IfBlock -> IfBlock
flattenIf (IfBlock cond b1 r) =
  let b1' = (id +++ flattenIf) b1
      r' = (id +++ flattenIf) r
  in case b1' of
    Right ifB -> mergeIf cond r' ifB
    Left _ -> IfBlock cond b1' r'
  where
    mergeIf :: Expr -> Either DataDef IfBlock -> IfBlock -> IfBlock
    -- if c1 then (if c2 (if ...) r2) r1
    -- ~> if c1 and c2 and ... then ... else if c2 r2 else r1
    mergeIf c1 r1 (IfBlock c2 (Right b2) r2) =
      let c = BinaryExpr BinAnd c1 c2
          (IfBlock c2' b _r2') = mergeIf c r2 b2
      in IfBlock c2' b $ Right (IfBlock c2 r2 r1)
    -- if c1 then (if c2 then e else r2) else r1
    -- ~> if c1 and c2 then e else if c1 then r2 else r1
    mergeIf c1 r1 (IfBlock c2 (Left def) r2) =
      IfBlock (BinaryExpr BinAnd c1 c2) (Left def)
      $ Right (IfBlock c1 r2 r1)

ifBlockSM :: MonadVarGen m => Maybe String -> IfBlock -> m StateMachine
ifBlockSM blockName block = liftM (StateMachine blockName) $ mkIfStates block

-- | Translate if chain into automaton. Normally one would construct
-- first a Mealy automaton (which we could do) where the definitions would be
-- on the transitions and then convert that into a Moore automaton. We do
-- that for now in one go. Later when, actions on transitions are supported,
-- we use actions on transitions.
mkIfStates :: MonadVarGen m => IfBlock -> m [State]
mkIfStates = mkIfStates' []
  where
    -- the transitions differ only in the head state so we can build them
    -- top-down
    mkIfStates' :: MonadVarGen m => [Transition] -> IfBlock -> m [State]
    mkIfStates' ts (IfBlock cond (Left d1) (Left d2)) =
      do s0Name <- newVar "ifState"
         s1Name <- newVar "ifState"
         let t0 = Transition (ConstBoolExpr True) Nothing (TargetFork Resume s0Name)
             t1 = Transition cond Nothing (TargetFork Resume s1Name)
             ts' = ts ++ [t1, t0]
             s0 = State True False s0Name d2 ts' [] Nothing
             s1 = State False False s1Name d1 ts' [] Nothing
         return [s1, s0]
    mkIfStates' ts (IfBlock cond (Left d) (Right r)) =
      do sName <- newVar "ifState"
         let t = Transition cond Nothing (TargetFork Resume sName)
             ts' = ts ++ [t]
         sts <- mkIfStates' ts' r         
         let (State _ _ _ _ ts'' _ _) = head sts 
             s = State False False sName d ts'' [] Nothing
         return $ s : sts
    mkIfStates' _ (IfBlock _ (Right _) _) = error "mkIfStates: should have been flattened"

matchBlockSM :: MonadVarGen m => Maybe String -> MatchBlock -> m StateMachine
matchBlockSM = $notImplemented

toIf :: MonadVarGen m => DataDef -> m DataDef
toIf def =
  do (eqs', vars) <- runWriterT . mapM toIfEq $ dataEquations def
     return $ def { dataLocals = dataLocals def ++ vars
                  , dataEquations = concat eqs' }

toIfEq :: MonadVarGen m => Equation -> WriterT [VarDecl] m [Equation]
toIfEq (ClockedEquation _name block ret returnsAll) =
  faninM ifBlockIf matchBlockIf block
toIfEq e = return [e]

ifBlockIf :: IfBlock -> WriterT [VarDecl] m [Equation]
ifBlockIf (IfBlock cond (Left def) elseBlock) = $notImplemented
ifBlockIf (IfBlock _ (Right _) _) = error "ifBlockIf: should have been flattened"

matchBlockIf :: MatchBlock -> WriterT [VarDecl] m [Equation]
matchBlockIf = $notImplemented
