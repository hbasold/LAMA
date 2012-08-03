{-# LANGUAGE TypeSynonymInstances #-}
module TrEquation where

import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L

-- An equation has a content and set of local and state variables
-- together with the initialisation of the state variables.
data TrEquation a = TrEquation
                    { trEqRhs :: a -- ^ Translated rhs of an equation
                    , trEqLocalVars :: [L.Variable] -- ^ Local variables to be declared
                    , trEqStateVars :: [L.Variable] -- ^ State variables to be declared
                    , trEqInits :: L.StateInit -- ^ Initialisation of state variables
                    , trEqSubAutom :: [(L.SimpIdent, L.Node)]
                      -- ^ Nodes containing subautomata for state equations
                    }
data TrEqCont =
  SimpleEq L.Flow
  | AutomatonEq L.Automaton

instance Functor TrEquation where
  fmap f = \(TrEquation x l s i a) -> TrEquation (f x) l s i a