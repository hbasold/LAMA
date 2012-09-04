module TrEquation where

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid

import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L

-- | Represents the result of a translation of an equation.
-- In consists what has been produced as immediate rhs and
-- what has to be put into or changed in the surrounding scope.
data TrEquation a = TrEquation
                    { trEqRhs :: a -- ^ Translated rhs of an equation
                    , trEqLocalVars :: [L.Variable] -- ^ Local variables to be declared
                    , trEqStateVars :: [L.Variable] -- ^ State variables to be declared
                    , trEqInits :: L.StateInit -- ^ Initialisation of state variables
                    , trEqSubAutom :: [(L.SimpIdent, L.Node)]
                      -- ^ Nodes containing subautomata for state equations
                    , trEqPrecond :: [L.Expr]
                    , trEqAsState :: Set L.SimpIdent
                      -- ^ Used variables which have to become state variables
                    } deriving Show

baseEq :: a -> TrEquation a
baseEq x = TrEquation x [] [] Map.empty [] [] Set.empty

data TrEqCont =
  SimpleEq L.Flow
  | InitEq (L.Flow, L.Flow)
    -- ^ An equation with an initialisation has two flows:
    -- one for the initialisation and one for the "true" definition.
  | AutomatonEq L.Automaton [L.Variable] L.Flow
    -- ^ An automaton has additionally locally declared variables (in the states)
    -- and a flow for the conditions of weak transitions.
  | NonExecutable -- ^ Content which does not produce any values (like preconditions)
  deriving Show

instance Functor TrEquation where
  fmap f = \(TrEquation x l s i a p asS) -> TrEquation (f x) l s i a p asS

foldlTrEq :: (b -> a -> b) -> b -> [TrEquation a] -> TrEquation b
foldlTrEq f i = foldl f' $ baseEq i
  where
    f' (TrEquation b l1 s1 i1 n1 p1 asS1) (TrEquation a l2 s2 i2 n2 p2 asS2) =
      TrEquation (f b a)
      (l1 ++ l2) (s1 ++ s2)
      (i1 `Map.union` i2) (n1 ++ n2) (p1 ++ p2) (asS1 `mappend` asS2)

mergeTrEqs :: [TrEquation a] -> TrEquation [a]
mergeTrEqs = foldlTrEq (\eqs eq -> eqs ++ [eq]) []
