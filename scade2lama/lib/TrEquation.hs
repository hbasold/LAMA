module TrEquation where

import qualified Data.Map as Map

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
                    , trEqPrecond :: [L.Expr]
                    } deriving Show

baseEq :: a -> TrEquation a
baseEq x = TrEquation x [] [] Map.empty [] []

data TrEqCont =
  SimpleEq L.Flow
  | AutomatonEq L.Automaton [L.Variable]
    -- ^ An automaton has a potential name, the automaton itself
    -- and locally declared variables (in the states).
  | NonExecutable -- ^ Content which does not produce any values (like preconditions)
  deriving Show

instance Functor TrEquation where
  fmap f = \(TrEquation x l s i a p) -> TrEquation (f x) l s i a p

foldlTrEq :: (b -> a -> b) -> b -> [TrEquation a] -> TrEquation b
foldlTrEq f i = foldl f' (TrEquation i [] [] Map.empty [] [])
  where
    f' (TrEquation b l1 s1 i1 n1 p1) (TrEquation a l2 s2 i2 n2 p2) =
      TrEquation (f b a)
      (l1 ++ l2) (s1 ++ s2)
      (i1 `Map.union` i2) (n1 ++ n2) (p1 ++ p2)

mergeTrEqs :: [TrEquation a] -> TrEquation [a]
mergeTrEqs = foldlTrEq (\eqs eq -> eqs ++ [eq]) []
