module Lang.LAMA.Structure.SimpIdentUntyped (
  module Lang.LAMA.Structure,
  Program,
  -- * Type definitions
  -- ** Enums
  EnumDef, EnumConstr,
  -- * Constants
  Constant,
  -- * Nodes
  Node, Variable,
  Declarations,
  -- * Data flow
  Flow,
  -- ** Definition of local and output variables
  InstantDefinition,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  LocationId, Location, Edge, Automaton,
  -- * Expressions
  Prod, Pattern,
  Atom, Expr, ConstExpr,
  -- * Constructors
  boolConst, mkIntConst, mkRealConst, constAtExpr, mkAtomVar,
  mkIte, mkLogNot, mkExpr2, mkConst,
  module Lang.LAMA.Fix
) where

import Lang.LAMA.Identifier
import qualified Lang.LAMA.UnTypedStructure as S
import Lang.LAMA.Structure
import Lang.LAMA.UnTypedStructure (boolConst, mkIntConst, mkRealConst, constAtExpr, mkAtomVar, mkIte, mkLogNot, mkExpr2, mkConst)
import Lang.LAMA.Fix

type Constant = S.Constant
type Expr = S.Expr SimpIdent
type Atom = S.Atom SimpIdent
type ConstExpr = S.ConstExpr SimpIdent

type Program = S.Program SimpIdent
type Node = S.Node SimpIdent
type Declarations = S.Declarations SimpIdent
type Flow = S.Flow SimpIdent
type InstantDefinition = S.InstantDefinition SimpIdent
type StateTransition = S.StateTransition SimpIdent
type StateInit = S.StateInit SimpIdent
type Location = S.Location SimpIdent
type Edge = S.Edge SimpIdent
type Automaton = S.Automaton SimpIdent

type EnumDef = S.EnumDef SimpIdent
type EnumConstr = S.EnumConstr SimpIdent
type Variable = S.Variable SimpIdent
type LocationId = S.LocationId SimpIdent
type Prod = S.Prod SimpIdent
type Pattern = S.Pattern SimpIdent