module Lang.LAMA.Structure.PosIdentUntyped (
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
  boolConst, constAtExpr,
  module Lang.LAMA.Fix
) where

import Lang.LAMA.Identifier
import qualified Lang.LAMA.UnTypedStructure as S
import Lang.LAMA.Structure
import Lang.LAMA.UnTypedStructure (boolConst, constAtExpr)
import Lang.LAMA.Fix

type Constant = S.Constant
type Expr = S.Expr PosIdent
type Atom = S.Atom PosIdent
type ConstExpr = S.ConstExpr PosIdent

type Program = S.Program PosIdent
type Node = S.Node PosIdent
type Declarations = S.Declarations PosIdent
type Flow = S.Flow PosIdent
type InstantDefinition = S.InstantDefinition PosIdent
type StateTransition = S.StateTransition PosIdent
type StateInit = S.StateInit PosIdent
type Location = S.Location PosIdent
type Edge = S.Edge PosIdent
type Automaton = S.Automaton PosIdent

type EnumDef = S.EnumDef PosIdent
type EnumConstr = S.EnumConstr PosIdent
type Variable = S.Variable PosIdent
type LocationId = S.LocationId PosIdent
type Prod = S.Prod PosIdent
type Pattern = S.Pattern PosIdent