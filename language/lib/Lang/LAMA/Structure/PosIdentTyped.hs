module Lang.LAMA.Structure.PosIdentTyped (
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
  InstantDefinition, Instant,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  LocationId, Location, Edge, Automaton,
  -- * Expressions
  Prod, Array, Pattern, PatHead,
  Atom, Expr, ConstExpr,
  -- * Constructors
  boolConst, constAtExpr
) where

import Lang.LAMA.Identifier
import qualified Lang.LAMA.Typing.TypedStructure as S
import Lang.LAMA.Structure
import Lang.LAMA.Typing.TypedStructure (boolConst, constAtExpr)

type Constant = S.Constant PosIdent
type Expr = S.Expr PosIdent
type Atom = S.Atom PosIdent
type ConstExpr = S.ConstExpr PosIdent

type Program = S.Program PosIdent
type Node = S.Node PosIdent
type Declarations = S.Declarations PosIdent
type Flow = S.Flow PosIdent
type InstantDefinition = S.InstantDefinition PosIdent
type Instant = S.Instant PosIdent
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
type Array = S.Array PosIdent
type Pattern = S.Pattern PosIdent
type PatHead = S.PatHead PosIdent
