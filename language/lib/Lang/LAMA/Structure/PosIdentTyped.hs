module Lang.LAMA.Structure.PosIdentTyped (
  module Lang.LAMA.Structure,
  Program,
  -- * Type definitions
  TypeDef,
  -- ** Enums
  EnumConstr, EnumT,
  -- ** Records
  RecordField, RecordT,
  -- * Constants
  Constant,
  -- * Nodes
  Node, Variable,
  Declarations,
  -- * Data flow
  Flow,
  -- ** Definition of local and output variables
  Pattern, InstantDefinition, Instant,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  LocationId, Location, Edge, Automaton,
  -- * Expressions
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

type TypeDef = GTypeDef PosIdent
type EnumConstr = GEnumConstr PosIdent
type EnumT = GEnumT PosIdent
type RecordField = GRecordField PosIdent
type RecordT = GRecordT PosIdent
type Variable = GVariable PosIdent
type Pattern = S.Pattern PosIdent
type LocationId = S.LocationId PosIdent
