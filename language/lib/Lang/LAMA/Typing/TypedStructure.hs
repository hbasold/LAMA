{-| Structure of LAMA programs with types -}
module Lang.LAMA.Typing.TypedStructure (
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

import Lang.LAMA.Structure
import Lang.LAMA.Types

-- | Typed constant
type Constant i = Typed i GConst

-- $untyped-doc
-- The parameter /e/ of the untyped expressions
-- is replaced by the typed variant of themselves
-- by 'Typed'. So 'Typed' builds up a fix point type.

type Expr i = Typed i (GExpr i (Constant i) (Atom i))             -- ^ Typed expression
type Atom i = Typed i (GAtom i (Constant i))             -- ^ Typed atom
type ConstExpr i = Typed i (GConstExpr i (Constant i))   -- ^ Typed constant expression

type Program i = GProgram i (Constant i) (Expr i) (ConstExpr i) (Instant i)
type Node i = GNode i (Expr i) (ConstExpr i) (Instant i)
type Declarations i = GDeclarations i (Expr i) (ConstExpr i) (Instant i)
type Flow i = GFlow i (Expr i) (Instant i)
type InstantDefinition i = GInstantDefinition i (Instant i)
type Instant i = Typed i (GInstant i (Expr i))
type StateTransition i = GStateTransition i (Expr i)
type StateInit i = GStateInit i (ConstExpr i)
type Location i = GLocation i (Expr i) (Instant i)
type Edge i = GEdge i (Expr i)
type Automaton i = GAutomaton i (Expr i) (Instant i)

type TypeDef i = GTypeDef i
type EnumConstr i = GEnumConstr i
type EnumT i = GEnumT i
type RecordField i = GRecordField i
type RecordT i = GRecordT i
type Variable i = GVariable i
type Pattern i = GPattern i
type LocationId i = GLocationId i

boolConst :: Bool -> Constant i
boolConst c = mkTyped (BoolConst c) boolT

constAtExpr :: Constant i -> Expr i
constAtExpr c = mkTyped (AtExpr (AtomConst c)) (getType c)
