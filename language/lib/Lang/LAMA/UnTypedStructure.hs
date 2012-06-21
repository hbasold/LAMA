{-| Structure of LAMA programs without types -}
module Lang.LAMA.UnTypedStructure (
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
  boolConst, constAtExpr,
  module Lang.LAMA.Fix
) where

import Lang.LAMA.Structure
import Lang.LAMA.Fix

-- | Constants
type Constant = Fix GConst

type Expr i = Fix (GExpr i Constant (Atom i))         -- ^ expression
type Atom i = Fix (GAtom i Constant)              -- ^ atom
type ConstExpr i = Fix (GConstExpr i Constant)    -- ^ constant expression

type Program i = GProgram i Constant (Expr i) (ConstExpr i) (Instant i)
type Node i = GNode i (Expr i) (ConstExpr i) (Instant i)
type Declarations i = GDeclarations i (Expr i) (ConstExpr i) (Instant i)
type Flow i = GFlow i (Expr i) (Instant i)
type InstantDefinition i = GInstantDefinition i (Instant i)
type Instant i = Fix (GInstant i (Expr i))
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

boolConst :: Bool -> Constant
boolConst c = Fix (BoolConst c)

constAtExpr :: Constant -> Expr i
constAtExpr c = Fix (AtExpr (AtomConst c))
