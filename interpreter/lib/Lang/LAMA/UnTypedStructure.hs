{-| Structure of LAMA programs without types -}
module Lang.LAMA.UnTypedStructure (
  module Lang.LAMA.Structure,
  Program,
  Constant,
  -- * Nodes
  Node,
  Declarations,
  -- * Data flow
  Flow,
  -- ** Definition of local and output variables
  InstantDefinition, Instant,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  Location, Edge, Automaton,
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

type Expr = Fix (GExpr Constant Atom)         -- ^ expression
type Atom = Fix (GAtom Constant)              -- ^ atom
type ConstExpr = Fix (GConstExpr Constant)    -- ^ constant expression

type Program = GProgram Constant Expr ConstExpr Instant
type Node = GNode Expr ConstExpr Instant
type Declarations = GDeclarations Expr ConstExpr Instant
type Flow = GFlow Expr Instant
type InstantDefinition = GInstantDefinition Instant
type Instant = Fix (GInstant Expr)
type StateTransition = GStateTransition Expr
type StateInit = GStateInit ConstExpr
type Location = GLocation Expr Instant
type Edge = GEdge Expr
type Automaton = GAutomaton Expr Instant

boolConst :: Bool -> Constant
boolConst c = Fix (BoolConst c)

constAtExpr :: Constant -> Expr
constAtExpr c = Fix (AtExpr (AtomConst c))
