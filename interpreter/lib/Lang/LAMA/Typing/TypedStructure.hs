{-| Structure of LAMA programs with types -}
module Lang.LAMA.Typing.TypedStructure (
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
  Atom, Expr, ConstExpr
) where

import Lang.LAMA.Structure
import Lang.LAMA.Types

-- | Typed constant
type Constant = Typed GConst

-- $untyped-doc
-- The parameter /e/ of the untyped expressions
-- is replaced by the typed variant of themselves
-- by 'Typed'. So 'Typed' builds up a fix point type.

type Expr = Typed (GExpr Constant Atom)             -- ^ Typed expression
type Atom = Typed (GAtom Constant)             -- ^ Typed atom
type ConstExpr = Typed (GConstExpr Constant)   -- ^ Typed constant expression

type Program = GProgram Constant Expr ConstExpr Instant
type Node = GNode Expr ConstExpr Instant
type Declarations = GDeclarations Expr ConstExpr Instant
type Flow = GFlow Expr Instant
type InstantDefinition = GInstantDefinition Instant
type Instant = Typed (GInstant Expr)
type StateTransition = GStateTransition Expr
type StateInit = GStateInit ConstExpr
type Location = GLocation Expr Instant
type Edge = GEdge Expr
type Automaton = GAutomaton Expr Instant
