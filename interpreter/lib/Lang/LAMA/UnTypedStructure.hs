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
  InstantDefinition,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  Location, Edge, Automaton,
  -- * Expressions
  Atom, Expr, ConstExpr,
  module Lang.LAMA.Fix
) where

import Lang.LAMA.Structure
import Lang.LAMA.Fix

-- | Constants
type Constant = Fix GConst

type Expr = Fix (GExpr Constant Atom)         -- ^ expression
type Atom = Fix (GAtom Constant)              -- ^ atom
type ConstExpr = Fix (GConstExpr Constant)    -- ^ constant expression

type Program = GProgram Constant Expr ConstExpr
type Node = GNode Expr ConstExpr
type Declarations = GDeclarations Expr ConstExpr
type Flow = GFlow Expr
type InstantDefinition = GInstantDefinition Expr
type StateTransition = GStateTransition Expr
type StateInit = GStateInit ConstExpr
type Location = GLocation Expr
type Edge = GEdge Expr
type Automaton = GAutomaton Expr


