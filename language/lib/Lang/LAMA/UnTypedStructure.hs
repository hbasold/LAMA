{-| Structure of LAMA programs without types -}
module Lang.LAMA.UnTypedStructure (
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
  boolConst, mkIntConst, mkRealConst, constAtExpr, mkAtomVar,
  mkInstantExpr, mkNodeUsage, mkIte, mkLogNot, mkExpr2, mkConst,
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

type EnumDef i = GEnumDef i
type EnumConstr i = GEnumConstr i
type Variable i = GVariable i
type LocationId i = GLocationId i
type Prod i = GProd (Expr i)
type Array i = GArray (Expr i)
type Pattern i = GPattern i (Expr i)
type PatHead i = GPatHead i

boolConst :: Bool -> Constant
boolConst = Fix . BoolConst

mkIntConst :: Integer -> Constant
mkIntConst = Fix . IntConst

mkRealConst :: Rational -> Constant
mkRealConst = Fix . RealConst

constAtExpr :: Constant -> Expr i
constAtExpr c = Fix (AtExpr (AtomConst c))

mkAtomVar :: i -> Expr i
mkAtomVar = Fix . AtExpr . AtomVar

mkInstantExpr :: Expr i -> Instant i
mkInstantExpr = Fix . InstantExpr

mkNodeUsage :: i -> [Expr i] -> Instant i
mkNodeUsage x = Fix . NodeUsage x

mkIte :: Expr i -> Expr i -> Expr i -> Expr i
mkIte c e1 = Fix . Ite c e1

mkLogNot :: Expr i -> Expr i
mkLogNot = Fix . LogNot

mkExpr2 :: BinOp -> Expr i -> Expr i -> Expr i
mkExpr2 o e1 = Fix . Expr2 o e1

mkConst :: Constant -> ConstExpr i
mkConst = Fix . Const
