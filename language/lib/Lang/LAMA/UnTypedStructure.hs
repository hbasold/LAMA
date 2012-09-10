{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
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
  InstantDefinition,
  -- ** Definition of state variables
  StateTransition, StateInit,
  -- * Automata
  LocationId, Location, Edge, Automaton,
  -- * Expressions
  Prod, PatternHead, Pattern,
  Atom, Expr, ConstExpr,
  -- * Constructors
  boolConst, mkIntConst, mkRealConst, constAtExpr, mkAtomVar,
  mkIte, mkLogNot, mkExpr2, mkProject, mkConst,
  module Lang.LAMA.Fix
) where

import Data.Natural
import Lang.LAMA.Structure
import Lang.LAMA.Fix
import Lang.LAMA.Identifier

-- | Constants
type Constant = Fix GConst

type Expr i = Fix (GExpr i Constant (Atom i))         -- ^ expression
type Atom i = Fix (GAtom i Constant)              -- ^ atom
type ConstExpr i = Fix (GConstExpr i Constant)    -- ^ constant expression

type Program i = GProgram i Constant (Expr i) (ConstExpr i)
type Node i = GNode i (Expr i) (ConstExpr i)
type Declarations i = GDeclarations i (Expr i) (ConstExpr i)
type Flow i = GFlow i (Expr i)
type InstantDefinition i = GInstantDefinition i (Expr i)
type StateTransition i = GStateTransition i (Expr i)
type StateInit i = GStateInit i (ConstExpr i)
type Location i = GLocation i (Expr i)
type Edge i = GEdge i (Expr i)
type Automaton i = GAutomaton i (Expr i)

type EnumDef i = GEnumDef i
type EnumConstr i = GEnumConstr i
type Variable i = GVariable i
type LocationId i = GLocationId i
type Prod i = GProd (Expr i)
type PatternHead i = GPatternHead i
type Pattern i = GPattern i (Expr i)

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

mkIte :: Expr i -> Expr i -> Expr i -> Expr i
mkIte c e1 = Fix . Ite c e1

mkLogNot :: Expr i -> Expr i
mkLogNot = Fix . LogNot

mkExpr2 :: BinOp -> Expr i -> Expr i -> Expr i
mkExpr2 o e1 = Fix . Expr2 o e1

mkProject :: i -> Natural -> Expr i
mkProject x = Fix . Project x

mkConst :: Constant -> ConstExpr i
mkConst = Fix . Const

instance Ident i => ViewExpr i (Expr i) Constant (Atom i) where
  viewExpr = unfix

instance Ident i => PackedExpr i (Expr i) Constant (Atom i) where
  packExpr = Fix

instance ViewConst Constant where
  viewConst = unfix

instance PackedConst Constant where
  packConst = Fix