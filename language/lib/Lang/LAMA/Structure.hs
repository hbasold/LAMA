{-# LANGUAGE DeriveDataTypeable #-}
{-| Structure of LAMA programs -}
module Lang.LAMA.Structure (
  GProgram(..),
  -- * Type definitions
  -- ** Enums
  GEnumDef(..), GEnumConstr(..),
  -- * Constants
  GConst(..),
  -- * Nodes
  GNode(..), GVariable(..), varIdent, varType, GDeclarations(..),
  -- * Data flow
  GFlow(..),
  -- ** Definition of local and output variables
  GInstantDefinition(..),
  -- ** Definition of state variables
  GStateTransition(..), GStateInit,
  -- * Automata
  GLocationId, GLocation(..), GEdge(..), GAutomaton(..),
  -- * Expressions
  -- ** Untyped expressions
  -- $untyped-doc
  GProd(..), GPatternHead(..), GPattern(..),
  GAtom(..), GExpr(..), GConstExpr(..), BinOp(..)
) where

import Data.Natural
import Data.Map
import Data.Typeable
import Data.Monoid

import Lang.LAMA.Identifier
import Data.String (IsString(..))
import Lang.LAMA.Types

data GProgram i const expr cexpr = Program {
    progEnumDefinitions     :: Map (TypeAlias i) (GEnumDef i),
    progConstantDefinitions :: Map i const,
    progDecls               :: GDeclarations i expr cexpr,
    progFlow                :: GFlow i expr,
    progInitial             :: GStateInit i cexpr,
    progAssertion           :: expr,
    progInvariant           :: expr
  } deriving (Eq, Show)


---- Type definitions -----

-- | Naming of enum constructors
newtype GEnumConstr i = EnumCons { runEnumCons :: i } deriving (Eq, Ord, Show, Typeable)
instance Ident i => Ident (GEnumConstr i) where
  identBS (EnumCons x) = identBS x
  identPretty (EnumCons x) = identPretty x

instance IsString i => IsString (GEnumConstr i) where
  fromString = EnumCons . fromString

-- | Enum definition
data GEnumDef i = EnumDef [GEnumConstr i] deriving (Eq, Show)

---- Constants -----
-- | LAMA constants
data GConst f
    = BoolConst Bool        -- ^ Boolean constant
    | IntConst Integer      -- ^ Integer constant
    | RealConst Rational    -- ^ Real constant (seen as arbitrary rational number)
    | SIntConst Natural Integer     -- ^ Bounded signed constant
    | UIntConst Natural Natural     -- ^ Bounded unsigned constant
    deriving (Eq, Show)


---- Nodes -----

data GNode i expr cexpr = Node {
    nodeDecls       :: GDeclarations i expr cexpr,
    nodeOutputs     :: [GVariable i],
    nodeFlow        :: GFlow i expr,
    nodeAutomata    :: Map Int (GAutomaton i expr),
    nodeInitial     :: GStateInit i cexpr,
    nodeAssertion   :: expr
  } deriving (Eq, Show)
  
data GVariable i = Variable i (Type i) deriving (Eq, Show)

varIdent :: GVariable i -> i
varIdent (Variable x _) = x

varType :: GVariable i -> Type i
varType (Variable _ t) = t

data GDeclarations i expr cexpr = Declarations {
    declsNode   :: Map i (GNode i expr cexpr),
    declsInput  :: [GVariable i],
    declsLocal  :: [GVariable i],
    declsState  :: [GVariable i]
  } deriving (Eq, Show)

---- Data flow -----

data GFlow i expr = Flow {
    flowDefinitions :: [GInstantDefinition i expr],
    flowTransitions :: [GStateTransition i expr]
  } deriving (Eq, Show)

data GInstantDefinition i expr
  = InstantExpr i expr
  | NodeUsage i i [expr]     -- ^ Using a node
  deriving (Eq, Show)

data GStateTransition i expr = StateTransition i expr deriving (Eq, Show)
type GStateInit i cexpr = Map i cexpr


---- Automaton -----

type GLocationId i = i
data GLocation i expr = Location (GLocationId i) (GFlow i expr) deriving (Eq, Show)
data GEdge i expr = Edge (GLocationId i) (GLocationId i) expr deriving (Eq, Show)
data GAutomaton i expr = Automaton {
    automLocations :: [GLocation i expr],
    automInitial :: GLocationId i,
    automEdges :: [GEdge i expr],
    automDefaults :: Map i expr
  } deriving (Eq, Show)


---- Expressions -----

-- | Untyped atomic expressions
data GAtom i const f
  = AtomConst const  -- ^ Constant
  | AtomVar i  -- ^ Variable
  | AtomEnum (GEnumConstr i) -- ^ Enum value
  deriving (Eq, Show)

data GProd expr = Prod [expr] deriving (Eq, Show)

data GPatternHead i =
  EnumPattern (GEnumConstr i)
  | BottomPattern
  deriving (Eq, Show)

data GPattern i expr = Pattern (GPatternHead i) expr deriving (Eq, Show)

-- | Untyped LAMA expressions
data GExpr i const atom f
  = AtExpr (GAtom i const atom)                    -- ^ Atomic expression (see GAtom)
  | LogNot f                        -- ^ Logical negation
  | Expr2 BinOp f f                 -- ^ Binary expression
  | Ite f f f                       -- ^ If-then-else
  | ProdCons (GProd f) -- ^ Product constructor
  | Project i Natural      -- ^ Product projection
  | Match f [GPattern i f] -- ^ Pattern match
  deriving (Eq, Show)

-- | Binary operators
data BinOp
  = Or | And | Xor | Implies
  | Equals | Less | LEq | Greater | GEq
  | Plus | Minus | Mul | RealDiv | IntDiv | Mod
  deriving (Eq, Show)

-- | Untyped constant expressions
data GConstExpr i const f
  = Const const                       -- ^ Simple constant
  | ConstEnum (GEnumConstr i)
  | ConstProd (GProd f) -- ^ Product constructed from constant expressions
  deriving (Eq, Show)


---- Instances -----

instance EqFunctor GProd where
  eqF = (==)

instance EqFunctor GConst where
  eqF = (==)

instance (Ident i, Eq const) => EqFunctor (GConstExpr i const) where
  eqF = (==)

instance (Ident i, Eq const) => EqFunctor (GAtom i const) where
  eqF = (==)

instance (Ident i, Eq const, Eq atom) => EqFunctor (GExpr i const atom) where
  eqF = (==)


instance ShowFunctor GProd where
  showF = show

instance ShowFunctor GConst where
  showF = show

instance (Ident i, Show const) => ShowFunctor (GConstExpr i const) where
  showF = show

instance (Ident i, Show const) => ShowFunctor (GAtom i const) where
  showF = show
  
instance (Ident i, Show const, Show atom) => ShowFunctor (GExpr i const atom) where
  showF = show

instance Monoid (GFlow i expr) where
  mempty = Flow [] []
  mappend (Flow d1 s1) (Flow d2 s2) = Flow (d1 ++ d2) (s1 ++ s2)