{-| Structure of LAMA programs -}
module Lang.LAMA.Structure (
  Program(..),
  -- * Type definitions
  TypeDef(..),
  -- ** Enums
  EnumConstr, EnumT(..),
  -- ** Records
  RecordField, RecordT(..),
  -- * Constants
  Constant, UConst(..),
  -- * Nodes
  Node(..), Variable(..), varIdent,
  -- * Data flow
  Flow(..),
  -- ** Definition of local and output variables
  Pattern, NodeUsage(..), InstantDefinition(..),
  -- ** Definition of state variables
  StateTransition(..), StateInit,
  -- * Automata
  LocationId, Location(..), Edge(..), Automaton(..),
  -- * Expressions
  Atom, Expr, ConstExpr,
  -- ** Untyped expressions
  -- $untyped-doc
  UAtom(..), UExpr(..), UConstExpr(..), BinOp(..), RecordConstr(..)
) where

import Data.Natural
import Data.Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types

-- | A LAMA program needs at least a top level node ('progMainNode')
--  which will be the target for the given verification
--  properties ('progInvariant').
data Program = Program {
    progTypeDefinitions     :: Map TypeId TypeDef,
    progConstantDefinitions :: Map Identifier Constant,
    progMainNode            :: Node,
    progAssertions          :: [Expr],
    progInitial             :: StateInit,
    progInvariant           :: [Expr]
  } deriving (Eq, Show)


---- Type definitions -----

-- | Type definition
data TypeDef
  = EnumDef EnumT     -- ^ Enum definition
  | RecordDef RecordT -- ^ Record definition
  deriving (Eq, Show)

-- | Naming of enum constructors
type EnumConstr = Identifier
-- | Enum definition: lists the names for the constructors
data EnumT = EnumT [EnumConstr] deriving (Eq, Show)

-- | Naming of record fields
type RecordField = Identifier
-- | Record definition: consists of named fields and their types
data RecordT = RecordT [(RecordField, Type)] deriving (Eq, Show)


---- Constants -----

-- | Typed constant
type Constant = Typed UConst
-- | LAMA constants
data UConst e
    = BoolConst Bool        -- ^ Boolean constant
    | IntConst Integer      -- ^ Integer constant
    | RealConst Rational    -- ^ Real constant (seen as arbitrary rational number)
    | SIntConst Integer     -- ^ Bounded signed constant (bit size is to be found in the type)
    | UIntConst Natural     -- ^ Bounded unsigned constant (bit size is to be found in the type)
    deriving (Eq, Show)


---- Nodes -----

data Node = Node {
    nodeName        :: Identifier,
    nodeInputs      :: [Variable],
    nodeOutputs     :: [Variable],
    nodeSubNodes    :: [Node],
    nodeState       :: [Variable],
    nodeLocals      :: [Variable],
    nodeFlow        :: Flow,
    nodeAutomata    :: [Automaton],
    nodeInitial     :: StateInit
  } deriving (Eq, Show)
  
data Variable = Variable Identifier Type deriving (Eq, Show)

varIdent :: Variable -> Identifier
varIdent (Variable x _) = x


---- Data flow -----

data Flow = Flow {
    flowDefinitions :: [InstantDefinition],
    flowOutputs     :: [InstantDefinition],
    flowTransitions :: [StateTransition]
  } deriving (Eq, Show)

type Pattern = [Identifier]
data NodeUsage = NodeUsage Identifier [Expr] deriving (Eq, Show)
data InstantDefinition = SimpleDef Identifier Expr | NodeUsageDef Pattern NodeUsage deriving (Eq, Show)

data StateTransition = StateTransition Identifier Expr deriving (Eq, Show)
type StateInit = Map Identifier ConstExpr


---- Automaton -----

type LocationId = Identifier
data Location = Location LocationId Flow deriving (Eq, Show)
data Edge = Edge LocationId LocationId Expr deriving (Eq, Show)
data Automaton = Automaton {
    automLocations :: [Location],
    automInitial :: LocationId,
    automEdges :: [Edge]
  } deriving (Eq, Show)


---- Expressions -----

-- $untyped-doc
-- The parameter /e/ of the untyped expressions
-- is replaced by the typed variant of themselves
-- by 'Typed'. So 'Typed' builds up a fix point type.

type Expr = Typed UExpr             -- ^ Typed expression
type Atom = Typed UAtom             -- ^ Typed atom
type ConstExpr = Typed UConstExpr   -- ^ Typed constant expression

-- | Untyped atomic expressions
data UAtom e
  = AtomConst Constant  -- ^ Constant
  | AtomVar Identifier  -- ^ Variable
  deriving (Eq, Show)

-- | Construction of records: requires type and expression for each field
data RecordConstr e = RecordConstr TypeId [e] deriving (Eq, Show)

-- | Untyped LAMA expressions
data UExpr e
  = AtExpr Atom                     -- ^ Atomic expression (see UAtom)
  | LogNot e                        -- ^ Logical negation
  | Expr2 BinOp e e                 -- ^ Binary expression
  | Ite e e e                       -- ^ If-then-else
  | Constr (RecordConstr e)         -- ^ Record construtor
  | Select Identifier RecordField   -- ^ Record selection
  | Project Identifier Natural      -- ^ Array projection
  deriving (Eq, Show)

-- | Binary operators
data BinOp
  = Or | And | Xor | Implies
  | Equals | Less | LEq | Greater | GEq
  | Plus | Minus | Mul | RealDiv | IntDiv | Mod
  deriving (Eq, Show)

-- | Untyped constant expressions
data UConstExpr e
  = Const Constant                        -- ^ Simple constant
  | ConstRecord (RecordConstr ConstExpr)  -- ^ Record constructed from constant expressions
  deriving (Eq, Show)


---- Instances -----

instance EqFunctor RecordConstr where
  eqF = (==)

instance EqFunctor UConst where
  eqF = (==)
  
instance EqFunctor UConstExpr where
  eqF = (==)

instance EqFunctor UAtom where
  eqF = (==)

instance EqFunctor UExpr where
  eqF = (==)


instance ShowFunctor RecordConstr where
  showF = show

instance ShowFunctor UConst where
  showF = show
  
instance ShowFunctor UConstExpr where
  showF = show

instance ShowFunctor UAtom where
  showF = show
  
instance ShowFunctor UExpr where
  showF = show


