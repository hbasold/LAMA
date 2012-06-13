{-| Structure of LAMA programs -}
module Lang.LAMA.Structure (
  GProgram(..),
  -- * Type definitions
  TypeDef(..),
  -- ** Enums
  EnumConstr, EnumT(..),
  -- ** Records
  RecordField, RecordT(..),
  -- * Constants
  GConst(..),
  -- * Nodes
  GNode(..), Variable(..), varIdent, varType, GDeclarations(..),
  -- * Data flow
  GFlow(..),
  -- ** Definition of local and output variables
  Pattern, GInstantDefinition(..), GInstant(..),
  -- ** Definition of state variables
  GStateTransition(..), GStateInit,
  -- * Automata
  LocationId, GLocation(..), GEdge(..), GAutomaton(..),
  -- * Expressions
  -- ** Untyped expressions
  -- $untyped-doc
  GAtom(..), GExpr(..), GConstExpr(..), BinOp(..), GRecordConstr(..), GTuple(..)
) where

import Data.Natural
import Data.Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types

-- | A LAMA program needs at least a top level node ('progMainNode')
--  which will be the target for the given verification
--  properties ('progInvariant').
data GProgram c e ce i = Program {
    progTypeDefinitions     :: Map TypeAlias TypeDef,
    progConstantDefinitions :: Map Identifier c,
    progDecls               :: GDeclarations e ce i,
    progFlow                :: GFlow e i,
    progInitial             :: GStateInit ce,
    progAssertions          :: [e],
    progInvariant           :: [e]
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
-- | LAMA constants
data GConst e
    = BoolConst Bool        -- ^ Boolean constant
    | IntConst Integer      -- ^ Integer constant
    | RealConst Rational    -- ^ Real constant (seen as arbitrary rational number)
    | SIntConst Natural Integer     -- ^ Bounded signed constant
    | UIntConst Natural Natural     -- ^ Bounded unsigned constant
    deriving (Eq, Show)


---- Nodes -----

data GNode e ce i = Node {
    nodeInputs      :: [Variable],
    nodeOutputs     :: [Variable],
    nodeDecls       :: GDeclarations e ce i,
    nodeFlow        :: GFlow e i,
    nodeOutputDefs  :: [GInstantDefinition i],
    nodeAutomata    :: Map Int (GAutomaton e i),
    nodeInitial     :: GStateInit ce
  } deriving (Eq, Show)
  
data Variable = Variable Identifier Type deriving (Eq, Show)

varIdent :: Variable -> Identifier
varIdent (Variable x _) = x

varType :: Variable -> Type
varType (Variable _ t) = t

data GDeclarations e ce i = Declarations {
    declsNode   :: Map Identifier (GNode e ce i),
    declsState  :: [Variable],
    declsLocal  :: [Variable]
  } deriving (Eq, Show)

---- Data flow -----

data GFlow e i = Flow {
    flowDefinitions :: [GInstantDefinition i],
    flowTransitions :: [GStateTransition e]
  } deriving (Eq, Show)

type Pattern = [Identifier]
data GInstantDefinition i = InstantDef Pattern i deriving (Eq, Show)
data GInstant e f
  = InstantExpr e
  | NodeUsage Identifier [e]     -- ^ Using a node
  deriving (Eq, Show)

data GStateTransition e = StateTransition Identifier e deriving (Eq, Show)
type GStateInit ce = Map Identifier ce


---- Automaton -----

type LocationId = Identifier
data GLocation e i = Location LocationId (GFlow e i) deriving (Eq, Show)
data GEdge e = Edge LocationId LocationId e deriving (Eq, Show)
data GAutomaton e i = Automaton {
    automLocations :: [GLocation e i],
    automInitial :: LocationId,
    automEdges :: [GEdge e]
  } deriving (Eq, Show)


---- Expressions -----

-- | Untyped atomic expressions
data GAtom c e
  = AtomConst c  -- ^ Constant
  | AtomVar Identifier  -- ^ Variable
  deriving (Eq, Show)

-- | Construction of records: requires type and expression for each field
data GRecordConstr e = RecordConstr TypeAlias [e] deriving (Eq, Show)

data GTuple e = Tuple [e] deriving (Eq, Show)

-- | Untyped LAMA expressions
data GExpr c a e
  = AtExpr (GAtom c a)                    -- ^ Atomic expression (see GAtom)
  | LogNot e                        -- ^ Logical negation
  | Expr2 BinOp e e                 -- ^ Binary expression
  | Ite e e e                       -- ^ If-then-else
  | Constr (GRecordConstr e)         -- ^ Record construtor
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
data GConstExpr c e
  = Const c                       -- ^ Simple constant
  | ConstRecord (GRecordConstr e)  -- ^ Record constructed from constant expressions
  | ConstTuple (GTuple e)
  deriving (Eq, Show)


---- Instances -----

instance EqFunctor GRecordConstr where
  eqF = (==)

instance EqFunctor GTuple where
  eqF = (==)

instance EqFunctor GConst where
  eqF = (==)

instance Eq e => EqFunctor (GInstant e) where
  eqF = (==)
  
instance Eq c => EqFunctor (GConstExpr c) where
  eqF = (==)

instance Eq c => EqFunctor (GAtom c) where
  eqF = (==)

instance (Eq c, Eq a) => EqFunctor (GExpr c a) where
  eqF = (==)


instance ShowFunctor GRecordConstr where
  showF = show

instance ShowFunctor GTuple where
  showF = show

instance ShowFunctor GConst where
  showF = show

instance Show e => ShowFunctor (GInstant e) where
  showF = show
  
instance Show c => ShowFunctor (GConstExpr c) where
  showF = show

instance Show c => ShowFunctor (GAtom c) where
  showF = show
  
instance (Show c, Show a) => ShowFunctor (GExpr c a) where
  showF = show


