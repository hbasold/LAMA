{-| Structure of LAMA programs -}
module Lang.LAMA.Structure (
  GProgram(..),
  -- * Type definitions
  GTypeDef(..),
  -- ** Enums
  GEnumConstr, GEnumT(..),
  -- ** Records
  GRecordField, GRecordT(..),
  -- * Constants
  GConst(..),
  -- * Nodes
  GNode(..), GVariable(..), varIdent, varType, GDeclarations(..),
  -- * Data flow
  GFlow(..),
  -- ** Definition of local and output variables
  GPattern, GInstantDefinition(..), GInstant(..),
  -- ** Definition of state variables
  GStateTransition(..), GStateInit,
  -- * Automata
  GLocationId, GLocation(..), GEdge(..), GAutomaton(..),
  -- * Expressions
  -- ** Untyped expressions
  -- $untyped-doc
  GAtom(..), GExpr(..), GConstExpr(..), BinOp(..), GRecordConstr(..), GTuple(..)
) where

import Data.Natural
import Data.Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types

data GProgram i const expr cexpr inst = Program {
    progTypeDefinitions     :: Map (TypeAlias i) (GTypeDef i),
    progConstantDefinitions :: Map i const,
    progDecls               :: GDeclarations i expr cexpr inst,
    progFlow                :: GFlow i expr inst,
    progInitial             :: GStateInit i cexpr,
    progAssertion           :: expr,
    progInvariant           :: expr
  } deriving (Eq, Show)


---- Type definitions -----

-- | Type definition
data GTypeDef i
  = EnumDef (GEnumT i)     -- ^ Enum definition
  | RecordDef (GRecordT i) -- ^ Record definition
  deriving (Eq, Show)

-- | Naming of enum constructors
type GEnumConstr i = i
-- | Enum definition: lists the names for the constructors
data GEnumT i = EnumT [GEnumConstr i] deriving (Eq, Show)

-- | Naming of record fields
type GRecordField i = i
-- | Record definition: consists of named fields and their types
data GRecordT i = RecordT [(GRecordField i, Type i)] deriving (Eq, Show)


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

data GNode i expr cexpr inst = Node {
    nodeInputs      :: [GVariable i],
    nodeOutputs     :: [GVariable i],
    nodeDecls       :: GDeclarations i expr cexpr inst,
    nodeFlow        :: GFlow i expr inst,
    nodeOutputDefs  :: [GInstantDefinition i inst],
    nodeAutomata    :: Map Int (GAutomaton i expr inst),
    nodeInitial     :: GStateInit i cexpr
  } deriving (Eq, Show)
  
data GVariable i = Variable i (Type i) deriving (Eq, Show)

varIdent :: GVariable i -> i
varIdent (Variable x _) = x

varType :: GVariable i -> Type i
varType (Variable _ t) = t

data GDeclarations i expr cexpr inst = Declarations {
    declsNode   :: Map i (GNode i expr cexpr inst),
    declsState  :: [GVariable i],
    declsLocal  :: [GVariable i]
  } deriving (Eq, Show)

---- Data flow -----

data GFlow i expr inst = Flow {
    flowDefinitions :: [GInstantDefinition i inst],
    flowTransitions :: [GStateTransition i expr]
  } deriving (Eq, Show)

type GPattern i = [i]
data GInstantDefinition i inst = InstantDef (GPattern i) inst deriving (Eq, Show)
data GInstant i expr f
  = InstantExpr (expr)
  | NodeUsage i [expr]     -- ^ Using a node
  deriving (Eq, Show)

data GStateTransition i expr = StateTransition i expr deriving (Eq, Show)
type GStateInit i cexpr = Map i cexpr


---- Automaton -----

type GLocationId i = i
data GLocation i expr inst = Location (GLocationId i) (GFlow i expr inst) deriving (Eq, Show)
data GEdge i expr = Edge (GLocationId i) (GLocationId i) expr deriving (Eq, Show)
data GAutomaton i expr inst = Automaton {
    automLocations :: [GLocation i expr inst],
    automInitial :: GLocationId i,
    automEdges :: [GEdge i expr]
  } deriving (Eq, Show)


---- Expressions -----

-- | Untyped atomic expressions
data GAtom i const f
  = AtomConst const  -- ^ Constant
  | AtomVar i  -- ^ Variable
  deriving (Eq, Show)

-- | Construction of records: requires type and expression for each field
data GRecordConstr i expr = RecordConstr (TypeAlias i) [expr] deriving (Eq, Show)

data GTuple i expr = Tuple [expr] deriving (Eq, Show)

-- | Untyped LAMA expressions
data GExpr i const atom f
  = AtExpr (GAtom i const atom)                    -- ^ Atomic expression (see GAtom)
  | LogNot (f)                        -- ^ Logical negation
  | Expr2 BinOp (f) (f)                 -- ^ Binary expression
  | Ite (f) (f) (f)                       -- ^ If-then-else
  | Constr (GRecordConstr i f)         -- ^ Record construtor
  | Select i (GRecordField i)   -- ^ Record selection
  | Project i Natural      -- ^ Array projection
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
  | ConstRecord (GRecordConstr i f)  -- ^ Record constructed from constant expressions
  | ConstTuple (GTuple i f)
  deriving (Eq, Show)


---- Instances -----

instance Ident i => EqFunctor (GRecordConstr i) where
  eqF = (==)

instance Ident i => EqFunctor (GTuple i) where
  eqF = (==)

instance EqFunctor GConst where
  eqF = (==)

instance (Ident i, Eq expr) => EqFunctor (GInstant i expr) where
  eqF = (==)
  
instance (Ident i, Eq const) => EqFunctor (GConstExpr i const) where
  eqF = (==)

instance (Ident i, Eq const) => EqFunctor (GAtom i const) where
  eqF = (==)

instance (Ident i, Eq const, Eq atom) => EqFunctor (GExpr i const atom) where
  eqF = (==)


instance Ident i => ShowFunctor (GRecordConstr i) where
  showF = show

instance Ident i => ShowFunctor (GTuple i) where
  showF = show

instance ShowFunctor GConst where
  showF = show

instance (Ident i, Show expr) => ShowFunctor (GInstant i expr) where
  showF = show
  
instance (Ident i, Show const) => ShowFunctor (GConstExpr i const) where
  showF = show

instance (Ident i, Show const) => ShowFunctor (GAtom i const) where
  showF = show
  
instance (Ident i, Show const, Show atom) => ShowFunctor (GExpr i const atom) where
  showF = show


