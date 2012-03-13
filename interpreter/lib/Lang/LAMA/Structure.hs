module Lang.LAMA.Structure where

import Data.Natural
import Data.Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types

type StateInit = Map Identifier ConstExpr

data File = File {
    fileTypeDefinitions :: Map TypeId TypeDef,
    fileConstantDefinitions :: Map Identifier Constant,
    fileMainNode :: Node,
    fileAssertions :: [Expr],
    fileInitial :: StateInit,
    fileInvariant :: [Expr]
  } deriving (Eq, Show)

data TypeDef = EnumDef EnumT | RecordDef RecordT deriving (Eq, Show)

type EnumConstr = Identifier
data EnumT = EnumT [EnumConstr] deriving (Eq, Show)

type RecordField = Identifier
data RecordT = RecordT [(RecordField, Type)] deriving (Eq, Show)
data RecordConstr e = RecordConstr TypeId [e] deriving (Eq, Show)

type Constant = Typed UConst
data UConst e = BoolConst Bool | IntConst Integer | RealConst Rational
                    | SIntConst Integer | UIntConst Natural
                    deriving (Eq, Show)

type ConstExpr = Typed UConstExpr
data UConstExpr e = Const Constant | ConstRecord (RecordConstr ConstExpr) deriving (Eq, Show)
                  
data Node = Node {
    nodeName :: Identifier,
    nodeInputs :: [Variable],
    nodeOutputs :: [Variable],
    nodeSubNodes :: [Node],
    nodeState :: [Variable],
    nodeLocals :: [Variable],
    nodeFlow :: Flow,
    nodeAutomata :: [Automaton],
    nodeInitial :: StateInit
  } deriving (Eq, Show)
  
data Variable = Variable Identifier Type deriving (Eq, Show)

data Flow = Flow {
    flowDefinitions :: [InstantDefinition],
    flowOutputs     :: [InstantDefinition],
    flowTransitions :: [StateTransition]
  } deriving (Eq, Show)

type Pattern = [Identifier]
data NodeUsage = NodeUsage Identifier [Expr] deriving (Eq, Show)
data InstantDefinition = SimpleDef Identifier Expr | NodeUsageDef Pattern NodeUsage deriving (Eq, Show)

data StateTransition = StateTransition Identifier Expr deriving (Eq, Show)

type LocationId = Identifier
data Location = Location LocationId Flow deriving (Eq, Show)
data Edge = Edge LocationId LocationId Expr deriving (Eq, Show)
data Automaton = Automaton {
    automLocations :: [Location],
    automInitial :: LocationId,
    automEdges :: [Edge]
  } deriving (Eq, Show)

type Expr = Typed UExpr
type Atom = Typed UAtom

data UAtom e = AtomConst Constant | AtomVar Identifier deriving (Eq, Show)
data UExpr e
  = AtExpr Atom | LogNot e | Expr2 BinOp e e | Ite e e e
  | Constr (RecordConstr e) | Project Identifier Natural | Select Identifier RecordField
  deriving (Eq, Show)

data BinOp
  = Or | And | Xor | Implies
  | Equals | Less | LEq | Greater | GEq
  | Plus | Minus | Mul | RealDiv | IntDiv | Mod
  deriving (Eq, Show)


--- Instances
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


