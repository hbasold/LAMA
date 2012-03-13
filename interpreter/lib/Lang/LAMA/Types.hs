module Lang.LAMA.Types where

import qualified Data.ByteString.Char8 as BS
import Data.Natural
import Data.Map
import Control.Arrow (first, (&&&))

type StateInit = Map Identifier ConstExpr

data File = File {
    fileTypeDefinitions :: Map TypeId TypeDef,
    fileConstantDefinitions :: Map Identifier Constant,
    fileMainNode :: Node,
    fileAssertions :: [Expr],
    fileInitial :: StateInit,
    fileInvariant :: [Expr]
  } deriving (Eq, Show)

type SourcePosition = (Int, Int)
data Identifier = Id BS.ByteString SourcePosition deriving Show

instance Eq Identifier where
  (Id s1 _) == (Id s2 _) = s1 == s2

instance Ord Identifier where
  compare (Id s1 _) (Id s2 _) = compare s1 s2

type TypeId = Identifier
data TypeDef = EnumDef EnumT | RecordDef RecordT deriving (Eq, Show)

type EnumConstr = Identifier
data EnumT = EnumT [EnumConstr] deriving (Eq, Show)

type RecordField = Identifier
data RecordT = RecordT [(RecordField, Type)] deriving (Eq, Show)
data RecordConstr e = RecordConstr TypeId [e] deriving (Eq, Show)

data Type = GroundType BaseType | NamedType TypeId | ArrayType BaseType Natural deriving (Eq, Show)
data BaseType =
  BoolT | IntT | RealT | SInt Natural | UInt Natural
  deriving (Eq, Show)
  
boolT :: Type
boolT = GroundType BoolT

intT :: Type
intT = GroundType IntT

realT :: Type
realT = GroundType RealT

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

data Typed e = Typed {
    untyped :: (e (Typed e)),
    getType :: Type
  }

-- | Construct new typed expression preserving the type
preserveType :: (Typed e1 -> (e2 (Typed e2))) -> Typed e1 -> Typed e2
preserveType cons = (uncurry Typed) . (first cons) . (id &&& getType)

class EqFunctor f where
  eqF :: Eq a => f a -> f a -> Bool

instance EqFunctor e => Eq (Typed e) where
  (Typed e1 t1) == (Typed e2 t2) = eqF e1 e2 && t1 == t2
  
class ShowFunctor f where
  showF :: Show a => f a -> String
  
instance ShowFunctor e => Show (Typed e) where
  show (Typed e t) = "(Typed (" ++ showF e ++ ") (" ++ show t ++ "))"

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


