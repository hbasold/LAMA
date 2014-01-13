{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-| Structure of LAMA programs -}
module Lang.LAMA.Structure (
  GProgram(..),
  -- * Type definitions
  GEnumDef(..), GEnumConstr(..),
  -- * Constants
  GConst(..),
  -- * Declarations of nodes and variables
  GNode(..), GVariable(..), GDeclarations(..),
  -- * Data flow
  GFlow(..),
  GInstantDefinition(..),
  GStateTransition(..), GStateInit,
  -- * Automata
  GLocationId(..), GLocation(..), GEdge(..), GAutomaton(..),
  -- * Expressions
  -- $generalised-types-doc
  GProd(..), GPatternHead(..), GPattern(..),
  GAtom(..), GExpr(..), GConstExpr(..), BinOp(..),
  -- * Viewing and mapping
  ViewExpr(..), PackedExpr(..), ViewConst(..), PackedConst(..),
  mapIdentExpr
) where

import Prelude.Extras

import Data.Natural
import Data.Map
import Data.Typeable
import Data.Monoid

import Lang.LAMA.Identifier
import Data.String (IsString(..))
import Lang.LAMA.Types

-- $generalised-types-doc
-- All defined types have type parameters which allow them to have
--
-- 1. an arbitrary identifier type (in most cases an identifier with or w/o position)
-- 
-- 2. additional data attached (mostly a type)
--
-- The second one requires the constant and expression types to be instantiated
-- as fixed point types (see "Lang.LAMA.Types").

---- Program ----

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
newtype GEnumConstr i = EnumCons { runEnumCons :: i }
                      deriving (Eq, Ord, Show, Typeable)

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
    = BoolConst Bool             -- ^ Boolean constant
    | IntConst Integer           -- ^ Integer constant
    | RealConst Rational         -- ^ Real constant (seen as arbitrary rational number)
    | SIntConst Natural Integer  -- ^ Bounded signed constant
    | UIntConst Natural Natural  -- ^ Bounded unsigned constant
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

-- | A variable consists of an identifier and a type.
data GVariable i = Variable
                   { varIdent :: i
                   , varType :: (Type i)
                   } deriving (Eq, Show)

-- | Keeps declarations of the current scope.
-- The kind of input depends on the context:
--
--  * on program level these are free variables
--
--  * on node level these are declared node inputs.
--
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

-- | Definition of local and output variables by an expression
-- or a call of a node.
data GInstantDefinition i expr
  = InstantExpr i expr
  | NodeUsage i i [expr]     -- ^ Using a node
  deriving (Eq, Show)

-- | Definition of state variables
data GStateTransition i expr = StateTransition i expr deriving (Eq, Show)

-- | Initialisation of state variables
type GStateInit i cexpr = Map i cexpr


---- Automaton -----

newtype GLocationId i = LocationId { runLocationId :: i }
                      deriving (Eq, Ord, Show, Typeable)

instance Ident i => Ident (GLocationId i) where
  identBS = identBS . runLocationId
  identPretty = identPretty . runLocationId

instance IsString i => IsString (GLocationId i) where
  fromString = LocationId . fromString

-- | A named mode of an automaton with its attached flow.
data GLocation i expr = Location (GLocationId i) (GFlow i expr) deriving (Eq, Show)

-- | An edge h -> t with a condition c.
data GEdge i expr = Edge (GLocationId i) (GLocationId i) expr deriving (Eq, Show)

data GAutomaton i expr = Automaton {
    automLocations :: [GLocation i expr],
    automInitial :: GLocationId i,
    automEdges :: [GEdge i expr],
    automDefaults :: Map i expr
    -- ^ Default expressions for partially defined local variables
  } deriving (Eq, Show)


---- Expressions -----

-- | Generalised atomic expressions
data GAtom i const f
  = AtomConst const          -- ^ Constant
  | AtomVar i                -- ^ Variable
  | AtomEnum (GEnumConstr i) -- ^ Enum value
  deriving (Eq, Show)

-- | Product of the given expression type.
data GProd expr = Prod [expr] deriving (Eq, Show)

-- | Generalised head of a pattern. Either an enum constructor or _.
data GPatternHead i =
  EnumPattern (GEnumConstr i)
  | BottomPattern
  deriving (Eq, Show)

-- | A pattern consists of a head /P/ and an expression /M/ which is
-- evaluated if that head matches: /P.M/.
data GPattern i expr = Pattern (GPatternHead i) expr deriving (Eq, Show)

-- | Generalised LAMA expressions
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

-- | Generalised constant expressions
data GConstExpr i const f
  = Const const               -- ^ Simple constant
  | ConstEnum (GEnumConstr i) -- ^ Enum in a constant context
  | ConstProd (GProd f)       -- ^ Product constructed from constant expressions
  deriving (Eq, Show)


---- Instances -----

instance Eq1 GProd where
  (==#) = (==)

instance Eq1 GConst where
  (==#) = (==)

instance (Ident i, Eq const) => Eq1 (GConstExpr i const) where
  (==#) = (==)

instance (Ident i, Eq const) => Eq1 (GAtom i const) where
  (==#) = (==)

instance (Ident i, Eq const, Eq atom) => Eq1 (GExpr i const atom) where
  (==#) = (==)


instance Show1 GProd where
  showsPrec1 = showsPrec

instance Show1 GConst where
  showsPrec1 = showsPrec

instance (Ident i, Show const) => Show1 (GConstExpr i const) where
  showsPrec1 = showsPrec

instance (Ident i, Show const) => Show1 (GAtom i const) where
  showsPrec1 = showsPrec
  
instance (Ident i, Show const, Show atom) => Show1 (GExpr i const atom) where
  showsPrec1 = showsPrec

instance Monoid (GFlow i expr) where
  mempty = Flow [] []
  mappend (Flow d1 s1) (Flow d2 s2) = Flow (d1 ++ d2) (s1 ++ s2)

class Ident i => ViewExpr i e const atom | e -> i, e -> const, e -> atom where
  viewExpr :: e -> GExpr i const atom e

class Ident i => PackedExpr i e const atom | e -> i, e -> const, e -> atom where
  packExpr :: GExpr i const atom e -> e

class ViewConst c where
  viewConst :: c -> GConst c

class PackedConst c where
  packConst :: GConst c -> c


mapIdentExpr :: (Ident i1, Ident i2,
                 ViewExpr i1 e1 c1 a1, ViewExpr i2 e2 c2 a2,
                 PackedExpr i1 e1 c1 a1, PackedExpr i2 e2 c2 a2,
                 ViewConst c1, ViewConst c2, PackedConst c1, PackedConst c2)
                => (i1 -> i2) -> (e1 -> e2)
mapIdentExpr f = \expr -> case expr of
  (viewExpr -> AtExpr (AtomConst c)) -> packExpr $ AtExpr (AtomConst $ mapIdentConst f c)
  (viewExpr -> AtExpr (AtomVar x)) -> packExpr $ AtExpr (AtomVar $ f x)
  (viewExpr -> AtExpr (AtomEnum x)) -> packExpr $ AtExpr (AtomEnum . EnumCons . f $ runEnumCons x)
  (viewExpr -> LogNot e) -> packExpr . LogNot $ mapIdentExpr f e
  (viewExpr -> Expr2 op e1 e2) ->
    packExpr $ Expr2 op (mapIdentExpr f e1) (mapIdentExpr f e2)
  (viewExpr -> Ite c e1 e2) ->
    packExpr $ Ite (mapIdentExpr f c) (mapIdentExpr f e1) (mapIdentExpr f e2)
  (viewExpr -> ProdCons (Prod es)) ->
    packExpr . ProdCons . Prod $ fmap (mapIdentExpr f) es
  (viewExpr -> Project x n) -> packExpr $ Project (f x) n
  (viewExpr -> Match e pats) -> packExpr $ Match (mapIdentExpr f e) $ fmap (mapIdentPattern f) pats
  _ -> undefined -- silence ghc

mapIdentConst :: (ViewConst c1, ViewConst c2, PackedConst c1, PackedConst c2) =>
                 (i1 -> i2) -> (c1 -> c2)
mapIdentConst _ (viewConst -> BoolConst c) = packConst $ BoolConst c
mapIdentConst _ (viewConst -> IntConst c) = packConst $ IntConst c
mapIdentConst _ (viewConst -> RealConst c) = packConst $ RealConst c
mapIdentConst _ (viewConst -> SIntConst n c) = packConst $ SIntConst n c
mapIdentConst _ (viewConst -> UIntConst n c) = packConst $ UIntConst n c

mapIdentPattern :: (Ident i1, Ident i2,
                    ViewExpr i1 e1 c1 a1, ViewExpr i2 e2 c2 a2,
                    PackedExpr i1 e1 c1 a1, PackedExpr i2 e2 c2 a2,
                    ViewConst c1, ViewConst c2, PackedConst c1, PackedConst c2)
                   => (i1 -> i2) -> (GPattern i1 e1 -> GPattern i2 e2)
mapIdentPattern f (Pattern h e) = Pattern (mapIdentPatternHead f h) (mapIdentExpr f e)

mapIdentPatternHead :: (Ident i1, Ident i2) => (i1 -> i2) -> (GPatternHead i1 -> GPatternHead i2)
mapIdentPatternHead f (EnumPattern (EnumCons x)) = EnumPattern . EnumCons $ f x
mapIdentPatternHead _ BottomPattern = BottomPattern
