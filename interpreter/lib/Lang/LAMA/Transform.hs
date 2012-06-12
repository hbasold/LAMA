{-# LANGUAGE TemplateHaskell #-}

{- Translate generated data structures to internal structures
  while checking for undefined automaton locations and
  constant expressions. -}
module Lang.LAMA.Transform (absToConc, transConstExpr) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Natural
import Data.Ratio
import qualified Data.ByteString.Char8 as BS
import Prelude hiding (foldl, concat, any)
import Data.Foldable
import Control.Applicative hiding (Const)
import Control.Arrow (second)
import Control.Monad.Error (throwError)
import Control.Monad (when)

import qualified Lang.LAMA.Parser.Abs as Abs
import qualified Lang.LAMA.Parser.Print as Abs (printTree)
import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.UnTypedStructure

-- | Monad for the transformation process
--    Carries possible errors
type Result = Either String

absToConc :: Abs.Program -> Either String Program
absToConc = transProgram

-- | Create identifier from position information and name
makeId :: ((Int, Int), BS.ByteString) -> Identifier
makeId (pos, str) = Id str pos

-- | Create identifier from position information and name without the last
--    character, this should be a "'" which is part of a state identifier
--    on the lhs in a state assignment.
makeStateId :: ((Int, Int), BS.ByteString) -> Identifier
makeStateId (pos, str) = Id (BS.init str) pos

--- Translation functions

transIdentifier :: Abs.Identifier -> Result Identifier
transIdentifier x = case x of
  Abs.Identifier str  -> return $ makeId str


transStateId :: Abs.StateId -> Result Identifier
transStateId x = case x of
  Abs.StateId str  -> return $ makeStateId str


transProgram :: Abs.Program -> Result Program
transProgram x = case x of
  Abs.Program typedefs constantdefs declarations flow initial assertion invariant -> do
    Program <$>
      (transTypeDefs typedefs) <*>
      (transConstantDefs constantdefs) <*>
      (transDeclarations declarations) <*>
      (transFlow flow) <*>
      (transInitial initial) <*>
      (transAssertion assertion) <*>
      (transInvariant invariant)

transTypeDefs :: Abs.TypeDefs -> Result (Map TypeAlias TypeDef)
transTypeDefs x = case x of
  Abs.NoTypeDefs  -> return Map.empty
  Abs.JustTypeDefs typedefs  -> fmap Map.fromList $ mapM transTypeDef typedefs

transTypeDef :: Abs.TypeDef -> Result (TypeAlias, TypeDef)
transTypeDef x = case x of
  Abs.EnumDef enumt  -> fmap (second EnumDef) $ transEnumT enumt
  Abs.RecordDef recordt  -> fmap (second RecordDef) $ transRecordT recordt


transEnumConstr :: Abs.EnumConstr -> Result EnumConstr
transEnumConstr x = case x of
  Abs.EnumConstr identifier  -> transIdentifier identifier


transEnumT :: Abs.EnumT -> Result (TypeAlias, EnumT)
transEnumT x = case x of
  Abs.EnumT identifier enumconstrs  ->
    (,) <$> (transIdentifier identifier) <*> (fmap EnumT $ mapM transEnumConstr enumconstrs)


transRecordField :: Abs.RecordField -> Result (RecordField, Type)
transRecordField x = case x of
  Abs.RecordField identifier t ->
    (,) <$> (transIdentifier identifier) <*> (transType t)

transRecordT :: Abs.RecordT -> Result (TypeAlias, RecordT)
transRecordT x = case x of
  Abs.RecordT identifier recordfields  -> do
    ident <- transIdentifier identifier
    fields <- mapM transRecordField recordfields
    return (ident, RecordT fields)


transType :: Abs.Type -> Result Type
transType x = case x of
  Abs.GroundType basetype  -> fmap GroundType $ transBaseType basetype
  Abs.TypeId identifier  -> fmap NamedType $ transIdentifier identifier
  Abs.ArrayType basetype natural  ->
    ArrayType <$> (transBaseType basetype) <*> (transNatural natural)


transBaseType :: Abs.BaseType -> Result BaseType
transBaseType x = case x of
  Abs.BoolT  -> return BoolT
  Abs.IntT  -> return IntT
  Abs.RealT  -> return RealT
  Abs.SInt natural  -> fmap SInt $ transNatural natural
  Abs.UInt natural  -> fmap UInt $ transNatural natural

transConstantDefs :: Abs.ConstantDefs -> Result (Map Identifier Constant)
transConstantDefs x = case x of
  Abs.NoConstantDefs -> return Map.empty
  Abs.JustConstantDefs constantdefs -> fmap Map.fromList $ mapM transConstantDef constantdefs


transConstantDef :: Abs.ConstantDef -> Result (Identifier, Constant)
transConstantDef x = case x of
  Abs.ConstantDef identifier constant ->
    (,) <$> transIdentifier identifier <*> transConstant constant


transNatural :: Abs.Natural -> Result Natural
transNatural x = case x of
  Abs.Nat n  -> return $ fromInteger n


transIntegerConst :: Abs.IntegerConst -> Result Integer
transIntegerConst x = case x of
  Abs.NonNegativeInt n  -> return n
  Abs.NegativeInt n  -> return $ -n


transConstant :: Abs.Constant -> Result Constant
transConstant = fmap Fix . transConstant'
  where
    transConstant' x = case x of
      Abs.BoolConst boolv  -> BoolConst <$> transBoolV boolv

      Abs.IntConst integerconst  -> IntConst <$> (transIntegerConst integerconst)

      Abs.RealConst integerconst0 integerconst  ->
        RealConst <$>
          ((%) <$> (transIntegerConst integerconst0) <*> (transIntegerConst integerconst))

      Abs.SIntConst natural integerconst  ->
        SIntConst <$> (transNatural natural) <*> (transIntegerConst integerconst)

      Abs.UIntConst natural0 natural  ->
        UIntConst <$> (transNatural natural0) <*> (transNatural natural)


transBoolV :: Abs.BoolV -> Result Bool
transBoolV x = case x of
  Abs.TrueV  -> return True
  Abs.FalseV  -> return False


transAssertion :: Abs.Assertion -> Result [Expr]
transAssertion x = case x of
  Abs.NoAssertion  -> return []
  Abs.JustAssertion expr  -> (:[]) <$> (transExpr expr)


transInitial :: Abs.Initial -> Result (Map Identifier ConstExpr)
transInitial x = case x of
  Abs.NoInitial  -> return Map.empty
  Abs.JustInitial stateinits  -> fmap Map.fromList $ mapM transStateInit stateinits


transInvariant :: Abs.Invariant -> Result [Expr]
transInvariant x = case x of
  Abs.NoInvariant  -> return []
  Abs.JustInvariant expr  -> fmap (:[]) $ transExpr expr


transStateInit :: Abs.StateInit -> Result (Identifier, ConstExpr)
transStateInit x = case x of
  Abs.StateInit identifier constexpr  -> do
    (,) <$> transIdentifier identifier <*> (transConstExpr constexpr)


transConstExpr :: Abs.ConstExpr -> Result ConstExpr
transConstExpr x = case x of
  Abs.ConstExpr expr  -> transExpr expr >>= evalConst . unfix
  where
    evalConst :: GExpr Constant Atom Expr -> Result ConstExpr
    evalConst (AtExpr (AtomConst c)) = return $ Fix $ Const c
    evalConst (Constr (RecordConstr tid es)) = do
      cExprs <- mapM (evalConst . unfix) es
      return $ Fix $ ConstRecord $ RecordConstr tid cExprs
    evalConst _ = throwError $ "Not a constant expression: " ++ Abs.printTree x


transTypedVars :: Abs.TypedVars -> Result [Variable]
transTypedVars x = case x of
  Abs.TypedVars identifiers t  -> do
    t' <- transType t
    let varCons = flip Variable $ t'
    fmap (map varCons) $ mapM transIdentifier identifiers


transMaybeTypedVars :: Abs.MaybeTypedVars -> Result [Variable]
transMaybeTypedVars x = case x of
  Abs.NoTypedVars  -> return []
  Abs.JustTypedVars typedvarss  -> fmap concat $ mapM transTypedVars typedvarss


transNode :: Abs.Node -> Result (Identifier, Node)
transNode x = case x of
  Abs.Node identifier maybetypedvars typedvarss declarations flow outputs controlstructure initial ->
    (,) <$> (transIdentifier identifier) <*>
      (Node <$>
        (transMaybeTypedVars maybetypedvars) <*>
        (fmap concat $ mapM transTypedVars typedvarss) <*>
        (transDeclarations declarations) <*>
        (transFlow flow) <*>
        (transOutputs outputs) <*>
        (transControlStructure controlstructure) <*>
        (transInitial initial))

transDeclarations :: Abs.Declarations -> Result Declarations
transDeclarations x = case x of
  Abs.Declarations nodedecls statedecls localdecls ->
    Declarations <$>
      transNodeDecls nodedecls <*>
      transStateDecls statedecls <*>
      transLocalDecls localdecls

transVarDecls :: Abs.VarDecls -> Result [Variable]
transVarDecls x = case x of
  Abs.SingleDecl typedvars  -> transTypedVars typedvars
  Abs.ConsDecl typedvars vardecls  -> do
    vs <- transTypedVars typedvars
    vss <- transVarDecls vardecls
    return $ vs ++ vss


transNodeDecls :: Abs.NodeDecls -> Result (Map Identifier Node)
transNodeDecls x = case x of
  Abs.NoNodes  -> return Map.empty
  Abs.JustNodeDecls nodes  -> fmap Map.fromList $ mapM transNode nodes


transStateDecls :: Abs.StateDecls -> Result [Variable]
transStateDecls x = case x of
  Abs.NoStateDecls  -> return []
  Abs.JustStateDecls vardecls  -> transVarDecls vardecls


transLocalDecls :: Abs.LocalDecls -> Result [Variable]
transLocalDecls x = case x of
  Abs.NoLocals  -> return []
  Abs.JustLocalDecls vardecls  -> transVarDecls vardecls


transFlow :: Abs.Flow -> Result Flow
transFlow x = case x of
  Abs.Flow localdefinitions transitions  ->
    Flow <$>
      (transLocalDefinitions localdefinitions) <*>
      (transTransitions transitions)

transLocalDefinitions :: Abs.LocalDefinitions -> Result [InstantDefinition]
transLocalDefinitions x = case x of
  Abs.NoLocalDefinitons  -> return []
  Abs.JustLocalDefinitons instantdefinitions  -> mapM transInstantDefinition instantdefinitions


transTransitions :: Abs.Transitions -> Result [StateTransition]
transTransitions x = case x of
  Abs.NoTransitions  -> return []
  Abs.JustTransitions transitions  -> mapM transTransition transitions


transOutputs :: Abs.Outputs -> Result [InstantDefinition]
transOutputs x = case x of
  Abs.NoOutputs  -> return []
  Abs.JustOutputs instantdefinitions  -> mapM transInstantDefinition instantdefinitions


transInstantDefinition :: Abs.InstantDefinition -> Result InstantDefinition
transInstantDefinition x = case x of
  Abs.InstantDef pattern expr  ->
    InstantDef <$> (transPattern pattern) <*> (transExpr expr)


transTransition :: Abs.Transition -> Result StateTransition
transTransition x = case x of
  Abs.Transition stateid expr  ->
    StateTransition <$> (transStateId stateid) <*> (transExpr expr)


transPattern :: Abs.Pattern -> Result Pattern
transPattern x = case x of
  Abs.SinglePattern identifier  -> (:[]) <$> (transIdentifier identifier)
  Abs.ProductPattern list2id  -> transList2Id list2id

transList2Id :: Abs.List2Id -> Result [Identifier]
transList2Id x = case x of
  Abs.Id2 identifier0 identifier  -> do
    ident1 <- transIdentifier identifier0
    ident2 <- transIdentifier identifier
    return [ident1, ident2]
  Abs.ConsId identifier list2id  -> (:) <$> (transIdentifier identifier) <*> (transList2Id list2id)


transControlStructure :: Abs.ControlStructure -> Result [Automaton]
transControlStructure x = case x of
  Abs.ControlStructure automatons  -> mapM transAutomaton automatons


transAutomaton :: Abs.Automaton -> Result Automaton
transAutomaton x = case x of
  Abs.Automaton locations initiallocation edges  -> do
    locs <- mapM transLocation locations
    Automaton locs <$>
      (transInitialLocation locs initiallocation) <*>
      (mapM (transEdge locs) edges)


transLocation :: Abs.Location -> Result Location
transLocation x = case x of
  Abs.Location identifier flow  ->
    Location <$> (transIdentifier identifier) <*> (transFlow flow)

isKnownLocation :: [Location] -> LocationId -> Result ()
isKnownLocation locs loc =
  when (not $ any (\(Location l _) -> l == loc) locs)
    (throwError $ "Unknown location " ++ prettyIdentifier loc)

transInitialLocation :: [Location] -> Abs.InitialLocation -> Result LocationId
transInitialLocation locs x = case x of
  Abs.InitialLocation identifier  -> do
    loc <- transIdentifier identifier
    isKnownLocation locs loc
    return loc


transEdge :: [Location] -> Abs.Edge -> Result Edge
transEdge locs x = case x of
  Abs.Edge identifier0 identifier expr  -> do
    t <- transIdentifier identifier0
    isKnownLocation locs t
    h <- transIdentifier identifier
    isKnownLocation locs h
    e <- transExpr expr
    return $ Edge t h e


transAtom :: Abs.Atom -> Result Atom
transAtom x = case x of
  Abs.AtomConst constant  -> Fix . AtomConst <$> transConstant constant
  Abs.AtomVar identifier  -> Fix . AtomVar <$> transIdentifier identifier

transExpr :: Abs.Expr -> Result Expr
transExpr = fmap Fix . transExpr'
  where
    transExpr' x = case x of
      Abs.AtExpr atom -> (AtExpr . unfix) <$> transAtom atom

      Abs.Expr1 Abs.Not expr ->
        LogNot <$> (transExpr expr)

      Abs.Expr2 binop expr0 expr ->
        Expr2 <$> transBinOp binop <*> transExpr expr0 <*> transExpr expr

      Abs.Expr3 Abs.Ite expr0 expr1 expr  ->
        Ite <$> transExpr expr0 <*> transExpr expr1 <*> transExpr expr

      Abs.Constr identifier exprs  ->
        Constr <$> (RecordConstr <$> transIdentifier identifier <*> mapM transExpr exprs)

      Abs.Project identifier natural  ->
        Project <$> transIdentifier identifier <*> transNatural natural

      Abs.Select identifier0 identifier  -> $notImplemented

      Abs.NodeUsage identifier exprs  ->
        NodeUsage <$> transIdentifier identifier <*> mapM transExpr exprs


transBinOp :: Abs.BinOp -> Result BinOp
transBinOp = return . transBinOp'
  where
    transBinOp' :: Abs.BinOp -> BinOp
    transBinOp' x = case x of
      Abs.Or  -> Or
      Abs.And  -> And
      Abs.Xor  -> Xor
      Abs.Implies  -> Implies
      Abs.Equals  -> Equals
      Abs.Less  -> Less
      Abs.Greater  -> Greater
      Abs.LEq  -> LEq
      Abs.GEq  -> GEq
      Abs.Plus  -> Plus
      Abs.Minus  -> Minus
      Abs.Mul  -> Mul
      Abs.RealDiv  -> RealDiv
      Abs.IntDiv  -> IntDiv
      Abs.Mod  -> Mod

