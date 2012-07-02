{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-}

module Lang.LAMA.Typing.Environment where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader.Class

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure

data VarUsage = Input | Output | Local | State

readable :: VarUsage -> Bool
readable Input = True
readable Output = False
readable Local = True
readable State = True

writable :: VarUsage -> Bool
writable Input = False
writable Output = True
writable State = True
writable Local = True

--- Accessing and manipulating an environment -----

class Ident i => Environment i e | e -> i where
  getEnum :: e -> (EnumConstr i) -> Maybe (Type i)
  isEnum :: e -> i -> Bool
  getConstant :: e -> i -> Maybe (Constant i)
  getVarType :: e -> i -> Maybe (Type i, VarUsage)
  getNode :: e -> i -> Maybe (Node i)

  emptyEnv :: e   -- ^ Generate empty environment

class (Ident i, Environment i e) => DynEnvironment i e | e -> i where
  addEnum :: e -> (TypeAlias i) -> (EnumDef i) -> e
  addVar :: e -> i -> (Type i, VarUsage) -> e
  addNode :: e -> i -> (Node i) -> e
  addConstant :: e -> i -> (Constant i) -> e

  addEnums :: e -> Map (TypeAlias i) (EnumDef i) -> e
  addVars :: e -> Map i (Type i, VarUsage) -> e
  addNodes :: e -> Map i (Node i) -> e
  addConstants :: e -> Map i (Constant i) -> e

  emptyDecls :: e -> e

  -- Default impementation in terms of single adders
  addEnums env = foldl (uncurry2 addEnum) env . Map.toList
  addVars env = foldl (uncurry2 addVar) env . Map.toList
  addNodes env = foldl (uncurry2 addNode) env . Map.toList
  addConstants env = foldl (uncurry2 addConstant) env . Map.toList

uncurry2 :: (a -> b -> c -> d) -> (a -> (b, c) -> d)
uncurry2 f a (b, c) = f a b c

-- | Environment which holds declared types, constants and variables
data Env i = Env {
    envCtors :: Map (EnumConstr i) (Type i),
    envEnums :: Set (TypeAlias i),
    envConsts :: Map i (Constant i),
    envVars :: Map i (Type i, VarUsage),
    envNodes :: Map i (Node i)
  }

instance Ident i => Environment i (Env i) where
  getEnum e x = Map.lookup x (envCtors e)
  isEnum e x = x `Set.member` (envEnums e)
  getVarType e x = Map.lookup x (envVars e)
  getNode e n = Map.lookup n (envNodes e)
  getConstant e c = Map.lookup c (envConsts e)

  emptyEnv = Env Map.empty Set.empty Map.empty Map.empty Map.empty

instance Ident i => DynEnvironment i (Env i) where
  addEnum env x (EnumDef cs)
    = env {
        envCtors = foldl (\enums c -> Map.insert c (EnumType x) enums) (envCtors env) cs,
        envEnums = Set.insert x $ envEnums env
      }
  addVar env x t = env { envVars = Map.insert x t $ envVars env }
  addNode env n d = env { envNodes = Map.insert n d $ envNodes env }
  addConstant env x c = env { envConsts = Map.insert x c $ envConsts env }

  emptyDecls (Env ts es cs _ _) = Env ts es cs Map.empty Map.empty

-- | Lookup the type of an enum constructor
envLookupEnum :: (Environment i e, MonadReader e m) => EnumConstr i -> m (Type i)
envLookupEnum ident = do
  env <- ask
  case getEnum env ident of
    Nothing -> fail $ "Undefined enum constructor " ++ show ident
    Just t -> return t

envIsEnum :: (Environment i e, MonadReader e m) => TypeAlias i -> m Bool
envIsEnum x = ask >>= return . (flip isEnum x)

-- | Lookup a variable that needs to be read
envLookupReadable :: (Ident i, Environment i e, MonadReader e m) => i -> m (Type i)
envLookupReadable ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> case getConstant env ident of
      Nothing -> fail $ "Undefined variable " ++ identPretty ident
      Just c -> return $ getType c
    Just (t, u) -> if readable u then return t
                    else fail $ "Variable " ++ identPretty ident ++ " not readable"

-- | Lookup a variable that needs to be written
envLookupWritable :: (Ident i, Environment i e, MonadReader e m) => i -> m (Type i)
envLookupWritable ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> fail $ "Undefined variable " ++ identPretty ident
    Just (t, u) -> if writable u then return t
                    else fail $ "Variable " ++ identPretty ident ++ " not writable"

-- | Lookup a state variable
envLookupState :: (Ident i, Environment i e, MonadReader e m) => i -> m (Type i)
envLookupState ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> fail $ "Undefined variable " ++ identPretty ident
    Just (t, State) -> return t
    _ -> fail $ "Variable " ++ identPretty ident ++ " is not a state variable"

-- | Lookup a state variable
envLookupNodeSignature :: (Ident i, Environment i e, MonadReader e m) => i -> m ([Variable i], [Variable i])
envLookupNodeSignature ident = do
  env <- ask
  case getNode env ident of
    Nothing -> fail $ "Undefined nodes " ++ identPretty ident
    Just n -> return (nodeInputs n, nodeOutputs n)

variableMap :: Ident i => VarUsage -> [Variable i] -> Map i (Type i, VarUsage)
variableMap u = Map.fromList . map splitVar
  where splitVar (Variable ident t) = (ident, (t, u))

-- | Add types to the environment
envAddEnums :: (DynEnvironment i e, MonadReader e m) => Map (TypeAlias i) (EnumDef i) -> m a -> m a
envAddEnums ts = local $ (\env -> addEnums env ts)

-- | Adds a type to in the environment
envAddEnum :: (DynEnvironment i e, MonadReader e m) => (TypeAlias i) -> (EnumDef i) -> m a -> m a
envAddEnum ident t = local $ (\env -> addEnum env ident t)

-- | Adds constants to the environment
envAddConsts :: (Ident i, DynEnvironment i e, MonadReader e m) => Map i (Constant i) -> m a -> m a
envAddConsts cs = local $ (\env -> addConstants env cs)

-- | Add scoped variables to the environment
envAddLocal :: (Ident i, DynEnvironment i e, MonadReader e m) => Map i (Type i, VarUsage) -> m a -> m a
envAddLocal vars = local $ (\env -> addVars env vars)

-- | Set the nodes in the environment
envAddNodes :: (Ident i, DynEnvironment i e, MonadReader e m) => Map i (Node i) -> m a -> m a
envAddNodes ns = local $ (\env -> addNodes env ns)

envAddDecls :: (DynEnvironment i e, MonadReader e m) => Declarations i -> m a -> m a
envAddDecls decls =
  let vars = (variableMap State $ declsState decls) `Map.union` (variableMap Local $ declsLocal decls)
      localNodes = declsNode decls
  in (envAddLocal vars) . (envAddNodes localNodes)

envAddVariables :: (DynEnvironment i e, MonadReader e m) => VarUsage -> [Variable i] -> m a -> m a
envAddVariables u = envAddLocal . (variableMap u)

envEmptyDecls :: (DynEnvironment i e, MonadReader e m) => m a -> m a
envEmptyDecls = local emptyDecls

