{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-}

module Lang.LAMA.Typing.Environment where

import qualified Data.Map as Map
import Data.Map (Map)

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
  getTypeDef :: e -> (TypeAlias i) -> Maybe (TypeDef i)
  getConstant :: e -> i -> Maybe (Constant i)
  getVarType :: e -> i -> Maybe (Type i, VarUsage)
  getNode :: e -> i -> Maybe (Node i)

  emptyEnv :: e   -- ^ Generate empty environment

class (Ident i, Environment i e) => DynEnvironment i e | e -> i where
  addType :: e -> (TypeAlias i) -> (TypeDef i) -> e
  addVar :: e -> i -> (Type i, VarUsage) -> e
  addNode :: e -> i -> (Node i) -> e
  addConstant :: e -> i -> (Constant i) -> e

  addTypes :: e -> Map (TypeAlias i) (TypeDef i) -> e
  addVars :: e -> Map i (Type i, VarUsage) -> e
  addNodes :: e -> Map i (Node i) -> e
  addConstants :: e -> Map i (Constant i) -> e

  emptyDecls :: e -> e

  -- Default impementation in terms of single adders
  addTypes env = foldl (uncurry2 addType) env . Map.toList
  addVars env = foldl (uncurry2 addVar) env . Map.toList
  addNodes env = foldl (uncurry2 addNode) env . Map.toList
  addConstants env = foldl (uncurry2 addConstant) env . Map.toList

uncurry2 :: (a -> b -> c -> d) -> (a -> (b, c) -> d)
uncurry2 f a (b, c) = f a b c

-- | Environment which holds declared types, constants and variables
data Env i = Env {
    envTypes :: Map (TypeAlias i) (TypeDef i),
    envConsts :: Map i (Constant i),
    envVars :: Map i (Type i, VarUsage),
    envNodes :: Map i (Node i)
  }

instance Ident i => Environment i (Env i) where
  getTypeDef e x = Map.lookup x (envTypes e)
  getVarType e x = Map.lookup x (envVars e)
  getNode e n = Map.lookup n (envNodes e)
  getConstant e c = Map.lookup c (envConsts e)

  emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

instance Ident i => DynEnvironment i (Env i) where
  addType env x t = env { envTypes = Map.insert x t $ envTypes env }
  addVar env x t = env { envVars = Map.insert x t $ envVars env }
  addNode env n d = env { envNodes = Map.insert n d $ envNodes env }
  addConstant env x c = env { envConsts = Map.insert x c $ envConsts env }

  emptyDecls (Env ts cs _ _) = Env ts cs Map.empty Map.empty

-- | Lookup a record type
envLookupRecordType :: (Environment i e, MonadReader e m) => (TypeAlias i) -> m (RecordT i)
envLookupRecordType ident = do
  env <- ask
  case getTypeDef env ident of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just (RecordDef t) -> return t
    _ -> fail $ show ident ++ " is not a record type"


-- | Lookup a type
envLookupType :: (Environment i e, MonadReader e m) => (TypeAlias i) -> m (TypeDef i)
envLookupType ident = do
  env <- ask
  case getTypeDef env ident of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just t -> return t

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
envAddTypes :: (DynEnvironment i e, MonadReader e m) => Map (TypeAlias i) (TypeDef i) -> m a -> m a
envAddTypes ts = local $ (\env -> addTypes env ts)

-- | Adds a type to in the environment
envAddType :: (DynEnvironment i e, MonadReader e m) => (TypeAlias i) -> (TypeDef i) -> m a -> m a
envAddType ident t = local $ (\env -> addType env ident t)

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

envEmptyDecls :: (DynEnvironment i e, MonadReader e m) => m a -> m a
envEmptyDecls = local emptyDecls

