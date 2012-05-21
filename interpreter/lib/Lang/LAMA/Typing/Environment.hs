{-# LANGUAGE FlexibleContexts #-}

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

class Environment e where
  getTypeDef :: e -> TypeAlias -> Maybe TypeDef
  getConstant :: e -> Identifier -> Maybe Constant
  getVarType :: e -> Identifier -> Maybe (Type, VarUsage)
  getNode :: e -> Identifier -> Maybe Node

  emptyEnv :: e   -- ^ Generate empty environment

class Environment e => DynEnvironment e where
  addType :: e -> TypeAlias -> TypeDef -> e
  addVar :: e -> Identifier -> (Type, VarUsage) -> e
  addNode :: e -> Identifier -> Node -> e
  addConstant :: e -> Identifier -> Constant -> e

  addTypes :: e -> Map TypeAlias TypeDef -> e
  addVars :: e -> Map Identifier (Type, VarUsage) -> e
  addNodes :: e -> Map Identifier Node -> e
  addConstants :: e -> Map Identifier Constant -> e

  emptyDecls :: e -> e

  -- Default impementation in terms of single adders
  addTypes env = foldl (uncurry2 addType) env . Map.toList
  addVars env = foldl (uncurry2 addVar) env . Map.toList
  addNodes env = foldl (uncurry2 addNode) env . Map.toList
  addConstants env = foldl (uncurry2 addConstant) env . Map.toList

uncurry2 :: (a -> b -> c -> d) -> (a -> (b, c) -> d)
uncurry2 f a (b, c) = f a b c

-- | Environment which holds declared types, constants and variables
data Env = Env {
    envTypes :: Map TypeAlias TypeDef,
    envConsts :: Map Identifier Constant,
    envVars :: Map Identifier (Type, VarUsage),
    envNodes :: Map Identifier Node
  }

instance Environment Env where
  getTypeDef e x = Map.lookup x (envTypes e)
  getVarType e x = Map.lookup x (envVars e)
  getNode e n = Map.lookup n (envNodes e)
  getConstant e c = Map.lookup c (envConsts e)

  emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

instance DynEnvironment Env where
  addType env x t = env { envTypes = Map.insert x t $ envTypes env }
  addVar env x t = env { envVars = Map.insert x t $ envVars env }
  addNode env n d = env { envNodes = Map.insert n d $ envNodes env }
  addConstant env x c = env { envConsts = Map.insert x c $ envConsts env }

  emptyDecls (Env ts cs _ _) = Env ts cs Map.empty Map.empty

-- | Lookup a record type
envLookupRecordType :: (Environment e, MonadReader e m) => TypeAlias -> m RecordT
envLookupRecordType ident = do
  env <- ask
  case getTypeDef env ident of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just (RecordDef t) -> return t
    _ -> fail $ show ident ++ " is not a record type"


-- | Lookup a type
envLookupType :: (Environment e, MonadReader e m) => TypeAlias -> m TypeDef
envLookupType ident = do
  env <- ask
  case getTypeDef env ident of
    Nothing -> fail $ "Undefined type " ++ show ident
    Just t -> return t

-- | Lookup a variable that needs to be read
envLookupReadable :: (Environment e, MonadReader e m) => Identifier -> m Type
envLookupReadable ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> case getConstant env ident of
      Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
      Just c -> return $ getType c
    Just (t, u) -> if readable u then return t
                    else fail $ "Variable " ++ prettyIdentifier ident ++ " not readable"

-- | Lookup a variable that needs to be written
envLookupWritable :: (Environment e, MonadReader e m) => Identifier -> m Type
envLookupWritable ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
    Just (t, u) -> if writable u then return t
                    else fail $ "Variable " ++ prettyIdentifier ident ++ " not writable"

-- | Lookup a state variable
envLookupState :: (Environment e, MonadReader e m) => Identifier -> m Type
envLookupState ident = do
  env <- ask
  case getVarType env ident of
    Nothing -> fail $ "Undefined variable " ++ prettyIdentifier ident
    Just (t, State) -> return t
    _ -> fail $ "Variable " ++ prettyIdentifier ident ++ " is not a state variable"

-- | Lookup a state variable
envLookupNodeSignature :: (Environment e, MonadReader e m) => Identifier -> m ([Variable], [Variable])
envLookupNodeSignature ident = do
  env <- ask
  case getNode env ident of
    Nothing -> fail $ "Undefined nodes " ++ prettyIdentifier ident
    Just n -> return (nodeInputs n, nodeOutputs n)

variableMap :: VarUsage -> [Variable] -> Map Identifier (Type, VarUsage)
variableMap u = Map.fromList . map splitVar
  where splitVar (Variable ident t) = (ident, (t, u))

-- | Add types to the environment
envAddTypes :: (DynEnvironment e, MonadReader e m) => Map TypeAlias TypeDef -> m a -> m a
envAddTypes ts = local $ (\env -> addTypes env ts)

-- | Adds a type to in the environment
envAddType :: (DynEnvironment e, MonadReader e m) => TypeAlias -> TypeDef -> m a -> m a
envAddType ident t = local $ (\env -> addType env ident t)

-- | Adds constants to the environment
envAddConsts :: (DynEnvironment e, MonadReader e m) => Map Identifier Constant -> m a -> m a
envAddConsts cs = local $ (\env -> addConstants env cs)

-- | Add scoped variables to the environment
envAddLocal :: (DynEnvironment e, MonadReader e m) => Map Identifier (Type, VarUsage) -> m a -> m a
envAddLocal vars = local $ (\env -> addVars env vars)

-- | Set the nodes in the environment
envAddNodes :: (DynEnvironment e, MonadReader e m) => Map Identifier Node -> m a -> m a
envAddNodes ns = local $ (\env -> addNodes env ns)

envAddDecls :: (DynEnvironment e, MonadReader e m) => Declarations -> m a -> m a
envAddDecls decls =
  let vars = (variableMap State $ declsState decls) `Map.union` (variableMap Local $ declsLocal decls)
      localNodes = Map.fromList $ map (\n -> (nodeName n, n)) (declsNode decls)
  in (envAddLocal vars) . (envAddNodes localNodes)

envEmptyDecls :: (DynEnvironment e, MonadReader e m) => m a -> m a
envEmptyDecls = local emptyDecls

