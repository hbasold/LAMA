{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module TransformEnv where

import Development.Placeholders

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Types
import Language.SMTLib2 as SMT
import Data.Unit

import Data.Array as Arr
import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable

import Control.Monad.State (StateT(..), MonadState(..), modify, gets)
import Control.Monad.Error (ErrorT(..), MonadError(..))

import SMTEnum
import LamaSMTTypes

data NodeEnv i = NodeEnv
                 { nodeEnvIn :: [TypedStream i]
                 , nodeEnvOut :: [TypedStream i]
                 , nodeEnvVars :: VarEnv i
                 }

data VarEnv i = VarEnv
                { nodes :: Map i (NodeEnv i)
                  -- | Maps names of variables to a SMT expression for using that variable
                , vars :: Map i (TypedStream i)
                }

data Env i = Env
           { constants :: Map i (TypedExpr i)
           , enumAnn :: Map i (SMTAnnotation SMTEnum)
           , enumConsAnn :: Map (EnumConstr i) (SMTAnnotation SMTEnum)
           , varEnv :: VarEnv i
           , currAutomatonIndex :: Integer
           }

emptyVarEnv :: VarEnv i
emptyVarEnv = VarEnv Map.empty Map.empty

emptyEnv :: Env i
emptyEnv = Env Map.empty Map.empty Map.empty emptyVarEnv 0

type DeclM i = StateT (Env i) (ErrorT String SMT)

putConstants :: Ident i => Map i (Constant i) -> DeclM i ()
putConstants cs =
  let cs' = fmap trConstant cs
  in modify $ \env -> env { constants = cs' }

putEnumAnn :: Ident i => Map i (SMTAnnotation SMTEnum) -> DeclM i ()
putEnumAnn eAnns =
  modify $ \env -> env { enumAnn = (enumAnn env) `Map.union` eAnns }

putEnumConsAnn :: Ident i => Map (EnumConstr i) (SMTAnnotation SMTEnum) -> DeclM i ()
putEnumConsAnn consAnns =
  modify $ \env -> env { enumConsAnn = (enumConsAnn env) `Map.union` consAnns }

modifyVarEnv :: (VarEnv i -> VarEnv i) -> DeclM i ()
modifyVarEnv f = modify $ \env -> env { varEnv = f $ varEnv env }

modifyNodes :: (Map i (NodeEnv i) -> Map i (NodeEnv i)) -> DeclM i ()
modifyNodes f = modifyVarEnv $ (\env -> env { nodes = f $ nodes env })

modifyVars :: (Map i (TypedStream i) -> Map i (TypedStream i)) -> DeclM i ()
modifyVars f = modifyVarEnv $ (\env -> env { vars = f $ vars env })

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

lookupVar :: (MonadState (Env i) m, MonadError String m, Ident i) => i -> m (TypedStream i)
lookupVar x = gets (vars . varEnv) >>= lookupErr ("Unknown variable " ++ identPretty x) x

lookupNode :: Ident i => i -> DeclM i (NodeEnv i)
lookupNode n = gets (nodes . varEnv) >>= lookupErr ("Unknown node " ++ identPretty n) n

lookupEnumAnn :: (MonadState (Env i) m, MonadError String m, Ident i) => i -> m (SMTAnnotation SMTEnum)
lookupEnumAnn t = gets enumAnn >>= lookupErr ("Unknown enum " ++ identPretty t) t

lookupEnumConsAnn :: Ident i => EnumConstr i -> DeclM i (SMTAnnotation SMTEnum)
lookupEnumConsAnn x = gets enumConsAnn >>= lookupErr ("Unknown enum constructor " ++ identPretty x) x

localVarEnv :: (VarEnv i -> VarEnv i) -> DeclM i a -> DeclM i a
localVarEnv f m =
  do curr <- get
     modifyVarEnv f
     r <- m
     put curr
     return r

nextAutomatonIndex :: MonadState (Env i) m => m Integer
nextAutomatonIndex = state $ \env ->
  let i = currAutomatonIndex env
  in (i, env { currAutomatonIndex = i+1 })

-- | Defines a stream analogous to defFun.
defStream :: Ident i => Type i -> (StreamPos -> TypedExpr i) -> DeclM i (TypedStream i)
defStream (GroundType BoolT) f = liftSMT . fmap BoolStream $ defFun (unBool' . f)
defStream (GroundType IntT) f = liftSMT . fmap IntStream $ defFun (unInt . f)
defStream (GroundType RealT) f = liftSMT . fmap RealStream $ defFun (unReal . f)
defStream (GroundType _) f = $notImplemented
defStream (EnumType t) f = lookupEnumAnn t >>= \a -> liftSMT . fmap EnumStream $ defFunAnn unit a (unEnum . f)
-- We have to pull the product out of a stream.
-- If we are given a function f : StreamPos -> (Ix -> TE) = TypedExpr as above,
-- we would like to have as result something like:
-- g : Ix -> (StreamPos -> TE)
-- g(i)(t) = defStream(λt'.f(t')(i))(t)
-- Here i is the index into the product and t,t' are time variables.
defStream (ProdType ts) f =
  do let u = length ts - 1
     x <- mapM (\(ty, i) -> defStream ty ((! i) . unProd' . f)) $ zip ts [0..u]
     return . ProdStream $ listArray (0,u) x

trConstant :: Ident i => Constant i -> TypedExpr i
trConstant (untyped -> BoolConst c) = BoolExpr $ constant c
trConstant (untyped -> IntConst c) = IntExpr $ constant c
trConstant (untyped -> RealConst c) = RealExpr $ constant c
trConstant (untyped -> SIntConst n c) = $notImplemented
trConstant (untyped -> UIntConst n c) = $notImplemented