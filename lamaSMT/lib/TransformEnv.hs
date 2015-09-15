{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module TransformEnv where

import Development.Placeholders

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Types
import Language.SMTLib2 as SMT

import Data.Array as Arr
import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable
import Data.List (replicate)

import Control.Monad.State (StateT(..), MonadState(..), modify, gets)
import Control.Monad.Error (ErrorT(..), MonadError(..))

import Unit
import SMTEnum
import NatInstance
import LamaSMTTypes
import Internal.Monads

data NodeEnv i = NodeEnv
                 { nodeEnvIn :: [TypedExpr i]
                 , nodeEnvOut :: Map i (TypedExpr i)
                 , nodeEnvVars :: VarEnv i
                 }

data VarEnv i = VarEnv
                { nodes :: Map i (NodeEnv i)
                , vars :: Map i (TypedExpr i)
                  -- ^ Maps names of variables to a SMT expression for using
                  -- that variable
                }

data Env i = Env
           { constants :: Map i (TypedExpr i)
           , enumAnn :: Map i (SMTAnnotation SMTEnum)
           , enumConsAnn :: Map (EnumConstr i) (SMTAnnotation SMTEnum)
           , varEnv :: VarEnv i
           , currAutomatonIndex :: Integer
           , natImpl :: NatImplementation
           , enumImpl :: EnumImplementation
           }

emptyVarEnv :: VarEnv i
emptyVarEnv = VarEnv Map.empty Map.empty

emptyEnv :: NatImplementation -> EnumImplementation -> Env i
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

modifyVars :: (Map i (TypedExpr i) -> Map i (TypedExpr i)) -> DeclM i ()
modifyVars f = modifyVarEnv $ (\env -> env { vars = f $ vars env })

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

lookupVar :: (MonadState (Env i) m, MonadError String m, Ident i) => i -> m (TypedExpr i)
lookupVar x = gets (vars . varEnv) >>= lookupErr ("Unknown variable " ++ identPretty x) x

lookupNode :: Ident i => i -> DeclM i (NodeEnv i)
lookupNode n
  = gets (nodes . varEnv)
    >>= lookupErr ("Unknown node " ++ identPretty n) n

lookupEnumAnn :: (MonadState (Env i) m, MonadError String m, Ident i) =>
                 i -> m (SMTAnnotation SMTEnum)
lookupEnumAnn t
  = gets enumAnn >>=
    lookupErr ("Unknown enum " ++ identPretty t) t

lookupEnumConsAnn :: Ident i => EnumConstr i -> DeclM i (SMTAnnotation SMTEnum)
lookupEnumConsAnn x
  = gets enumConsAnn
    >>= lookupErr ("Unknown enum constructor " ++ identPretty x) x

localVarEnv :: (VarEnv i -> VarEnv i) -> DeclM i a -> DeclM i a
localVarEnv f m =
  do curr <- gets varEnv
     modifyVarEnv f
     r <- m
     modifyVarEnv (const curr)
     return r

nextAutomatonIndex :: MonadState (Env i) m => m Integer
nextAutomatonIndex = state $ \env ->
  let i = currAutomatonIndex env
  in (i, env { currAutomatonIndex = i+1 })

-- | Defines a stream analogous to defFun.
defStream :: Ident i =>
             Type i -> (StreamPos -> TypedExpr i) -> DeclM i (TypedStream i)
defStream ty sf = gets natImpl >>= \natAnn -> defStream' natAnn ty sf
  where
    defStream' :: Ident i =>
                  NatImplementation -> Type i -> (StreamPos -> TypedExpr i)
                  -> DeclM i (TypedStream i)
    defStream' natAnn (GroundType BoolT) f
      = liftSMT . fmap BoolStream $ defFunAnn natAnn (unBool' . f)
    defStream' natAnn (GroundType IntT) f
      = liftSMT . fmap IntStream $ defFunAnn natAnn (unInt . f)
    defStream' natAnn (GroundType RealT) f
      = liftSMT . fmap RealStream $ defFunAnn natAnn (unReal . f)
    defStream' natAnn (GroundType _) f = $notImplemented
    defStream' natAnn (EnumType alias) f
      = do ann <- lookupEnumAnn alias
           liftSMT $ fmap (EnumStream ann) $ defFunAnn natAnn (unEnum . f)
    -- We have to pull the product out of a stream.
    -- If we are given a function f : StreamPos -> (Ix -> TE) = TypedExpr as above,
    -- we would like to have as result something like:
    -- g : Ix -> (StreamPos -> TE)
    -- g(i)(t) = defStream(λt'.f(t')(i))(t)
    -- Here i is the index into the product and t,t' are time variables.
    defStream' natAnn (ProdType ts) f =
      do let u = length ts - 1
         x <- mapM defParts $ zip ts [0..u]
         return . ProdStream $ listArray (0,u) x
      where defParts (ty2, i) = defStream' natAnn ty2 ((! i) . unProd' . f)

-- | Defines a function instead of streams
defFunc :: Ident i =>
             Int -> Type i -> ([SMTExpr Bool] -> TypedExpr i) -> DeclM i (TypedFunc i)
defFunc i (GroundType BoolT) f = liftSMT . fmap BoolFunc $
                                defFunAnn (replicate i ()) (unBool' . f)
defFunc i (GroundType IntT) f = liftSMT . fmap IntFunc $
                                defFunAnn (replicate i ()) (unInt . f)
defFunc i (GroundType RealT) f = liftSMT . fmap RealFunc $
                               defFunAnn (replicate i ()) (unReal . f)
defFunc i (GroundType _) f = $notImplemented
defFunc i (EnumType alias) f = do ann <- lookupEnumAnn alias
                                  liftSMT $ fmap (EnumFunc ann) $
                                   defFunAnn (replicate i ()) (unEnum . f)
-- We have to pull the product out of a stream.
-- If we are given a function f : FuncPos -> (Ix -> TE) = TypedExpr as above,
-- we would like to have as result something like:
-- g : Ix -> (FuncPos -> TE)
-- g(i)(t) = defFunc(λt'.f(t')(i))(t)
-- Here i is the index into the product and t,t' are time variables.
defFunc i (ProdType ts) f =
  do let u = length ts - 1
     x <- mapM defParts $ zip ts [0..u]
     return . ProdFunc $ listArray (0,u) x
  where defParts (ty2, i) = defFunc i ty2 ((! i) . unProd' . f)

-- stream :: Ident i => Type i -> DeclM i (Stream t)

trConstant :: Ident i => Constant i -> TypedExpr i
trConstant (untyped -> BoolConst c) = BoolExpr $ constant c
trConstant (untyped -> IntConst c) = IntExpr $ constant c
trConstant (untyped -> RealConst c) = RealExpr $ constant c
trConstant (untyped -> SIntConst n c) = $notImplemented
trConstant (untyped -> UIntConst n c) = $notImplemented
