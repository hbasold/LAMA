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
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable

import Control.Monad.State (StateT(..), MonadState(..), modify, gets)
import Control.Monad.Error (ErrorT(..), MonadError(..))

import SMTEnum
import NatInstance
import LamaSMTTypes
import Definition
import Posets
import Internal.Monads

data NodeEnv i = NodeEnv
                 { nodeEnvIn :: [TypedExpr]
                 , nodeEnvOut :: [(i, TypedExpr)]
                 , nodeEnvVars :: VarEnv i
                 }

data VarEnv i = VarEnv
                { nodes :: Map i (NodeEnv i)
                , vars :: Map i (TypedExpr)
                  -- ^ Maps names of variables to a SMT expression for using
                  -- that variable
                }

data Env i = Env
           { constants :: Map i (TypedExpr)
           , enumAnn :: Map i (SMTAnnotation SMTEnum)
           , enumConsAnn :: Map (EnumConstr i) (SMTAnnotation SMTEnum)
           , varEnv :: VarEnv i
           , currAutomatonIndex :: Integer
           , varList :: [TypedExpr]
           , instSetBool :: [Term]
           , instSetInt :: [Term]
           , natImpl :: NatImplementation
           , enumImpl :: EnumImplementation
           }

-- | Gets an "undefined" value for a given type of expression.
-- The expression itself is not further analysed.
-- FIXME: Make behaviour configurable, i.e. bottom can be some
-- default value or a left open stream
-- (atm it does the former).
getBottom :: TypedExpr -> TypedExpr
getBottom (BoolExpr _)     = BoolExpr $ constant False
getBottom (IntExpr _)      = IntExpr  $ constant 0xdeadbeef
getBottom (RealExpr _)     = RealExpr . constant $ fromInteger 0xdeadbeef
getBottom (EnumExpr e) = EnumExpr e --evtl. TODO
getBottom (ProdExpr strs)  = ProdExpr $ fmap getBottom strs

emptyVarEnv :: VarEnv i
emptyVarEnv = VarEnv Map.empty Map.empty

emptyEnv :: NatImplementation -> EnumImplementation -> Env i
emptyEnv = Env Map.empty Map.empty Map.empty emptyVarEnv 0 [] [] []

type DeclM i = StateT (Env i) (ErrorT String SMT)

putConstants :: Ident i => Map i (Constant i) -> DeclM i ()
putConstants cs =
  let cs' = fmap trConstant cs
  in modify $ \env -> env { constants = cs' }

putVar :: Ident i => TypedExpr -> DeclM i ()
putVar var =
  modify $ \env -> env { varList = (varList env) ++ [var] }

getN :: TypedExpr -> DeclM i Int
getN x = do vars <- gets varList
            return $ case List.elemIndex x vars of
                          Nothing -> error $ "Could not be found in list of variables: " ++ show x
                          Just n -> n

putTerm :: Ident i => TypedExpr -> DeclM i ()
putTerm e@(BoolExpr s) = do
  n <- getN e
  modify $ \env -> env { instSetBool = instSetBool env ++ [BoolTerm n] }
putTerm e@(IntExpr s) = do
  n <- getN e
  modify $ \env -> env { instSetInt = instSetInt env ++ [IntTerm n] }
putTerm _ = return ()

getTypedValue :: MonadSMT m => TypedExpr -> m (TypedExpr)
getTypedValue (BoolExpr s) = liftSMT $ getValue s >>= return . BoolExpr . constant
getTypedValue (IntExpr s) = liftSMT $ getValue s >>= return . IntExpr . constant
getTypedValue e = liftSMT $ return $ getBottom e

evalBoolTerm :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> Term -> m Bool
evalBoolTerm i (BoolTerm f) = liftSMT $ getValue $ unBool $ head $ lookupArgs [f] False i

evalIntTerm :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> Term -> m Integer
evalIntTerm i (IntTerm f) = liftSMT $ getValue $ unInt $ head $ lookupArgs [f] False i

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

modifyVars :: (Map i (TypedExpr) -> Map i (TypedExpr)) -> DeclM i ()
modifyVars f = modifyVarEnv $ (\env -> env { vars = f $ vars env })

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

lookupVar :: (MonadState (Env i) m, MonadError String m, Ident i) => i -> m (TypedExpr)
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

-- | Defines a function instead of streams
defFunc :: Ident i =>
            Type i -> [TypedAnnotation] -> ([TypedExpr] -> TypedExpr) -> DeclM i (TypedFunc)
defFunc (GroundType BoolT) ann f = liftSMT . fmap BoolFunc $
                                defFunAnn ann (unBool' . f)
defFunc (GroundType IntT) ann f = liftSMT . fmap IntFunc $
                                defFunAnn ann (unInt . f)
defFunc (GroundType RealT) ann f = liftSMT . fmap RealFunc $
                               defFunAnn ann (unReal . f)
defFunc (GroundType _) ann f = $notImplemented
defFunc (EnumType alias) ann f = do eann <- lookupEnumAnn alias
                                    liftSMT $ fmap (EnumFunc eann) $
                                      defFunAnn ann (unEnum . f)
-- We have to pull the product out of a function
defFunc (ProdType ts) ann f =
  do let u = length ts - 1
     x <- mapM defParts $ zip ts [0..u]
     return . ProdFunc $ listArray (0,u) x
  where defParts (ty2, i) = defFunc ty2 ann ((! i) . unProd' . f)

trConstant :: Ident i => Constant i -> TypedExpr
trConstant (untyped -> BoolConst c) = BoolExpr $ constant c
trConstant (untyped -> IntConst c) = IntExpr $ constant c
trConstant (untyped -> RealConst c) = RealExpr $ constant c
trConstant (untyped -> SIntConst n c) = $notImplemented
trConstant (untyped -> UIntConst n c) = $notImplemented
