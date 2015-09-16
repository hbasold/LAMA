module Definition where

import Data.Array as Arr
import qualified Data.Map as Map
import Data.Map (Map)

import Language.SMTLib2 as SMT

import Lang.LAMA.Identifier

import LamaSMTTypes
import TransformEnv
import Internal.Monads

data Definition i =
  SingleDef [i] (SMTFunction [SMTExpr Bool] Bool)
  | ProdDef (Array Int (Definition i))
  deriving Show

ensureDefinition :: [i] -> TypedFunc i -> Definition i
ensureDefinition al (BoolFunc s) = SingleDef al s
ensureDefinition al (ProdFunc ps) = ProdDef $ fmap (ensureDefinition al) ps
ensureDefinition al _
  = error $ "ensureDefinition: not a boolean function" -- : " ++ show s

assertDefinition :: (Ident i, MonadSMT m) =>
                    (SMTExpr Bool -> SMTExpr Bool)
                    -> VarEnv i
                    -> Definition i
                    -> m ()
assertDefinition f env (SingleDef al s) = liftSMT $ assert (f $ s `app` (lookupArgs al env))
assertDefinition f env (ProdDef ps) = mapM_ (assertDefinition f env) $ Arr.elems ps

lookupArgs :: Ident i => [i] -> VarEnv i -> [SMTExpr Bool]
lookupArgs al env = map (lookupArgs' env) al
  where
    lookupArgs' env i = case Map.lookup i (vars env) of
                          Just x -> unBool' x
                          Nothing -> error "bla"--(flip lookupArgs' $ i) . nodeEnvVars $ Map.elems (nodes env)


data ProgDefs i = ProgDefs
                { flowDef :: [Definition i]
                , precondition :: Definition i
                , invariantDef :: Definition i
                }
