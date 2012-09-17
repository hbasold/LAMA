module Definition where

import Data.Array as Arr

import Language.SMTLib2 as SMT

import LamaSMTTypes

data Definition =
  SingleDef (Stream Bool)
  | ProdDef (Array Int Definition)
  deriving Show

ensureDefinition :: TypedStream i -> Definition
ensureDefinition (BoolStream s) = SingleDef s
ensureDefinition (ProdStream ps) = ProdDef $ fmap ensureDefinition ps
ensureDefinition s = error $ "ensureDefinition: not a boolean stream: " ++ show s

assertDefinition :: MonadSMT m => (SMTExpr Bool -> SMTExpr Bool) -> StreamPos -> Definition -> m ()
assertDefinition f i (SingleDef s) = liftSMT $ assert (f $ s `app` i)
assertDefinition f i (ProdDef ps) = mapM_ (assertDefinition f i) $ Arr.elems ps

data ProgDefs = ProgDefs
                { flowDef :: [Definition]
                , precondition :: Definition
                , invariantDef :: Definition
                }