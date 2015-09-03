module Definition where

import Data.Array as Arr

import Language.SMTLib2 as SMT

import LamaSMTTypes
import Internal.Monads

data Definition =
  SingleDef (SMTFunction [SMTExpr Bool] Bool)
  | ProdDef (Array Int Definition)
  deriving Show

ensureDefinition :: TypedFunc i -> Definition
ensureDefinition (BoolFunc s) = SingleDef s
ensureDefinition (ProdFunc ps) = ProdDef $ fmap ensureDefinition ps
ensureDefinition _
  = error $ "ensureDefinition: not a boolean function" -- : " ++ show s

assertDefinition :: MonadSMT m =>
                    (SMTExpr Bool -> SMTExpr Bool)
                    -> StreamPos
                    -> Definition
                    -> m ()
assertDefinition f i (SingleDef s) = do return ()--liftSMT $ assert (f $ s `app` i)
assertDefinition f i (ProdDef ps) = mapM_ (assertDefinition f i) $ Arr.elems ps

data ProgDefs = ProgDefs
                { flowDef :: [Definition]
                , precondition :: Definition
                , invariantDef :: Definition
                }
