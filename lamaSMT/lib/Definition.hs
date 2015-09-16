module Definition where

import Data.Array as Arr

import Language.SMTLib2 as SMT

import LamaSMTTypes
import Internal.Monads

data Definition =
  SingleDef [Int] (SMTFunction [SMTExpr Bool] Bool)
  | ProdDef (Array Int Definition)
  deriving Show

ensureDefinition :: [Int] -> TypedFunc i -> Definition
ensureDefinition argN (BoolFunc s) = SingleDef argN s
ensureDefinition argN (ProdFunc ps) = ProdDef $ fmap (ensureDefinition argN) ps
ensureDefinition argN _
  = error $ "ensureDefinition: not a boolean function" -- : " ++ show s

assertDefinition :: MonadSMT m =>
                    (SMTExpr Bool -> SMTExpr Bool)
                    -> [SMTExpr Bool]
                    -> Definition
                    -> m ()
assertDefinition f i (SingleDef argN s) = liftSMT $ assert (f $ s `app` (lookupArgs argN i))
assertDefinition f i (ProdDef ps) = mapM_ (assertDefinition f i) $ Arr.elems ps

lookupArgs :: [Int] -> [SMTExpr Bool] -> [SMTExpr Bool]
lookupArgs argN vars = map ((!!) vars) argN

data ProgDefs = ProgDefs
                { flowDef :: [Definition]
                , precondition :: Definition
                , invariantDef :: Definition
                }
