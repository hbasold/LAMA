module Definition where

import Lang.LAMA.Types

import Language.SMTLib2 as SMT

import Data.Array as Arr

import LamaSMTTypes
import Internal.Monads

data Definition =
  SingleDef [Int] Bool (SMTFunction [TypedExpr] Bool)
  | ProdDef (Array Int Definition)
  deriving Show

ensureDefinition :: [Int] -> Bool -> TypedFunc -> Definition
ensureDefinition argN succ (BoolFunc s) = SingleDef argN succ s
ensureDefinition argN succ (ProdFunc ps) = ProdDef $ fmap (ensureDefinition argN succ) ps
ensureDefinition argN succ _
  = error $ "ensureDefinition: not a boolean function" -- : " ++ show s

assertDefinition :: MonadSMT m =>
                    (SMTExpr Bool -> SMTExpr Bool)
                    -> ([TypedExpr], [TypedExpr])
                    -> Definition
                    -> m ()
assertDefinition f i (SingleDef argN succ s) = liftSMT $ assert (f $ s `app` (lookupArgs argN succ i))
assertDefinition f i (ProdDef ps) = mapM_ (assertDefinition f i) $ Arr.elems ps

lookupArgs :: [Int] -> Bool -> ([TypedExpr], [TypedExpr])
               -> [TypedExpr]
lookupArgs argN True vars = [(snd vars) !! (head argN)] ++ (map ((!!) (fst vars)) $ tail argN)
lookupArgs argN False vars = map ((!!) (fst vars)) argN

data ProgDefs = ProgDefs
                { flowDef :: [Definition]
                , precondition :: Definition
                , invariantDef :: Definition
                }
