module Definition where

import Lang.LAMA.Types

import Language.SMTLib2 as SMT

import Data.Array as Arr
import qualified Data.Set as Set
import Data.Set (Set)

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

data Term =
  BoolTerm [Int] (SMTFunction [TypedExpr] Bool)
  | IntTerm [Int] (SMTFunction [TypedExpr] Integer)
  | RealTerm [Int] (SMTFunction [TypedExpr] Rational)
  deriving (Show, Ord, Eq)

type PosetGraphNode = [Term]

data PosetGraph = PosetGraph
                  { vertices :: [PosetGraphNode]
                  , edges    :: [(Int, Int)]
                  }
  deriving (Show, Ord, Eq)

assertPosetGraph :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> PosetGraph -> m [()]
assertPosetGraph i (PosetGraph vertices edges) = do let vcs = map assertPosetGraph' vertices
                                                        vc = foldl (.&&.) (head vcs) $ tail vcs
                                                    liftSMT $ assert (not' vc)
                                                    return []
  where
    assertPosetGraph' (v:vs) = let c = map (\a -> mkRelation (fst i) (a, v) (.==.)) vs in
                                 foldl (.&&.) (head c) $ tail c
                                                   

mkRelation :: [TypedExpr] -> (Term, Term) -> (SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool) -> SMTExpr Bool
mkRelation i (BoolTerm argsf f, BoolTerm argsg g) r =
  (f `app` lookupArgs argsf False (i, i)) `r` (g `app` lookupArgs argsg False (i, i))

constructRs :: Set Term -> Type i -> [(Term, Term)]
constructRs ts (GroundType BoolT) = [(x,y) | x@(BoolTerm _ _) <- Set.toList ts,
                                      y@(BoolTerm _ _) <- Set.toList ts, x /= y]

assertR :: MonadSMT m => [TypedExpr] -> (Term, Term) -> m ()
assertR i (BoolTerm argsf f, BoolTerm argsg g) =
  liftSMT $ assert ((f `app` (lookupArgs argsf False (i, i))) .=>.
    (g `app` (lookupArgs argsg False (i, i))))
