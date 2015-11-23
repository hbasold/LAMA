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

assertPosetGraph :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> PosetGraph -> m [()]
assertPosetGraph i (PosetGraph vertices edges) = do mapM assertPosetGraph' vertices
                                                    --mapM (\(a, b) -> assertRelation (fst i) (head (vertices !! a), head (vertices !! b)) (.=>.)) edges
                                                    return []
  where
    assertPosetGraph' (v:vs) = mapM (\a -> assertRelation (fst i) (a, v) (.==.)) vs
    assertPosetGraph' _ = return []
                                                   

assertRelation :: MonadSMT m => [TypedExpr] -> (Term, Term) -> (SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool) -> m ()
assertRelation i (BoolTerm argsf f, BoolTerm argsg g) r =
  liftSMT $ assert ((f `app` (lookupArgs argsf False (i, i))) `r`
    (g `app` (lookupArgs argsg False (i, i))))

constructRs :: Set Term -> Type i -> [(Term, Term)]
constructRs ts (GroundType BoolT) = [(x,y) | x@(BoolTerm _ _) <- Set.toList ts,
                                      y@(BoolTerm _ _) <- Set.toList ts, x /= y]

mkRelation :: ([TypedExpr], [TypedExpr]) -> (Term, Term) -> SMTExpr Bool
mkRelation i (BoolTerm argsf f, BoolTerm argsg g) = (f `app` (lookupArgs argsf False i)) .=>.
                                                       (g `app` (lookupArgs argsg False i))

assertRs :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> [(Term, Term)] -> m ()
assertRs i rs = let c = (map (mkRelation i) rs) in
                  liftSMT $ assert (not' $ foldl (.&&.) (head c) $ tail c)

assertR :: MonadSMT m => [TypedExpr] -> (Term, Term) -> m ()
assertR i (BoolTerm argsf f, BoolTerm argsg g) =
  liftSMT $ assert ((f `app` (lookupArgs argsf False (i, i))) .=>.
    (g `app` (lookupArgs argsg False (i, i))))
