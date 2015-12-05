module Definition where

import Lang.LAMA.Types

import Language.SMTLib2 as SMT

import Data.Array as Arr
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.List as List
import Data.List ((\\))
import Control.Monad.State
import Control.Arrow ((***))

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
type PosetGraphEdge = (Int, Int)

data PosetGraph = PosetGraph
                  { vertices :: [PosetGraphNode]
                  , edges    :: [PosetGraphEdge]
                  }
  deriving (Show, Ord, Eq)

type GraphM = State [PosetGraphEdge]

buildNextGraph :: ([PosetGraphNode], [PosetGraphNode]) -> [PosetGraphEdge] -> PosetGraph
buildNextGraph (v0, v1) e = let leaves = getLeaves e
                                i = length v0
                                firstEdges = [(a, a+i) | a <- [0..i-1]] ++ e
                                otherEdges = evalState (traverseGraph i leaves) e
                                in removeUnreachableNodes $ removeEmptyNodes $ PosetGraph (v0 ++ v1) (firstEdges ++ otherEdges)
  where
    getLeaves e = [snd $ head e]

removeEmptyNodes :: PosetGraph -> PosetGraph
removeEmptyNodes (PosetGraph vs es) = PosetGraph (map snd vs') $ newEdges es
  where
    vs' = filter (\(_,v) -> not $ null v) $ zip [0..] vs
    newEdges ((a,b):eds) = case List.elemIndex a (map fst vs') of
                           Nothing -> newEdges eds
                           Just i -> case List.elemIndex b (map fst vs') of
                                       Nothing -> newEdges eds
                                       Just j -> [(i,j)] ++ newEdges eds
    newEdges [] = []

removeUnreachableNodes :: PosetGraph -> PosetGraph
removeUnreachableNodes (PosetGraph vs es) = PosetGraph (map snd vs') $ newEdges es
  where
    vs' = filter (\a -> (elem (fst a) nodesWithEdges) || (length (snd a) > 1)) $ zip [0..] vs
    nodesWithEdges = (fst $ unzip es) ++ (snd $ unzip es)
    newEdges ((a,b):eds) = case List.elemIndex a (map fst vs') of
                           Nothing -> newEdges eds
                           Just i -> case List.elemIndex b (map fst vs') of
                                       Nothing -> newEdges eds
                                       Just j -> [(i,j)] ++ newEdges eds
    newEdges [] = []

traverseGraph :: Int -> [Int] -> GraphM [PosetGraphEdge]
traverseGraph i (l:ls) = do edgesLeft <- get
                            let p = getPredecessors l edgesLeft
                            put $ edgesLeft \\ p
                            top <- traverseGraph i (map fst p)
                            rest <- traverseGraph i ls
                            return $ map ((+i) *** (+i)) p ++ top ++ rest
  where
    getPredecessors l e = [(x,y) | (x,y) <- e, y == l]
                            
traverseGraph _ [] = return []

assertPosetGraph :: MonadSMT m => (SMTExpr Bool -> SMTExpr Bool) -> ([TypedExpr], [TypedExpr]) -> PosetGraph -> m ()
assertPosetGraph f i (PosetGraph vertices edges) = do let vcs = map assertPosetGraphVs vertices
                                                          vc = foldl (.&&.) (constant True) $ vcs ++ assertPosetGraphEs edges
                                                      liftSMT $ assert (f vc)
                                                      --return
  where
    assertPosetGraphVs (v:[]) = constant True
    assertPosetGraphVs (v:vs) = let c = map (\a -> mkRelation (fst i) (a, v) (.==.)) vs in
                                  foldl (.&&.) (head c) $ tail c
    assertPosetGraphVs [] = constant True
    assertPosetGraphEs es = map (\(a,b) -> mkRelation (fst i) (head (vertices !! a), head (vertices !! b)) (.=>.)) es
                                                   

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
