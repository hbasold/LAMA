module Posets where

import Lang.LAMA.Types

import Language.SMTLib2 as SMT

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List ((\\))
import Control.Monad.State
import Control.Arrow ((***))

import LamaSMTTypes
import Internal.Monads
import Definition

data Term = BoolTerm Int | IntTerm Int
  deriving (Show, Ord, Eq)

type GraphNode = [Term]
type GraphEdge = (Int, Int)
type Chain     = [Term]

data Poset =
  PosetGraph [GraphNode] [GraphEdge]
  | PosetChains [Chain] (Map Term [Term])
  deriving (Show, Ord, Eq)

type GraphM = State [GraphEdge]

initGraph :: [Term] -> Maybe Poset
initGraph instSet = Just $ PosetGraph [instSet] []

buildNextGraph :: ([GraphNode], [GraphNode]) -> [GraphEdge] -> Poset
buildNextGraph (v0, v1) e = let leaves = getLeaves e
                                i = length v0
                                firstEdges = [(a, a+i) | a <- [0..i-1]] ++ e
                                otherEdges = evalState (traverseGraph i leaves) e
                                in removeUnreachableNodes $ removeEmptyNodes $ PosetGraph (v0 ++ v1) (firstEdges ++ otherEdges)
  where
    getLeaves ed = [snd $ head ed]

removeEmptyNodes :: Poset -> Poset
removeEmptyNodes (PosetGraph vs es) = PosetGraph (map snd vs') $ newEdges es
  where
    vs' = filter (\(_,v) -> not $ null v) $ zip [0..] vs
    newEdges ((a,b):eds) = case List.elemIndex a (map fst vs') of
                           Nothing -> newEdges eds
                           Just i -> case List.elemIndex b (map fst vs') of
                                       Nothing -> newEdges eds
                                       Just j -> [(i,j)] ++ newEdges eds
    newEdges [] = []
removeEmptyNodes _ = error "Poset is not a graph"

removeUnreachableNodes :: Poset -> Poset
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
removeUnreachableNodes _ = error "Poset is not a graph"

traverseGraph :: Int -> [Int] -> GraphM [GraphEdge]
traverseGraph i (l:ls) = do edgesLeft <- get
                            let p = getPredecessors l edgesLeft
                            put $ edgesLeft \\ p
                            top <- traverseGraph i (map fst p)
                            rest <- traverseGraph i ls
                            return $ map ((+i) *** (+i)) p ++ top ++ rest
  where
    getPredecessors a e = [(x,y) | (x,y) <- e, y == a]

traverseGraph _ [] = return []

assertPoset :: MonadSMT m => (SMTExpr Bool -> SMTExpr Bool) -> ([TypedExpr], [TypedExpr]) -> Poset -> m ()
assertPoset f i (PosetGraph vs es) = do let vcs = map assertPosetGraphVs vs
                                            vc = foldl (.&&.) (constant True) $ vcs ++ assertPosetGraphEs es
                                        liftSMT $ assert (f vc)
  where
    assertPosetGraphVs (_:[]) = constant True
    assertPosetGraphVs (vc:vcs) = let c = map (\a -> mkBoolRelation (fst i) (a, vc) (.==.)) vcs in
                                  foldl (.&&.) (head c) $ tail c
    assertPosetGraphVs [] = constant True
    assertPosetGraphEs ecs = map (\(a,b) -> mkBoolRelation (fst i) (head (vs !! a), head (vs !! b)) (.=>.)) ecs


mkBoolRelation :: [TypedExpr] -> (Term, Term) -> (SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool) -> SMTExpr Bool
mkBoolRelation i (BoolTerm f, BoolTerm g) r =
  (unBool $ head $ lookupArgs [f] False (i,i)) `r` (unBool $ head $ lookupArgs [g] False (i,i))

mkIntRelation :: [TypedExpr] -> (Term, Term) -> (SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) -> SMTExpr Bool
mkIntRelation i (IntTerm f, IntTerm g) r =
  (unInt $ head $ lookupArgs [f] False (i,i)) `r` (unInt $ head $ lookupArgs [g] False (i,i))
