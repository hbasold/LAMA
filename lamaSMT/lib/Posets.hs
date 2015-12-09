module Posets where

import Debug.Trace

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
type ChainNode = ([Integer], [Term])
type Chain     = [ChainNode]

data Poset =
  PosetGraph [GraphNode] [GraphEdge]
  | PosetChains [Chain] (Map Term [Term])
  deriving (Show, Ord, Eq)

type GraphM = State [GraphEdge]

initGraph :: GraphNode -> Maybe Poset
initGraph instSet = Just $ PosetGraph [instSet] []

initChains :: [Term] -> Maybe Poset
initChains instSet = Just $ PosetChains [[([], instSet)]] $ Map.singleton (head instSet) []

getPosetStats :: Poset -> String
getPosetStats (PosetGraph ns es) = (show $ sum (map (\i -> (List.length i) - 1) ns)) ++ " equalities and " ++ (show $ List.length es) ++  " inequalities"
getPosetStats (PosetChains cs m) = (show $ sum $ Set.toList (Set.map (\(_,i) -> (List.length i) - 1) $ getChainNodeSet cs)) ++ " equalities and " ++ (show $ (sum (map (\i -> (List.length i) - 1) cs)) + (List.length $ concat $ Map.elems m)) ++  " inequalities"

getChainNodeSet :: [Chain] -> Set ChainNode
getChainNodeSet cs = foldl (\s t -> Set.insert t s) Set.empty $ concat cs

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

type SortM = State ([Chain], Map Term [Term])

buildNextChain :: [ChainNode] -> Poset
buildNextChain ns = let s = execState (mapM insertChain ns) ([], Map.empty)
                    in {-trace (show $ fst s) $ trace (show $ snd s) $-} PosetChains (fst s) (snd s)

insertChain :: ChainNode -> SortM ()
insertChain node = do chains <- get
                      let res = unzip $ map (tryChain node) $ fst chains
                          newChains = if fst chains == fst res then [[node]] else []
                      put (fst res ++ newChains, Map.unions{-With (++)-}  $ snd res ++ [snd chains, Map.singleton (head $ snd node) []])
  where
    tryChain :: ChainNode -> Chain -> (Chain, Map Term [Term])
    tryChain n@(is,ts) c = let gB = List.findIndices (\a -> and $ map (\(b,c) -> b < c) $ zip (fst a) is) c
                               i  = if List.length gB == 0 then 0 else (maximum gB) + 1
                               lA = List.findIndices (\a -> and $ map (\(b,c) -> b > c) $ zip (fst a) is) c
                               j  = if List.length lA == 0 then 0 else (minimum lA) + 1
                           in if j == 1
                             then ([n] ++ c, Map.empty)
                             else if i == j - 1
                               then let (cl,cr) = List.splitAt i c
                                    in (cl ++ [n] ++ cr, Map.empty)
                               else if i == List.length c
                                 then (c ++ [n], Map.empty)
                                 else let m1 = if i > 0 then Map.singleton (head $ snd (c !! (i - 1))) [head ts] else Map.empty
                                          m2 = if j > 0 then Map.singleton (head ts) [head $ snd (c !! (j - 1))] else Map.empty
                                      in (c, m1 `Map.union` m2)

assertPoset :: MonadSMT m => (SMTExpr Bool -> SMTExpr Bool) -> ([TypedExpr], [TypedExpr]) -> Poset -> m ()
assertPoset f i (PosetChains cs m) = do let eq = concat $ map (assertEquality . snd) $ Set.toList $ getChainNodeSet cs
                                            rep = map (map (head . snd)) cs
                                            cc = concat $ map assertChain rep
                                            c  = foldl (.&&.) (constant True) $ cc ++ eq
                                        liftSMT $ assert $ f c
  where
    assertEquality (_:[]) = [constant True]
    assertEquality (t:ts) = map (\a -> mkIntRelation (fst i) (a, t) (.==.)) ts
    assertChain [] = [constant True]
    assertChain (_:[]) = [constant True]
    assertChain (t:ts) = [mkIntRelation (fst i) (t, head ts) (.<=.)] ++ assertChain (m Map.! t) ++ assertChain ts
    assertChain x = error $ "ha: " ++ show x
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
