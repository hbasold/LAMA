module Data.Graph.Inductive.DAG (
  DAG, mkDAG
) where

import Data.Graph.Inductive.Graph (Graph(..), Node)
import Data.Graph.Inductive.Query.DFS (scc)
import Data.Foldable (find)
import Control.Arrow (second)

newtype DAG gr a b = DAG { getGraph :: gr a b } deriving (Show, Eq)

-- | Constructs DAG out of the given graph /g/ iff /g/
--    consists only of trivial strongly connected
--    components (i.e. has no cycles).
mkDAG :: Graph gr => gr a b -> Either [Node] (DAG gr a b)
mkDAG g =
  case find (not . isSingleton) $ scc g of
    Nothing -> Right $ DAG g
    Just c -> Left c
    
  where isSingleton [_] = True
        isSingleton _ = False

unsafeMkDAG :: Graph gr => gr a b -> DAG gr a b
unsafeMkDAG g =
  case mkDAG g of
    Left _ -> error "unsafeMkDAG: Given graph is not acyclic."
    Right dag -> dag

instance Graph gr => Graph (DAG gr) where
  empty = DAG $ empty
  isEmpty = isEmpty . getGraph
  match n = (second DAG) . (match n) . getGraph
  mkGraph ns es = unsafeMkDAG $ mkGraph ns es
  labNodes = labNodes . getGraph
  matchAny = (second DAG) . matchAny . getGraph
  noNodes = noNodes . getGraph
  nodeRange = nodeRange . getGraph
  labEdges = labEdges . getGraph
