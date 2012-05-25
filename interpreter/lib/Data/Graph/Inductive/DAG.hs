{-# LANGUAGE TupleSections #-}

module Data.Graph.Inductive.DAG (
  DAG(..), mkDAG, dagMapNLab, dagMapNLabM
) where

import Data.Graph.Inductive.Graph (Graph(..), DynGraph, Node, nmap)
import Data.Graph.Inductive.Query.DFS (scc)
import Data.Graph.Inductive.MonadSupport (gmapM)
import Data.Foldable (find)
import Control.Arrow (second)
import Control.Monad (liftM)

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

-- | Maps the node label of a DAG
dagMapNLab :: DynGraph gr => (a -> c) -> DAG gr a b -> DAG gr c b
dagMapNLab f = unsafeMkDAG . nmap f . getGraph

dagMapNLabM :: (DynGraph gr, Monad m) => (a -> m c) -> DAG gr a b -> m (DAG gr c b)
dagMapNLabM f = liftM unsafeMkDAG . gmapM f' . getGraph
  where f' (i, n, l, o) = f l >>= \l' -> return (i, n, l', o)
