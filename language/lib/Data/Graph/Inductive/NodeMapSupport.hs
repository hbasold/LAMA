{-# LANGUAGE FlexibleContexts #-}

module Data.Graph.Inductive.NodeMapSupport (
  Gr.NodeMap,
  NodeMapM, runNodeMapM, insNodeWith, insNode', insMapNode', insMapNodes',
  insMapNodeM', insMapNodesM',
  insEdgeWith, insEdge', insMapEdge', insMapEdgeM'
) where

import Data.Graph.Inductive.NodeMap as Gr hiding (NodeMapM)
import Data.Graph.Inductive.Graph
import Control.Monad.State.Strict
import Data.Foldable (find)

-- | We redefine 'Data.Graph.Inductive.NodeMap.NodeMapM' here, because
--    the original type alias does not allow leaving the monadic return type
--    unbound.
type NodeMapM a b gr = State (NodeMap a, gr a b)

-- | Run a construction; return the value of the computation, the modified
-- 'NodeMap', and the modified 'Graph'.
runNodeMapM :: (DynGraph g, Ord a) => g a b -> NodeMapM a b g r -> (r, (NodeMap a, g a b))
runNodeMapM g m = runState m (fromGraph g, g)

-- | Insert a node into a graph. If it already exists updates the label with f new_label old_label.
insNodeWith :: DynGraph gr => (a -> a -> a) -> LNode a -> gr a b -> gr a b
insNodeWith f ln@(n, l1) g = case match n g of
  (Just (p, _, l2, s), g') -> let l' = f l1 l2 in (p, n, l', s) & g'
  _ -> insNode ln g

-- | Inserts a node only if does not already exist
insNode' :: DynGraph gr => LNode a -> gr a b -> gr a b
insNode' ln@(n, _) g = if not (gelem n g) then insNode ln g else g

insMapNode' :: (Ord a, DynGraph gr) => NodeMap a -> a -> gr a b -> (gr a b, NodeMap a, LNode a)
insMapNode' m a g =
    let (n, m') = mkNode m a
    in (insNode' n $! g, m', n)

insMapNodes' :: (Ord a, DynGraph gr) => NodeMap a -> [a] -> gr a b -> (gr a b, NodeMap a, [LNode a])
insMapNodes' m as g =
    let (ns, m') = mkNodes m as
    in (foldl (flip insNode') g ns, m', ns)

insMapNodeM' :: (Ord a, DynGraph gr, MonadState (NodeMap a, gr a b) m) => a -> m (LNode a)
insMapNodeM' n = do
  (m, g) <- get
  let (g', m', r) = insMapNode' m n g
  put (m', g')
  return r

insMapNodesM' :: (Ord a, DynGraph gr, MonadState (NodeMap a, gr a b) m) => [a] -> m [LNode a]
insMapNodesM' n = do
  (m, g) <- get
  let (g', m', r) = insMapNodes' m n g
  put (m', g')
  return r

-- | Inserts an edge into a graph combining existing edge labels.
insEdgeWith :: DynGraph gr => (b -> b -> b) -> LEdge b -> gr a b -> gr a b
insEdgeWith f le@(h, t, l1) g =
  let s = lsuc g h
      t' = find ((t ==) . fst) s
  in case t' of
    Just (_, l2) -> insEdge (h, t, f l1 l2) $ delEdge (h, t) g
    Nothing -> insEdge le g

-- | Inserts an edge only if it does not already exist
insEdge' :: DynGraph gr => LEdge b -> gr a b -> gr a b
insEdge' le@(h, t, _) g =
  let s = suc g h
      exists = any (t ==) s
  in if exists then g else insEdge le g

insMapEdge' :: (Ord a, DynGraph gr) => NodeMap a -> (a, a, b) -> gr a b -> gr a b
insMapEdge' m e g =
  let (Just e') = mkEdge m e
  in insEdge' e' $! g

insMapEdgeM' :: (Ord a, DynGraph gr, MonadState (NodeMap a, gr a b) m) => (a, a, b) -> m ()
insMapEdgeM' e = modify $ \(m, g) -> (m, insMapEdge' m e g)
