module Data.Graph.Inductive.NodeMapSupport where

import Data.Graph.Inductive.NodeMap
import Data.Graph.Inductive.Graph
import Control.Monad.State.Lazy

-- | Insert a node into a graph. If it already exists updates the label with f new_label old_label.
insNodeWith :: DynGraph gr => (a -> a -> a) -> LNode a -> gr a b -> gr a b
insNodeWith f ln@(n, l1) g = case match n g of
  (Just (p, _, l2, s), g') -> let l' = f l1 l2 in (p, n, l', s) & g'
  _ -> insNode ln g

-- | Inserts a node only if does not already exist
insNode' :: DynGraph gr => LNode a -> gr a b -> gr a b
insNode' = insNodeWith (const id)

insMapNode' :: (Ord a, DynGraph gr) => NodeMap a -> a -> gr a b -> (gr a b, NodeMap a, LNode a)
insMapNode' m a g =
    let (n, m') = mkNode m a
    in (insNode' n g, m', n)

insMapNodes' :: (Ord a, DynGraph gr) => NodeMap a -> [a] -> gr a b -> (gr a b, NodeMap a, [LNode a])
insMapNodes' m as g =
    let (ns, m') = mkNodes m as
    in (foldl (flip insNode') g ns, m', ns)

insMapNodeM' :: (Ord a, DynGraph gr) => a -> NodeMapM a b gr (LNode a)
insMapNodeM' n = do
  (m, g) <- get
  let (g', m', r) = insMapNode' m n g
  put (m', g')
  return r

insMapNodesM' :: (Ord a, DynGraph gr) => [a] -> NodeMapM a b gr [LNode a]
insMapNodesM' n = do
  (m, g) <- get
  let (g', m', r) = insMapNodes' m n g
  put (m', g')
  return r
