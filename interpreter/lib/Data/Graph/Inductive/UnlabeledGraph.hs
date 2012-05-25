{- Handle unlabeled graphs in a special way:
  all inserting operations add nodes iff it is
  needed.
-}
module Data.Graph.Inductive.UnlabeledGraph where

import Data.Graph.Inductive.Graph
import Data.Tuple (swap)

insNode' :: DynGraph gr => Node -> gr () b -> gr () b
insNode' n g = if not (gelem n g) then insNode (n, ()) g else g

insNodes' :: DynGraph gr => [Node] -> gr () b -> gr () b
insNodes' ns g = foldr insNode' g ns

merge' :: DynGraph gr => Context () b -> gr () b -> gr () b
merge' c@(i, n, (), o) g =
  let (mc, g') = match n g
      g'' = insNodes' (pre' c) $ insNodes' (suc' c) g'
  in case mc of
    Nothing -> c & g''
    Just c' -> (getPre c' ++ i, n, (), getSuc c' ++ o) & g''
  where
    getSuc = map swap . lsuc'
    getPre = map swap . lpre'
