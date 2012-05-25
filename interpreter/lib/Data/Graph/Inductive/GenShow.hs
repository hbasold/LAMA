{-# LANGUAGE ScopedTypeVariables #-}

module Data.Graph.Inductive.GenShow where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Tree as GTree

instance forall a b. (Show a, Show b) => Show (Gr a b) where
  show g =
    let n = labNodes g
        e = labEdges g
        g' = mkGraph n e :: GTree.Gr a b
    in show g'
