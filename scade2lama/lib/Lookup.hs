module Lookup where

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.Error (MonadError(..))

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v