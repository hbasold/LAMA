module Model where

import qualified Data.Map as Map
import Data.Map (Map)

import Language.SMTLib2 as SMT

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure

import Transform

data Model i = Model
               { values :: Map i (Constant i)
               , nodeVals :: Map i (Model i)
               } deriving Show

getModel :: Ident i => VarEnv i -> SMT (Model i)
getModel env = return $ Model Map.empty Map.empty
