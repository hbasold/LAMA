module Model (Model(..), NodeModel(..), getModel, prettyModel) where

import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Sequence
import Text.PrettyPrint

import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Applicative (Applicative(..), (<$>))

import Language.SMTLib2 as SMT

import Lang.LAMA.Identifier

import Transform

type ValueStreamT t = Seq t
data ValueStream
  = BoolVStream (ValueStreamT Bool)
  | IntVStream (ValueStreamT Integer)
  | RealVStream (ValueStreamT Rational)
  deriving Show


data Model i = Model
               { modelVars :: Map i ValueStream
               , modelNodes :: Map i (NodeModel i)
               } deriving Show

data NodeModel i = NodeModel
                   { nodeModelIn :: [ValueStream]
                   , nodeModelOut :: [ValueStream]
                   , nodeModelVars :: Model i
                   } deriving Show

prettyModel :: Ident i => Model i -> Doc
prettyModel m = prettyVars (modelVars m) $+$ prettyNodes (modelNodes m)

prettyVars :: Ident i => Map i ValueStream -> Doc
prettyVars = vcat . map (\(x, s) -> (ptext $ identPretty x) <+> text "=" <+> prettyStream s) . Map.toList

prettyNodes :: Ident i => Map i (NodeModel i) -> Doc
prettyNodes = vcat . map (\(x, n) -> (ptext $ identPretty x) <+> prettyNodeModel n) . Map.toList

prettyNodeModel :: Ident i => NodeModel i -> Doc
prettyNodeModel m = braces . nest 2 $
  text "Inputs:" $+$ nest 2 (vcat . map prettyStream $ nodeModelIn m) $+$
  text "Outputs:" $+$ nest 2 (vcat . map prettyStream $ nodeModelOut m) $+$
  prettyModel (nodeModelVars m)

prettyStream :: ValueStream -> Doc
prettyStream = text . show

getModel :: VarEnv i -> Seq StreamPos -> SMT (Model i)
getModel env = runReaderT (getModel' env)

type ModelM = ReaderT (Seq StreamPos) SMT

getModel' :: VarEnv i -> ModelM (Model i)
getModel' env =
  Model <$> getVarsModel (vars env) <*> mapM getNodeModel (nodes env)

getNodeModel :: NodeEnv i -> ModelM (NodeModel i)
getNodeModel (NodeEnv i o e) =
  NodeModel <$> mapM getVarModel o <*> mapM getVarModel i <*> getModel' e

getVarsModel :: Map i (TypedStream i) -> ModelM (Map i ValueStream)
getVarsModel = mapM getVarModel

getVarModel :: TypedStream i -> ModelM ValueStream
getVarModel (BoolStream s) = BoolVStream <$> getStreamValue s
getVarModel (IntStream s) = IntVStream <$> getStreamValue s
getVarModel (RealStream s) = RealVStream <$> getStreamValue s

getStreamValue :: SMTValue t => Stream t -> ModelM (ValueStreamT t)
getStreamValue s = ask >>= liftSMT . mapM (\i -> getValue $ s `app` i)
