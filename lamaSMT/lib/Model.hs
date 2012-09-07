module Model (Model(..), NodeModel(..), getModel, prettyModel, scadeScenario) where

import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Natural
import Text.PrettyPrint hiding ((<>))
import Data.Array as Arr
import Data.Monoid
import Data.Text (unpack)

import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Applicative (Applicative(..), (<$>))

import Language.SMTLib2 as SMT

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure

import SMTEnum
import LamaSMTTypes
import TransformEnv

type ValueStreamT t = Map Natural t
data ValueStream
  = BoolVStream (ValueStreamT Bool)
  | IntVStream (ValueStreamT Integer)
  | RealVStream (ValueStreamT Rational)
  | EnumVStream (ValueStreamT SMTEnum)
  | ProdVStream (Array Int ValueStream)
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
prettyVars = vcat . map (\(x, s) -> (ptext $ identString x) <+> text "=" <+> prettyStream s) . Map.toList

prettyNodes :: Ident i => Map i (NodeModel i) -> Doc
prettyNodes = vcat . map (\(x, n) -> (ptext $ identString x) <+> prettyNodeModel n) . Map.toList

prettyNodeModel :: Ident i => NodeModel i -> Doc
prettyNodeModel m = braces . nest 2 $
  text "Inputs:" $+$ nest 2 (vcat . map prettyStream $ nodeModelIn m) $+$
  text "Outputs:" $+$ nest 2 (vcat . map prettyStream $ nodeModelOut m) $+$
  prettyModel (nodeModelVars m)

prettyStream :: ValueStream -> Doc
prettyStream (BoolVStream s) = prettyStreamVals s
prettyStream (IntVStream s) = prettyStreamVals s
prettyStream (RealVStream s) = prettyStreamVals s
prettyStream (EnumVStream s) = prettyStreamVals s
prettyStream (ProdVStream s) = parens . hcat . punctuate comma . fmap prettyStream $ Arr.elems s

prettyStreamVals :: Show t => ValueStreamT t -> Doc
prettyStreamVals = cat . punctuate (char ',')
               . map (\(n, v) -> (integer $ toInteger n) <+> text "->" <+> text (show v))
               . Map.toList

getModel :: VarEnv i -> Map Natural StreamPos -> SMT (Model i)
getModel env = runReaderT (getModel' env)

type ModelM = ReaderT (Map Natural StreamPos) SMT

getModel' :: VarEnv i -> ModelM (Model i)
getModel' env =
  Model <$> getVarsModel (vars env) <*> mapM getNodeModel (nodes env)

getNodeModel :: NodeEnv i -> ModelM (NodeModel i)
getNodeModel (NodeEnv i o e) =
  NodeModel <$> mapM getVarModel i <*> mapM getVarModel o <*> getModel' e

getVarsModel :: Map i (TypedStream i) -> ModelM (Map i ValueStream)
getVarsModel = mapM getVarModel

getVarModel :: TypedStream i -> ModelM ValueStream
getVarModel (BoolStream s) = BoolVStream <$> getStreamValue s
getVarModel (IntStream s) = IntVStream <$> getStreamValue s
getVarModel (RealStream s) = RealVStream <$> getStreamValue s
getVarModel (EnumStream s) = EnumVStream <$> getStreamValue s
getVarModel (ProdStream s) = ProdVStream <$> mapM getVarModel s

getStreamValue :: SMTValue t => Stream t -> ModelM (ValueStreamT t)
getStreamValue s = ask >>= liftSMT . mapM (\i -> getValue $ s `app` i)

scadeScenario :: Ident i => Program i -> [String] -> Model i -> Doc
scadeScenario p varPath m =
  let progInputNames = map varIdent . declsInput $ progDecls p
      progInputs = (Map.fromList $ zip progInputNames (repeat ()))
      inputTraces = Map.toList $ (modelVars m) `Map.intersection` progInputs
      path = case varPath of
        [] -> mempty
        _ -> (vcat $ punctuate (text "/") $ map text varPath) <> text ("/")
  in scenario inputTraces path 0
  where
    scenario [] _ _ = mempty
    scenario inp@((_,s0):_) path i
      | hasValAt s0 i =
        let setOp = text "SSM::set"
            varSetter = map (\(x, v) -> setOp <+> (path <> (ptext $ identString x)) <+> (prettyVal i v)) inp
            rest = scenario inp path (i+1)
        in vcat varSetter $+$ text "SSM::cycle 1" $+$ rest
      | otherwise = mempty

    hasValAt :: ValueStream -> Natural -> Bool
    hasValAt (BoolVStream s) i = Map.member i s
    hasValAt (IntVStream s) i = Map.member i s
    hasValAt (RealVStream s) i = Map.member i s
    hasValAt (EnumVStream s) i = Map.member i s
    hasValAt (ProdVStream s) i = hasValAt (s ! 0) i

    prettyVal :: Natural -> ValueStream  -> Doc
    prettyVal i (BoolVStream s) = bool $ s Map.! i
    prettyVal i (IntVStream s) = integer $ s Map.! i
    prettyVal i (RealVStream s) = rational $ s Map.! i
    prettyVal i (EnumVStream s) = text $ unpack $ getEnumCons $ s Map.! i
    prettyVal i (ProdVStream s) = parens . hsep . punctuate (text ",") . map (prettyVal i) $ elems s

    bool True = text "true"
    bool False = text "false"