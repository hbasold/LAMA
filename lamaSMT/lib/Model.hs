module Model (Model(..), NodeModel(..), getModel, prettyModel, scadeScenario) where

import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Natural
import Text.PrettyPrint hiding ((<>))
import Data.Array as Arr
import Data.Monoid
import Data.Maybe (fromJust)
import qualified Data.List as List

import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Applicative (Applicative(..), (<$>))

import Language.SMTLib2 as SMT
-- import Language.SMTLib2.Internals.Translation as SMT (getValue')

import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure

import SMTEnum
import LamaSMTTypes
import TransformEnv
import Internal.Monads

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
prettyStream (IntVStream s)  = prettyStreamVals s
prettyStream (RealVStream s) = prettyStreamVals s
prettyStream (EnumVStream s) = prettyStreamVals s
prettyStream (ProdVStream s)
             = parens . hcat . punctuate comma . fmap prettyStream $ Arr.elems s

prettyStreamVals :: Show t => ValueStreamT t -> Doc
prettyStreamVals
        = cat . punctuate (char ',')
          . map (\(n, v) ->
                (integer $ toInteger n) <+> text "->" <+> text (show v))
          . Map.toList

getModel :: VarEnv i -> Map Natural [TypedExpr] -> SMT (Model i)
getModel env m = runReaderT (getModel' env) m

type ModelM = ReaderT (Map Natural [TypedExpr]) SMT

getModel' :: VarEnv i -> ModelM (Model i)
getModel' env =
  Model <$> getVarsModel (vars env) <*> mapM getNodeModel (nodes env)

getNodeModel :: NodeEnv i -> ModelM (NodeModel i)
getNodeModel (NodeEnv i o e) =
  NodeModel <$> mapM getVarModel i <*> mapM (getVarModel . snd) o <*> getModel' e

getVarsModel :: Map i (TypedExpr) -> ModelM (Map i ValueStream)
getVarsModel = mapM getVarModel

getVarModel :: TypedExpr -> ModelM ValueStream
getVarModel (BoolExpr s) = do varMap   <- ask
                              let i = fromJust $ List.elemIndex (BoolExpr s) (varMap Map.! 0)
                              stream <- liftSMT $ mapM (\l -> getValue $ unBool $ l !! i) varMap
                              return $ BoolVStream stream
getVarModel (IntExpr s)  = do varMap   <- ask
                              let i = fromJust $ List.elemIndex (IntExpr s) (varMap Map.! 0)
                              stream <- liftSMT $ mapM (\l -> getValue $ unInt $ l !! i) varMap
                              return $ IntVStream stream
getVarModel (RealExpr s) = do varMap   <- ask
                              let i = fromJust $ List.elemIndex (RealExpr s) (varMap Map.! 0)
                              stream <- liftSMT $ mapM (\l -> getValue $ unReal $ l !! i) varMap
                              return $ RealVStream stream
getVarModel (EnumExpr s) = do varMap   <- ask
                              let i = fromJust $ List.elemIndex (EnumExpr s) (varMap Map.! 0)
                              stream <- liftSMT $ mapM (\l -> getValue $ unEnum $ l !! i) varMap
                              return $ EnumVStream stream
getVarModel (ProdExpr s) = do varMap <- ask
                              let i = fromJust $ List.elemIndex (ProdExpr s) (varMap Map.! 0)
                                  newArg = Map.map (\l -> Arr.elems $ unProd $ l !! i) varMap
                              stream <- liftSMT $ mapM (\a -> runReaderT (getVarModel a) newArg) s
                              return $ ProdVStream stream

scadeScenario :: Ident i =>
              Program i -> [String] -> Model i -> Doc
scadeScenario p varPath m =
  let progInputNames = map varIdent . declsInput $ progDecls p
      progInputs = (Map.fromList $ zip progInputNames (repeat ()))
      lastIndex = case fmap fst . Map.minView . modelVars $ m of
        Nothing -> 0
        Just s -> getLastIndex s
      inputTraces = Map.toList $ (modelVars m) `Map.intersection` progInputs
      path = case varPath of
        [] -> mempty
        _ -> (hcat $ punctuate (text "::") $ map text varPath) <> text ("/")
  in scenario inputTraces path lastIndex 0
  where
    -- | Retrieves the last defined index of a given stream
    getLastIndex :: ValueStream -> Natural
    getLastIndex (BoolVStream s) = highestIndex s
    getLastIndex (IntVStream s)  = highestIndex s
    getLastIndex (RealVStream s) = highestIndex s
    getLastIndex (EnumVStream s) = highestIndex s
     -- abuses that products are non-empty
    getLastIndex (ProdVStream a) = getLastIndex (a ! 0)

    -- | Usese that streams are given by maps and so we can use findMax to
    -- get the highest defined index.
    highestIndex :: ValueStreamT t -> Natural
    highestIndex s
      | Map.null s = 0
      | otherwise  = fst $ Map.findMax s

    -- | Creates a Doc for all indices i..n from inp, setting the variables
    -- under path.
    scenario inp path n i
      | i <= n =
        let setOp = text "SSM::set"
            varSetter = map (\(x, v) ->
                              setOp
                              <+> (path <> (ptext $ identString x))
                              <+> (prettyVal i v)) inp
            rest = scenario inp path n (i+1)
        in vcat varSetter $+$ text "SSM::cycle 1" $+$ rest
      | otherwise = mempty

    prettyVal :: Natural -> ValueStream  -> Doc
    prettyVal i (BoolVStream s) = bool $ s Map.! i
    prettyVal i (IntVStream s) = integer $ s Map.! i
    prettyVal i (RealVStream s) = rational $ s Map.! i
    prettyVal i (EnumVStream s) = text $ getEnumCons $ s Map.! i
    prettyVal i (ProdVStream s) = parens
                                  . hsep
                                  . punctuate (text ",")
                                  . map (prettyVal i) $ elems s

    bool True = text "true"
    bool False = text "false"
