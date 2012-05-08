{-# LANGUAGE TypeSynonymInstances, ScopedTypeVariables #-}

module Main (main) where

import System.IO (stdin)
import System.Environment (getArgs)
import System.FilePath (takeBaseName)
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.ByteString.Char8 as BS
import Data.GraphViz as GV
import Data.GraphViz.Attributes.Complete as GV
import qualified Data.Graph.Inductive.Graph as G
import Data.Text.Lazy (pack)
import Data.Foldable (forM_)
import Lang.LAMA.Identifier
import Data.Map as Map
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Tree as GTree
import Control.Monad (void)

import Lang.LAMA.Parse
import Lang.LAMA.Dependencies

type Verbosity = Int

instance forall a b. (Show a, Show b) => Show (Gr a b) where
  show g =
    let n = G.labNodes g
        e = G.labEdges g
        g' = G.mkGraph n e :: GTree.Gr a b
    in show g'

instance Labellable () where
  toLabelValue = const $ textLabelValue $ pack ""

instance Labellable Var where
  toLabelValue = textLabelValue . pack . prettyVar
    where
      prettyVar ((Id x _), u, m) = BS.unpack x ++ "(" ++ show u ++ prettyMode m ++ ")"
      prettyMode GlobalMode = ""
      prettyMode (LocationMode (Id l _)) = " in " ++ BS.unpack l

putStrV :: Verbosity -> Verbosity -> String -> IO ()
putStrV whenV v s = if v >= whenV then putStrLn s else return ()

runFile :: Verbosity -> FilePath -> IO ()
runFile v f = putStrLn f >> BL.readFile f >>= run v f

run :: Verbosity -> FilePath -> BL.ByteString -> IO ()
run v f inp = case parseLAMA inp of
  Left (ParseError pe) -> do
    putStrLn "Parse failed..."
    putStrLn pe
  Left (StaticError se) -> do
    putStrLn $ "Conversion failed:"
    putStrLn se
  Right concTree -> case mkDeps concTree of
    Left err -> putStrLn "Dependency error: " >> putStrLn err
    Right deps -> do
      putStrV 2 v $ show concTree
      let progName = takeBaseName f
      -- dependency graph for program
      void $ runGraphviz (defaultVis $ depsGraph $ progFlowDeps deps) Svg (progName ++ ".svg")
      -- dependency graphs for nodes
      let gs = Map.toList $ fmap (defaultVis . depsGraph) (nodeDeps deps)
      forM_ gs (\(n, g) -> runGraphviz g Svg (progName ++ "_" ++ n ++ ".svg"))
      -- putStrV 1 v $ show $ fmap (graphviz' . graph) deps
      --forM_ deps (preview . graph)

defaultVis :: (G.Graph gr, Labellable nl) => gr nl el -> DotGraph G.Node
defaultVis = graphToDot params
  where params = nonClusteredParams {
          globalAttributes = [GraphAttrs [RankDir FromTop]],
          fmtNode = \(_, l) -> [Label $ toLabelValue l]
        }

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> BL.hGetContents stdin >>= run 2 "stdin"
            "-v":v:fs -> mapM_ (runFile $ read v) fs
            fs -> mapM_ (runFile 0) fs
