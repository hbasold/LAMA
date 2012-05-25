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
import Data.Graph.Inductive.GenShow ()
import Control.Monad (void, when, MonadPlus(..))
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class

import Lang.LAMA.Parse
import Lang.LAMA.Dependencies
import Lang.LAMA.Typing.TypedStructure

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> BL.hGetContents stdin >>= void . runMaybeT . run 2 "stdin"
            "-v":v:fs -> mapM_ (runFile $ read v) fs
            fs -> mapM_ (runFile 0) fs

type Verbosity = Int

whenV :: Monad m => Verbosity -> Verbosity -> m () -> m ()
whenV atLeast v = when (v >= atLeast)

putStrV :: Verbosity -> Verbosity -> String -> IO ()
putStrV atLeast v s = whenV atLeast v (putStrLn s)

runFile :: Verbosity -> FilePath -> IO ()
runFile v f = putStrLn f >> BL.readFile f >>= runMaybeT' . run v f
  where
    runMaybeT' :: Functor m => MaybeT m () -> m ()
    runMaybeT' = void . runMaybeT

run :: Verbosity -> FilePath -> BL.ByteString -> MaybeT IO ()
run v f inp = do
  prog <- checkErrors $ parseLAMA inp
  liftIO $ putStrV 2 v $ show prog
  deps <- checkDeps $ mkDeps prog
  liftIO $ whenV 1 v (showDeps f deps)

checkErrors :: Either Error Program -> MaybeT IO Program
checkErrors r = case r of
  Left (ParseError pe) -> printAndFail $ "Parse failed:\n" ++ pe
  Left (StaticError se) -> printAndFail $ "Conversion failed:\n" ++ se
  Left (TypeError te) -> printAndFail $ "Type check failed:\n" ++ te
  Right concTree -> return concTree

checkDeps :: Either String ProgDeps -> MaybeT IO ProgDeps
checkDeps d = case d of
  Left err -> printAndFail $ "Dependency error:\n" ++ err
  Right deps -> return deps

printAndFail :: String -> MaybeT IO a
printAndFail e = liftIO (putStrLn e) >> mzero

showDeps :: FilePath -> ProgDeps -> IO ()
showDeps f deps = do
    let progName = takeBaseName f
    -- dependency graph for program
    void $ runGraphviz (defaultVis $ progDepsFlow deps) Svg (progName ++ ".svg")
    -- dependency graphs for nodes
    forM_ (Map.toList $ progDepsNodes deps) (uncurry $ showNodes progName)
  where
    showNodes path n nDeps = do
      let thisPath = path ++ "_" ++ identString n
      void $ runGraphviz (defaultVis $ nodeDepsFlow nDeps) Svg (thisPath ++ ".svg")
      forM_ (Map.toList $ nodeDepsNodes nDeps) (uncurry $ showNodes thisPath)

defaultVis :: (G.Graph gr, Labellable nl) => gr (nl, a) el -> DotGraph G.Node
defaultVis = graphToDot params
  where params = nonClusteredParams {
          globalAttributes = [GraphAttrs [RankDir FromTop]],
          fmtNode = \(_, (v, _)) -> [Label $ toLabelValue v]
        }

instance Labellable () where
  toLabelValue = const $ textLabelValue $ pack ""

instance Labellable IdentCtx where
  toLabelValue = textLabelValue . pack . prettyVar
    where
      prettyVar (x, u, m) = BS.unpack x ++ "(" ++ show u ++ prettyMode m ++ ")"
      prettyMode GlobalMode = ""
      prettyMode LocationRefMode = " (ref)"
      prettyMode (LocationMode (Id l _)) = " in " ++ BS.unpack l
