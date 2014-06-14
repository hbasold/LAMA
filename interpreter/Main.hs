{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

module Main (main) where

import System.IO (stdin)
import System.Environment (getArgs)
import System.FilePath (takeBaseName)
import System.Console.GetOpt
import System.Exit (exitSuccess)
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.ByteString.Char8 as BS
import Data.GraphViz as GV
import Data.GraphViz.Attributes.Complete as GV
import qualified Data.Graph.Inductive.Graph as G
import Data.Text.Lazy (pack)
import Data.Foldable (forM_, foldlM, foldl)
import Lang.LAMA.Identifier
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (void, when, MonadPlus(..))
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import Text.PrettyPrint (render)
import qualified Data.Text.Lazy.IO as Text
import Prelude hiding (foldl)

import Lang.LAMA.Parse
import Lang.LAMA.Dependencies
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Interpret

type Verbosity = Int
data RunMode = Interactive Int

data Options = Options
  { optInput :: FilePath
  , optVerbose :: Verbosity
  , optMode :: RunMode
  , optDebug :: Bool
  , optDumpDeps :: Bool
  , optDumpDepsDot :: Bool
  , optShowHelp :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optVerbose            = 0
  , optMode               = Interactive 25
  , optDebug              = False
  , optDumpDeps           = False
  , optDumpDepsDot        = False
  , optShowHelp           = False
  }

resolveDebug :: Maybe String -> Options -> Options
resolveDebug Nothing opts = opts {optDebug = True}
resolveDebug (Just "dump-deps") opts = opts {optDumpDeps = True}
resolveDebug (Just "dump-deps-dot") opts = opts {optDumpDepsDot = True}
resolveDebug _ opts = opts

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['f'] ["file"]
      (ReqArg (\f opts -> opts {optInput = f}) "FILE")
      "input FILE or stdin"
    , Option ['v'] ["verbosity"]
      (ReqArg (\v opts -> opts {optVerbose = read v}) "VERBOSITY")
      "How much output?"
    , Option ['i'] ["interactive"]
      (ReqArg (\l opts -> opts {optMode = Interactive $ read l}) "LENGTH")
      "Run interactively"
    , Option ['d'] ["debug"]
      (OptArg (\o -> resolveDebug o) "WHAT")
      "Debug something; for more specific debugging use one of: [dump-deps, dump-deps-dot]"
    , Option ['h'] ["help"]
      (NoArg  (\opts -> opts {optShowHelp = True}))
      "Show this help"
    ]

interpreterOpts :: [String] -> IO Options
interpreterOpts argv =
  case getOpt (ReturnInOrder (\file opts -> opts {optInput = file})) options argv of
    (o,[],[]) ->
      let opts = foldl (flip id) defaultOptions o
      in return opts
    (_, (_:_), []) -> ioError $ userError "Unused free option -- should not happen"
    (_,_,errs) -> ioError (userError (concat errs ++ usage))

usage :: String
usage = usageInfo header options
  where header = "Usage: lamai [OPTION...] FILE"

main :: IO ()
main = do argv <- getArgs
          opts <- interpreterOpts argv
          when (optShowHelp opts) $ do
            putStr usage
            exitSuccess
          case (optInput opts) of
            "-" -> BL.hGetContents stdin >>= void . runMaybeT . run opts "stdin"
            f -> runFile opts f

whenV :: Monad m => Verbosity -> Verbosity -> m () -> m ()
whenV atLeast v = when (v >= atLeast)

putStrV :: Verbosity -> Verbosity -> String -> IO ()
putStrV atLeast v s = whenV atLeast v (putStrLn s)

runFile :: Options -> FilePath -> IO ()
runFile opts f = putStrLn f >> BL.readFile f >>= runMaybeT' . run opts f
  where
    runMaybeT' :: Functor m => MaybeT m () -> m ()
    runMaybeT' = void . runMaybeT

run :: Options -> FilePath -> BL.ByteString -> MaybeT IO ()
run opts f source = do
  prog <- checkErrors $ parseLAMA source
  liftIO $ putStrV 2 (optVerbose opts) $ show prog
  deps <- checkDeps $ mkDeps prog
  liftIO $ when (optDumpDeps opts) (depsSvg f deps)
  liftIO $ when (optDumpDepsDot opts) (depsDot f deps)
  let inp = map (dropPos . varIdent) . declsInput $ progDecls prog
  case optMode opts of
    Interactive l -> void $ go prog deps inp emptyState l
  where
    go :: Program PosIdent -> ProgDeps PosIdent -> [SimpIdent] -> State -> Int -> MaybeT IO ()
    go prog deps inp s i
      | i <= 0 = return ()
      | otherwise = do
          userInp <- askValues inp
          s' <- checkInterpret $ eval (updateState s userInp) prog deps
          liftIO $ putStrLn $ render $ prettyState s'
          void $ go prog deps inp s' (i-1)

checkErrors :: Either Error a -> MaybeT IO a
checkErrors r = case r of
  Left (ParseError pe) -> printAndFail $ "Parse failed:\n" ++ pe
  Left (StaticError se) -> printAndFail $ "Conversion failed:\n" ++ se
  Left (TypeError te) -> printAndFail $ "Type check failed:\n" ++ te
  Right concTree -> return concTree

checkDeps :: Either String (ProgDeps i) -> MaybeT IO (ProgDeps i)
checkDeps d = case d of
  Left err -> printAndFail $ "Dependency error:\n" ++ err
  Right deps -> return deps

checkInterpret :: Either String State -> MaybeT IO State
checkInterpret e = case e of
  Left err -> printAndFail $ "Interpretation error:\n" ++ err
  Right env -> return env

printAndFail :: String -> MaybeT IO a
printAndFail e = liftIO (putStrLn e) >> mzero

depsSvg :: Ident i => FilePath -> ProgDeps i -> IO ()
depsSvg f deps = do
    let progName = takeBaseName f
    -- dependency graph for program
    void $ runGraphviz (defaultVis $ progDepsFlow deps) Svg (progName ++ ".svg")
    -- dependency graphs for nodes
    forM_ (Map.toList $ progDepsNodes deps) (uncurry $ nodesSvg progName)
  where
    nodesSvg path n nDeps = do
      let thisPath = path ++ "_" ++ identString n
      void $ runGraphviz (defaultVis $ nodeDepsFlow nDeps) Svg (thisPath ++ ".svg")
      forM_ (Map.toList $ nodeDepsNodes nDeps) (uncurry $ nodesSvg thisPath)

depsDot :: Ident i => FilePath -> ProgDeps i -> IO ()
depsDot f deps = do
    let progName = takeBaseName f
    Text.writeFile (progName ++ ".dot") $ printDotGraph (defaultVis $ progDepsFlow deps)
    -- dependency graphs for nodes
    forM_ (Map.toList $ progDepsNodes deps) (uncurry $ nodesDot progName)
  where
    nodesDot path n nDeps = do
      let thisPath = path ++ "_" ++ identString n
      Text.writeFile (thisPath ++ ".dot") $ printDotGraph (defaultVis $ nodeDepsFlow nDeps)
      forM_ (Map.toList $ nodeDepsNodes nDeps) (uncurry $ nodesDot thisPath)

defaultVis :: (G.Graph gr, Labellable nl) => gr (nl, a) el -> DotGraph G.Node
defaultVis = graphToDot params
  where params = nonClusteredParams {
          globalAttributes = [GraphAttrs [RankDir FromTop]],
          fmtNode = \(_, (v, _)) -> [Label $ toLabelValue v]
        }

instance Labellable () where
  toLabelValue = const $ textLabelValue $ pack ""

instance Ident i => Labellable (IdentCtx i) where
  toLabelValue = textLabelValue . pack . prettyVar
    where
      prettyVar (x, u, m) = BS.unpack x ++ "(" ++ show u ++ prettyMode m ++ ")"
      prettyMode GlobalMode = ""
      prettyMode (LocationRefMode _) = " (ref)"
      prettyMode (LocationMode _ x) = " in " ++ identString x

askValues :: [SimpIdent] -> MaybeT IO (Map SimpIdent (ConstExpr PosIdent))
askValues = foldlM (\vs x -> do
    liftIO $ putStr "Please input value for " >> (BS.putStr $ identBS x) >> BS.putStr (BS.pack ": ")
    e <- liftIO $ fmap (BL.pack . BS.unpack) BS.getLine
    v <- checkErrors $ parseLAMAConstExpr e
    return $ Map.insert x v vs)
  Map.empty
  
