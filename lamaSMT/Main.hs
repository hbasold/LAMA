{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
module Main (main) where

import qualified Data.ByteString.Lazy.Char8 as BL

import Text.PrettyPrint (render)
import Data.List.Split (splitOn)

import System.IO (stdin)
import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitSuccess)

import Control.Monad.Trans.Maybe
import Control.Monad (when, MonadPlus(..))
import Control.Monad.IO.Class
import Control.Monad.Error (ErrorT(..))

import Lang.LAMA.Parse
import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure (Program)

import Transform
import Model
import Strategy
import Strategies.Factory

import Language.SMTLib2 (SMT, MonadSMT(..), SMTOption(..), setOption, withSMTSolver)
import Language.SMTLib2.Solver

data Options = Options
  { optInput :: FilePath
  , optStrategy :: Strategy
  , optSMTOpts :: [SMTOption]
  , optScenarioFile :: Maybe FilePath
  , optTopNodePath :: [String]
  , optDebug :: Bool
  , optDumpLama :: Bool
  , optDumpModel :: Bool
  , optShowHelp :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optStrategy           = defaultStrategy
  , optSMTOpts            = [ProduceModels True]
  , optScenarioFile       = Nothing
  , optTopNodePath        = []
  , optDebug              = False
  , optDumpLama           = False
  , optDumpModel          = False
  , optShowHelp           = False
  }

resolveDebug :: Maybe String -> Options -> Options
resolveDebug Nothing opts = opts {optDebug = True}
resolveDebug (Just "dump-lama") opts = opts {optDumpLama = True}
resolveDebug (Just "dump-model") opts = opts {optDumpModel = True}
resolveDebug _ opts = opts

parseNodeName :: String -> [String]
parseNodeName = splitOn "::"

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['i']     []
      (ReqArg (\f opts -> opts {optInput = f}) "FILE")
      "input FILE or stdin"
    , Option ['s'] ["strategy"]
      (ReqArg (\s opts -> opts {optStrategy = getStrategy s}) "STRATEGY")
      (getStrategyHelp 80)
    , Option ['o'] ["option"]
      (ReqArg (\o opts -> opts {optStrategy = readOptions' o $ optStrategy opts}) "OPTION")
      ("Pass options to the requested strategy (one per -o).")
    , Option [] ["scenario"]
      (ReqArg (\f opts -> opts {optScenarioFile = Just f}) "FILE")
      ("File where to put the error Scade trace.")
    , Option [] ["node-name"]
      (ReqArg (\n opts -> opts {optTopNodePath = parseNodeName n}) "SCADE NODE")
      ("Qualified name of Scade node for which the trace should be generated.")
    , Option ['d'] ["debug"]
      (OptArg resolveDebug "WHAT")
      "Debug something; for more specific debugging use one of: [dump-lama,dump-model]"
    , Option ['h'] ["help"]
      (NoArg  (\opts -> opts {optShowHelp = True}))
      "Show this help"
  ]

interpreterOpts :: [String] -> IO Options
interpreterOpts argv =
  case getOpt (ReturnInOrder (\file opts -> opts)) options argv of
    (o,[],[]) ->
      let opts = foldl (flip id) defaultOptions o
      in return opts
    (_, (_:_), []) -> ioError $ userError "Unused free option -- should not happen"
    (_,_,errs) -> ioError (userError (concat errs ++ usage))

usage :: String
usage = usageInfo header options
  where header = "Usage: lamaSMT [OPTION...]"

main :: IO ()
main = do
  argv <- getArgs
  opts <- interpreterOpts argv
  when (optShowHelp opts) $ do
    putStr usage
    exitSuccess
  r <- case (optInput opts) of
    "-" -> BL.hGetContents stdin >>= runMaybeT . run opts "stdin"
    f -> runFile opts f
  case r of
    Just () -> return ()
    Nothing -> return ()

runFile :: Options -> FilePath -> IO (Maybe ())
runFile opts f = BL.readFile f >>= runMaybeT . run opts f

run :: Options -> FilePath -> BL.ByteString -> MaybeT IO ()
run opts@Options {optStrategy = strat} file inp = do
  p <- checkErrors $ parseLAMA inp
  liftIO $ when (optDumpLama opts) (print p)
  model <- liftIO
    . runCheck opts
    $ (liftSMT . mapM_ setOption $ optSMTOpts opts) >>
    lamaSMT p >>= (uncurry $ checkWithModel strat)
  liftIO $ checkModel opts p model

checkErrors :: Either Error a -> MaybeT IO a
checkErrors r = case r of
  Left (ParseError pe) -> printAndFail $ "Parse failed:\n" ++ pe
  Left (StaticError se) -> printAndFail $ "Conversion failed:\n" ++ se
  Left (TypeError te) -> printAndFail $ "Type check failed:\n" ++ te
  Right concTree -> return concTree

printAndFail :: MonadIO m => String -> MaybeT m a
printAndFail e = liftIO (putStrLn e) >> mzero

runCheck :: Options -> SMTErr a -> IO a
runCheck opts = chooseSolver (optDebug opts) . checkError
  where
    checkError :: SMTErr a -> SMT a
    checkError m =
      let smt = runErrorT m
      in do r <- smt
            case r of
              Left err -> liftIO $ fail err
              Right x -> return x

    chooseSolver hasDebug =
      if hasDebug
      then withSMTSolver "tee debug.txt | z3 -smt2 -in -m"
      else withZ3

checkModel :: Ident i => Options -> Program i -> Maybe (Model i) -> IO ()
checkModel _ _ Nothing = putStrLn "42"
checkModel opts prog (Just m) =
  do putStrLn ":-("
     when (optDumpModel opts) (putStrLn . render $ prettyModel m)
     case optScenarioFile opts of
       Nothing -> return ()
       Just f -> writeFile f $ render $ scadeScenario prog (optTopNodePath opts) m