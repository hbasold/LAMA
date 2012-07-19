{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
module Main (main) where

import qualified Data.ByteString.Lazy.Char8 as BL

import System.IO (stdin)
import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitSuccess)

import Control.Monad.Trans.Maybe
import Control.Monad (when, MonadPlus(..))
import Control.Monad.IO.Class
import Control.Monad.Error (ErrorT(..))

import Lang.LAMA.Parse

import Transform
import Strategy
import Strategies.BMC

import Language.SMTLib2 (SMT, withSMTSolver)
import Language.SMTLib2.Solver

data Options = forall s . Strategy s => Options
  { optInput :: FilePath
  , optStrategy :: s
  , optDebug :: Bool
  , optShowHelp :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optStrategy           = BMC 5
  , optDebug              = False
  , optShowHelp           = False
  }

resolveDebug :: Maybe String -> Options -> Options
resolveDebug Nothing opts = opts {optDebug = True}
resolveDebug _ opts = opts

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['i']     []
      (ReqArg (\f opts -> opts {optInput = f}) "FILE")
      "input FILE or stdin"
    , Option ['d'] ["debug"]
      (OptArg resolveDebug "WHAT")
      "Debug something; for more specific debugging use one of: [dump-scade]"
    , Option ['h'] ["help"]
      (NoArg  (\opts -> opts {optShowHelp = True}))
      "Show this help"
  ]

interpreterOpts :: [String] -> IO Options
interpreterOpts argv =
  case getOpt (ReturnInOrder (\f opts -> opts)) options argv of
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
    Just s -> return ()
    Nothing -> return ()

runFile :: Options -> FilePath -> IO (Maybe ())
runFile opts f = BL.readFile f >>= runMaybeT . run opts f

run :: Options -> FilePath -> BL.ByteString -> MaybeT IO ()
run opts@Options {optStrategy = strat} f inp = do
  p <- checkErrors $ parseLAMA inp
  liftIO $ runCheck opts $ check strat =<< lamaSMT p

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