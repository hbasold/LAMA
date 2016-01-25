{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
module Main (main) where

import qualified Data.ByteString.Lazy.Char8 as BL

import Text.PrettyPrint (Doc, render, vcat, text, ($$))
import Data.List.Split (splitOn)

import System.IO (stdin)
import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitSuccess)

import Control.Monad.Trans.Maybe
import Control.Monad (when, MonadPlus(..))
import Control.Monad.IO.Class
import Control.Monad.Error (ErrorT(..))
import Control.Monad.Trans.Class

import Lang.LAMA.Parse
import Lang.LAMA.Identifier
import Lang.LAMA.Typing.TypedStructure (Program)

import SMTEnum
import NatInstance
import Transform
import Model
import Strategy
import Strategies.Factory
import Internal.Monads

import Language.SMTLib2 (SMT, SMTOption(..), setOption)
import Language.SMTLib2.Pipe (withPipe)

z3Base :: String
-- z3Base = "z3 -smt2 -in"
z3Base = "z3"

z3Debug :: String
-- z3Base = "z3 -smt2 -in"
z3Debug = "z3-debug"

data Options = Options
  { optInput :: FilePath
  , optStrategy :: Strategy
  , optSMTOpts :: [SMTOption]
  , optScenarioFile :: Maybe FilePath
  , optTopNodePath :: [String]
  , optSolver :: String -- ^ base command to run solver
  , optSolverOptions :: [String]
  , optNatImpl :: NatImplementation
  , optEnumImpl :: EnumImplementation
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
  , optSolver             = z3Base
  , optSolverOptions      = []
  , optNatImpl            = NatType
  , optEnumImpl           = EnumImplType
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

parseNatImpl :: String -> NatImplementation
parseNatImpl "type" = NatType
parseNatImpl "int" = NatInt
parseNatImpl i = error $ "Invalid natural implementation: " ++ i

parseEnumImpl :: String -> EnumImplementation
parseEnumImpl "type" = EnumImplType
parseEnumImpl "bits" = EnumImplBit
parseEnumImpl i = error $ "Invalid enum implementation: " ++ i

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
    , Option [] ["solver"]
      (ReqArg (\s opts -> opts {optSolver = s}) "CMD")
      ("Command to run solver interactively using SMTLib2 input.")
    , Option [] ["solver-opts"]
      (ReqArg (\o opts -> opts {optSolverOptions = optSolverOptions opts ++ [o]}) "OPTION")
      ("Additional option to pass to used SMT solver.")
    , Option [] ["nat-impl"]
      (ReqArg (\i opts -> opts {optNatImpl = parseNatImpl i}) "IMPL")
      ("Implementation to use for natural numbers. Can be one of {type, int}.")
    , Option [] ["enum-impl"]
      (ReqArg (\i opts -> opts {optEnumImpl = parseEnumImpl i}) "IMPL")
      ("Implementation to use for enumerations. Can be one of {type, bits}.")
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
run opts@Options{..} file inp = do
  p <- checkErrors $ parseLAMA inp
  liftIO $ when optDumpLama (print p)
  model <- runCheck opts
    ( (liftSMT $ mapM_ setOption optSMTOpts) >>
      lamaSMT optNatImpl optEnumImpl p >>=
      (uncurry $ checkWithModel optStrategy) )
  liftIO $ checkModel opts p model

checkErrors :: Either Error a -> MaybeT IO a
checkErrors r = case r of
  Left (ParseError pe) -> printAndFail $ "Parse failed:\n" ++ pe
  Left (StaticError se) -> printAndFail $ "Conversion failed:\n" ++ se
  Left (TypeError te) -> printAndFail $ "Type check failed:\n" ++ te
  Right concTree -> return concTree

printAndFail :: MonadIO m => String -> MaybeT m a
printAndFail e = liftIO (putStrLn e) >> mzero

runCheck :: Options -> SMTErr a -> MaybeT IO a
runCheck progOpts = chooseSolver progOpts . checkError
  where
    checkError :: SMTErr a -> MaybeT SMT a
    checkError m =
      let smt = runErrorT m
      in do r <- lift smt
            case r of
              Left err -> printAndFail err
              Right x -> return x

    chooseSolver :: Options -> MaybeT SMT a -> MaybeT IO a
    chooseSolver opts =
      let solverCmd = if optDebug opts then z3Debug else z3Base
      in mapMaybeT
         $ withPipe solverCmd (["-smt2","-in"] ++ optSolverOptions opts)
--      let -- solverBase = optSolver opts ++ " " ++ (intercalate " " $ optSolverOptions opts)
          -- solverCmd = (if optDebug opts then "tee debug.txt | " else "")
                      -- ++ solverBase
  -- withPipe solverCmd []

checkModel :: Ident i =>
           Options
           -> Program i
           -> (StrategyResult i)
           -> IO ()
checkModel _ _ Success = putStrLn "42"
checkModel opts prog (Failure lastIndex m) =
  do putStrLn ":-("
     putStrLn $ "Found counterexample at depth " ++ show lastIndex
     when (optDumpModel opts) (putStrLn . render $ prettyModel m)
     case optScenarioFile opts of
       Nothing -> return ()
       Just f -> writeFile f $ render $ scadeScenario prog (optTopNodePath opts) m
checkModel opts prog (Unknown what hints) =
  do putStrLn ":-("
     putStrLn what
     when (optDumpModel opts)
          (putStrLn . render . prettyHints $ hints)
     case optScenarioFile opts of
       Nothing -> return ()
       Just f ->
         mapM_ (\h ->
                 writeFile (f ++ "_" ++ hintDescr h)
                 . render
                 $ scadeScenario prog (optTopNodePath opts) (hintModel h))
               hints

prettyHints :: Ident i => Hints i -> Doc
prettyHints = vcat . map prettyHint
  where
    prettyHint h
      = text ("Hint for " ++ (hintDescr h))
        $$ prettyModel (hintModel h)
