module Main (main) where

import System.IO (stdin, stdout, stderr, hGetContents, hPutStr, hPutStrLn)
import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitSuccess)

import Control.Monad.Trans.Maybe
import Control.Monad (when, MonadPlus(..), (<=<))
import Control.Monad.IO.Class (liftIO)

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.Scade.Syntax
import Language.Scade.Pretty (prettyScade)
import Text.PrettyPrint (render)

import VarGen
import qualified FlattenListExpr as FlattenList
import qualified RewriteTemporal as Temporal
import qualified RewriteOperatorApp as OpApp
import qualified UnrollTemporal as Unroll
import Transform
import Lang.LAMA.Pretty
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L

data Options = Options
  { optInput :: FilePath
  , optOutput :: FilePath
  , optTopNode :: String
  , optDebug :: Bool
  , optDumpScade :: Bool
  , optDumpLama :: Bool
  , optDumpRewrite :: Bool
  , optShowHelp :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optOutput             = "-"
  , optTopNode            = ""
  , optDebug              = False
  , optDumpScade          = False
  , optDumpLama           = False
  , optDumpRewrite        = False
  , optShowHelp           = False
  }

resolveDebug :: Maybe String -> Options -> Options
resolveDebug Nothing opts = opts {optDebug = True}
resolveDebug (Just "dump-scade") opts = opts {optDumpScade = True}
resolveDebug (Just "dump-lama") opts = opts {optDumpLama = True}
resolveDebug (Just "dump-rewrite") opts = opts {optDumpRewrite = True}
resolveDebug _ opts = opts

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['i']     []
      (ReqArg (\f opts -> opts {optInput = f}) "FILE")
      "input FILE or stdin"
    , Option ['f'] ["file"] (ReqArg (\f opts -> opts {optOutput = f}) "FILE")
      "output FILE or stdout"
    , Option ['d'] ["debug"]
      (OptArg resolveDebug "WHAT")
      "Debug something; for more specific debugging use one of: [dump-scade, dump-lama, dump-rewrite]"
    , Option ['h'] ["help"]
      (NoArg  (\opts -> opts {optShowHelp = True}))
      "Show this help"
  ]

interpreterOpts :: [String] -> IO Options
interpreterOpts argv =
  case getOpt (ReturnInOrder (\f opts -> opts {optTopNode = f})) options argv of
    (o,[],[]) ->
      let opts = foldl (flip id) defaultOptions o
      in return opts
    (_, (_:_), []) -> ioError $ userError "Unused free option -- should not happen"
    (_,_,errs) -> ioError (userError (concat errs ++ usage))

usage :: String
usage = usageInfo header options
  where header = "Usage: scade2lama [OPTION...] NODE"

main :: IO ()
main = do
  argv <- getArgs
  opts <- interpreterOpts argv
  when (optShowHelp opts) $ do
    putStr usage
    exitSuccess
  r <- case (optInput opts) of
    "-" -> hGetContents stdin >>= runMaybeT . run opts "stdin"
    f -> runFile opts f
  case r of
    Just s -> case (optOutput opts) of
      "-" -> hPutStr stdout s
      f -> writeFile f s
    Nothing -> return ()

runFile :: Options -> FilePath -> IO (Maybe String)
runFile opts f = readFile f >>= runMaybeT . run opts f

run :: Options -> FilePath -> String -> MaybeT IO String
run opts f inp = do
  s <- checkScadeError $ scade $ alexScanTokens inp
  liftIO $ when (optDumpScade opts) (putStrLn $ show s)
  let r = evalVarGen (rewrite s) 0
  liftIO $ when (optDumpRewrite opts) (putStrLn $ render $ prettyScade r)
  l <- checkTransformError $ transform (optTopNode opts) r
  liftIO $ when (optDumpLama opts) (putStrLn $ show l)
  return $ prettyLama l

checkScadeError :: [Declaration] -> MaybeT IO [Declaration]
checkScadeError = return

checkTransformError :: Either String L.Program -> MaybeT IO L.Program
checkTransformError (Left e) = (liftIO $ hPutStrLn stderr $ "Transform error: \n" ++ e) >> mzero
checkTransformError (Right p) = return p

rewrite :: [Declaration] -> VarGen [Declaration]
rewrite = -- Temporal.rewrite
          -- <=<
          OpApp.rewrite
          <=< return . Unroll.rewrite
          <=< return . FlattenList.rewrite
