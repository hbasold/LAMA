module Main (main) where

import qualified Data.Set as Set
import Data.List.Split (splitOn)
import Data.Foldable (foldlM)

import System.IO (stdin, stdout, stderr, hGetContents, hPutStr, hPutStrLn)
import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitSuccess)

import Control.Monad.Trans.Class
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Trans.Maybe
import Control.Monad (when, MonadPlus(..), (<=<))
import Control.Monad.IO.Class

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.Scade.Syntax

import Text.PrettyPrint (render)

import Options
import VarGen
import qualified RewriteTimesExpr as Times
import qualified FlattenListExpr as FlattenList
import qualified Inlining as Inline
import qualified RewriteClockedEquation as Clocked
import qualified RewriteOperatorApp as OpApp
import qualified UnrollTemporal as Unroll
import qualified UnrollFby as Fby
import ExtractPackages
import TransformPackage
import Lang.LAMA.Pretty

resolveDebug :: Maybe String -> Options -> Options
resolveDebug Nothing opts = opts {optDebug = True}
resolveDebug (Just "dump-scade") opts = opts {optDumpScade = True}
resolveDebug (Just "dump-lama") opts = opts {optDumpLama = True}
resolveDebug (Just "dump-rewrite") opts = opts {optDumpRewrite = True}
resolveDebug _ opts = opts

resolveInline :: Maybe String -> Options -> Either String Options
resolveInline Nothing = return
resolveInline (Just extra) = resolve' extra
  where
    resolve' o opts =
      let os = splitOn "," o
          nameValueAssoc = map (splitOn "=") os
      in do inlineOpts' <- foldlM assignValue (optInline opts) nameValueAssoc
            return $ opts {optInline = inlineOpts'}
    assignValue inlOpts ["depth", d] = return $ inlOpts { inlineDepth = read d }
    assignValue inlOpts ["state-scope"] =
      return $ inlOpts { inlineScopes = Set.insert InlineStateScope (inlineScopes inlOpts) }
    assignValue _ [n, v] = throwError $ "Unknown inlining option: " ++ n ++ "=" ++ v
    assignValue _ [n] = throwError $ "Unknown inlining option: " ++ n
    assignValue _ o = throwError $ "Invalid inlining option: " ++ show o

options :: [OptDescr (Options -> Either String Options)]
options =
  [ Option ['i']     []
      (ReqArg (\f opts -> return $ opts {optInput = f}) "FILE")
      "input FILE or stdin"
    , Option ['f'] ["file"] (ReqArg (\f opts -> return $ opts {optOutput = f}) "FILE")
      "output FILE or stdout"
    , Option [] ["inline"] (OptArg (\o -> resolveInline o . activateInlining) "OPTIONS")
      ("Activates inlining with optional extra options (comma separated). " ++
       "Those can be: depth=<int>, state-scope.")
    , Option ['d'] ["debug"]
      (OptArg (\o -> return . resolveDebug o) "WHAT")
      "Debug something; for more specific debugging use one of: [dump-scade, dump-lama, dump-rewrite]"
    , Option ['h'] ["help"]
      (NoArg  (\opts -> return $ opts {optShowHelp = True}))
      "Show this help"
  ]

interpreterOpts :: [String] -> IO Options
interpreterOpts argv =
  case getOpt (ReturnInOrder (\f opts -> return $ opts {optTopNode = f})) options argv of
    (o,[],[]) ->
      let r = foldlM (flip id) defaultOptions o
      in case r of
        Left err -> ioError $ userError err
        Right opts -> return opts
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
run opts f inp = (flip evalVarGenT 50) $ do
  s <- lift $ checkScadeError $ scade $ alexScanTokens inp
  liftIO $ when (optDumpScade opts) (putStrLn $ show s)
  r <- checkErr "Rewrite error:" =<< (runInVarGenT $ (flip runReaderT opts) $ runErrorT $ rewrite s)
  let ps = extractPackages r
  ps' <- checkErr "Rewrite error:" =<< (runInVarGenT $ runErrorT $ rewrite2 ps)
  liftIO $ when (optDumpRewrite opts) (putStrLn $ render $ prettyPackage ps')
  l <- checkErr "Tranform error:" =<< (runInVarGenT $ transformPackage (optTopNode opts) ps')
  liftIO $ when (optDumpLama opts) (putStrLn $ show l)
  return $ prettyLama l

checkScadeError :: [Declaration] -> MaybeT IO [Declaration]
checkScadeError = return

checkErr :: (MonadPlus m, MonadIO m) => String -> Either String a -> m a
checkErr prefix (Left err) = (liftIO . hPutStrLn stderr $ prefix ++ " " ++ err) >> mzero
checkErr _ (Right x) = return x

rewrite :: [Declaration] -> ErrorT String (ReaderT Options VarGen) [Declaration]
rewrite = -- Temporal.rewrite
          -- <=<
          Unroll.rewrite
          <=< Fby.rewrite
          <=< Inline.rewrite -- for now: after clock equation rewrite because that produces states
          <=< Clocked.rewrite
          <=< return . FlattenList.rewrite
          <=< return . Times.rewrite

rewrite2 :: Package -> ErrorT String VarGen Package
rewrite2 = OpApp.rewrite