module Main (main) where

import System.IO (stdin, hGetContents)
import System.Environment (getArgs)

import Control.Monad.Trans.Maybe
import Control.Monad (void, when, MonadPlus(..))
import Control.Monad.IO.Class (liftIO)

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.Scade.Syntax

import Transform
import Lang.LAMA.Pretty
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= void . runMaybeT . run 2 "stdin"
            "-v":v:fs -> mapM_ (runFile (read v)) fs
            fs -> mapM_ (runFile 0) fs

type Verbosity = Int

whenV :: Monad m => Verbosity -> Verbosity -> m () -> m ()
whenV atLeast v = when (v >= atLeast)

putStrV :: Verbosity -> Verbosity -> String -> IO ()
putStrV atLeast v s = whenV atLeast v (putStrLn s)

runFile :: Verbosity -> FilePath -> IO ()
runFile v f = putStrLn f >> readFile f >>= runMaybeT' . run v f
  where
    runMaybeT' :: Functor m => MaybeT m () -> m ()
    runMaybeT' = void . runMaybeT

run :: Verbosity -> FilePath -> String -> MaybeT IO ()
run v f inp = do
  s <- checkScadeError $ scade $ alexScanTokens inp
  liftIO $ putStrV 2 v $ show s
  l <- checkTransformError $ transform s  
  liftIO $ putStrV 1 v $ (f ++ " as LAMA:")
  liftIO $ putStrV 1 v $ prettyLama l

checkScadeError :: [Declaration] -> MaybeT IO [Declaration]
checkScadeError = return

checkTransformError :: Either String L.Program -> MaybeT IO L.Program
checkTransformError (Left e) = (liftIO $ putStrLn $ "Transform error: \n" ++ e) >> mzero
checkTransformError (Right p) = return p
