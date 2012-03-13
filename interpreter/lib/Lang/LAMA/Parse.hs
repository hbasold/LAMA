module Lang.LAMA.Parse (Error(..), parseLAMA) where

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Lang.LAMA.Parser.Abs as Abs
import qualified Lang.LAMA.Parser.Lex as Lex
import qualified Lang.LAMA.Parser.Par as Par
import Lang.LAMA.Parser.ErrM

import Lang.LAMA.Structure
import Lang.LAMA.Transform

lexer :: BS.ByteString -> [Lex.Token]
lexer = Lex.tokens
parse :: [Lex.Token] -> Err Abs.File
parse = Par.pFile

data Error = ParseError String | StaticError String deriving Show

parseLAMA :: BS.ByteString -> Either Error Program
parseLAMA inp =
  let ts = lexer inp
  in case parse ts of
    Bad s   -> Left $ ParseError s
    Ok tree -> case absToConc tree of
        Left s -> Left $ StaticError s
        Right concTree -> Right concTree  
