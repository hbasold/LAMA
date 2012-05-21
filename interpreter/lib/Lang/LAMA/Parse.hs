module Lang.LAMA.Parse (Error(..), parseLAMA) where

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Lang.LAMA.Parser.Abs as Abs
import qualified Lang.LAMA.Parser.Lex as Lex
import qualified Lang.LAMA.Parser.Par as Par
import Lang.LAMA.Parser.ErrM

import Lang.LAMA.Transform
import Lang.LAMA.TypedStructure
import Lang.LAMA.TypeCheck

lexer :: BS.ByteString -> [Lex.Token]
lexer = Lex.tokens
parse :: [Lex.Token] -> Err Abs.Program
parse = Par.pProgram

data Error = ParseError String | StaticError String | TypeError String deriving Show

parseLAMA :: BS.ByteString -> Either Error Program
parseLAMA inp =
  let ts = lexer inp
  in case parse ts of
    Bad s   -> Left $ ParseError s
    Ok tree -> case absToConc tree of
        Left s -> Left $ StaticError s
        Right concTree -> case typecheck concTree of
          Left s -> Left $ TypeError s
          Right typedTree -> Right typedTree
