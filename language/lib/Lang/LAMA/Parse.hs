module Lang.LAMA.Parse (Error(..), parseLAMA, parseLAMAExpr, parseLAMAConstExpr) where

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Lang.LAMA.Parser.Abs as Abs
import qualified Lang.LAMA.Parser.Lex as Lex
import qualified Lang.LAMA.Parser.Par as Par
import Lang.LAMA.Parser.ErrM

import Lang.LAMA.Transform
import Lang.LAMA.Structure.PosIdentTyped
import qualified Lang.LAMA.Structure.PosIdentUntyped as UT
import Lang.LAMA.Typing.TypeCheck

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

parseLAMAConstExpr :: BS.ByteString -> Either Error ConstExpr
parseLAMAConstExpr inp =
  let ts = lexer inp
  in case Par.pConstExpr ts of
    Bad s   -> Left $ ParseError s
    Ok tree -> case trConstExpr tree of
        Left s -> Left $ StaticError s
        Right concTree -> case typecheckConstExpr concTree of
          Left s -> Left $ TypeError s
          Right typedTree -> Right typedTree

parseLAMAExpr :: BS.ByteString -> Either Error UT.Expr
parseLAMAExpr inp =
  let ts = lexer inp
  in case Par.pExpr ts of
    Bad s   -> Left $ ParseError s
    Ok tree -> case trExpr tree of
        Left s -> Left $ StaticError s
        Right e -> Right e