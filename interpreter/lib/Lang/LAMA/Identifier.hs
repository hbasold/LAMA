module Lang.LAMA.Identifier where

import qualified Data.ByteString.Char8 as BS

type SourcePosition = (Int, Int)
data Identifier = Id BS.ByteString SourcePosition deriving Show

identString :: Identifier -> String
identString (Id s _) = BS.unpack s

instance Eq Identifier where
  (Id s1 _) == (Id s2 _) = s1 == s2

instance Ord Identifier where
  compare (Id s1 _) (Id s2 _) = compare s1 s2

prettyIdentifier :: Identifier -> String
prettyIdentifier (Id x (l, c)) = show x ++ " in line " ++ show l ++ " at column " ++ show c
