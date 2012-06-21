module Lang.LAMA.Identifier where

import qualified Data.ByteString.Char8 as BS

class (Eq i, Ord i, Show i) => Ident i where
  identBS :: i -> BS.ByteString
  identPretty :: i -> String

identString :: Ident i => i -> String
identString = BS.unpack . identBS

type SourcePosition = (Int, Int)
data PosIdent = PosIdent BS.ByteString SourcePosition deriving Show

instance Eq PosIdent where
  (PosIdent s1 _) == (PosIdent s2 _) = s1 == s2

instance Ord PosIdent where
  compare (PosIdent s1 _) (PosIdent s2 _) = compare s1 s2

instance Ident PosIdent where
  identBS (PosIdent s _) = s
  identPretty (PosIdent x (l, c)) = show x ++ " in line " ++ show l ++ " at column " ++ show c

newtype SimpIdent = SimpIdent BS.ByteString deriving (Eq, Ord, Show)

instance Ident SimpIdent where
  identBS (SimpIdent s) = s
  identPretty (SimpIdent x) = show x

dropPos :: PosIdent -> SimpIdent
dropPos = SimpIdent . identBS
