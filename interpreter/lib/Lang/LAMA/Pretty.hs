module Lang.LAMA.Pretty (prettyLama) where

import Lang.LAMA.UnTypedStructure
import qualified Lang.LAMA.Parser.Abs as Abs
import Lang.LAMA.Parser.Print (printTree)

prettyLama :: Program -> String
prettyLama = printTree . trProgram

trProgram :: Program -> Abs.Program
trProgram (Program t c d f i a p) =
  Abs.Program (trTypeDefs t) (trConstantDefs c) (trDecls d)
              (trFlow f) (trInitial i) (trAssertion a) (trInvariant p)


