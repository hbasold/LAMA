{-# LANGUAGE TemplateHaskell #-}

module Lang.LAMA.Pretty (prettyLama) where

import Development.Placeholders

import Data.Map as Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.UnTypedStructure
import qualified Lang.LAMA.Parser.Abs as Abs
import Lang.LAMA.Parser.Print (printTree)

prettyLama :: Program -> String
prettyLama = printTree . trProgram

trProgram :: Program -> Abs.Program
trProgram (Program t c d f i a p) =
  Abs.Program (trTypeDefs t) (trConstantDefs c) (trDecls d)
              (trFlow f) (trInitial i) (trAssertion a) (trInvariant p)

trTypeDefs :: Map TypeAlias TypeDef -> Abs.TypeDefs
trTypeDefs = $notImplemented

trConstantDefs :: Map Identifier Constant -> Abs.ConstantDefs
trConstantDefs = $notImplemented

trDecls :: Declarations -> Abs.Declarations
trDecls = $notImplemented

trFlow :: Flow -> Abs.Flow
trFlow = $notImplemented

trInitial :: StateInit -> Abs.Initial
trInitial = $notImplemented

trAssertion :: Expr -> Abs.Assertion
trAssertion = $notImplemented

trInvariant :: Expr -> Abs.Invariant
trInvariant = $notImplemented

