{-# LANGUAGE TemplateHaskell #-}

module Lang.LAMA.Pretty (prettyLama) where

import Development.Placeholders

import Data.Map as Map

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.UnTypedStructure
import qualified Lang.LAMA.Parser.Abs as Abs
import Lang.LAMA.Parser.Print (printTree)

prettyLama :: Ident i => Program i -> String
prettyLama = printTree . trProgram

trProgram :: Ident i => Program i -> Abs.Program
trProgram (Program t c d f i a p) =
  Abs.Program (trTypeDefs t) (trConstantDefs c) (trDecls d)
              (trFlow f) (trInitial i) (trAssertion a) (trInvariant p)

trTypeDefs :: Map (TypeAlias i) (TypeDef i) -> Abs.TypeDefs
trTypeDefs = $notImplemented

trConstantDefs :: Ident i => Map i Constant -> Abs.ConstantDefs
trConstantDefs = $notImplemented

trDecls :: Declarations i -> Abs.Declarations
trDecls = $notImplemented

trFlow :: Flow i -> Abs.Flow
trFlow = $notImplemented

trInitial :: StateInit i -> Abs.Initial
trInitial = $notImplemented

trAssertion :: Expr i -> Abs.Assertion
trAssertion = $notImplemented

trInvariant :: Expr i -> Abs.Invariant
trInvariant = $notImplemented

