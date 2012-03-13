{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Test.HUnit
import Control.Monad (when)
import System.Exit

import qualified TestAbsTrans as Abs

tests = TestList [
    TestLabel "TestAbsTrans" Abs.tests
  ]

main :: IO ()
main =
  runTestTT tests >>= \cnts ->
  when ((errors cnts) + (failures cnts) > 0) exitFailure
