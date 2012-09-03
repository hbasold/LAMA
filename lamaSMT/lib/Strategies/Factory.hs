{-# LANGUAGE NamedFieldPuns #-}
module Strategies.Factory where

import Text.PrettyPrint

import Strategy
import Strategies.BMC

defaultStrategy :: Strategy
defaultStrategy = Strategy (defaultStrategyOpts :: BMC)

getStrategyHelp :: Int -> String
getStrategyHelp lineLength = renderStyle (style { lineLength }) $
  hang
  (fsep [text "Strategy to use on given model.",
         text "Here are the possible strategies",
         text "together with their options",
         text "(given by -o) :"])
  2 (vcat $ map stratHelp strats)

  where
    strats =
      [("bmc",
        [(text "depth=DEPTH (natural number or \"inf\")",
          fsep [text "Depth where the checking process",
                text "should stop if no error is found.",
                text "If \"inf\"(inite) is given,",
                text "it only halts in case of an error."]),
         (text "progress", text "Display progress while checking.")])]

    stratHelp (s, opts) =
      text s $+$ nest 2 (vcat $ map (\(o,descr) -> fsep [text "*" <+> o, nest 2 $ text "—" <+> descr]) opts)

getStrategy :: String -> Strategy
getStrategy "bmc" = Strategy (defaultStrategyOpts :: BMC)
getStrategy _ = error "Unknown strategy"