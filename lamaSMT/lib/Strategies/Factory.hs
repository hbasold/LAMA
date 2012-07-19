module Strategies.Factory where

import Strategy
import Strategies.BMC

defaultStrategy :: Strategy
defaultStrategy = Strategy (defaultStrategyOpts :: BMC)

getStrategyNames :: [String]
getStrategyNames = ["bmc"]

getStrategy :: String -> Strategy
getStrategy "bmc" = Strategy (defaultStrategyOpts :: BMC)
getStrategy _ = error "Unknown strategy"