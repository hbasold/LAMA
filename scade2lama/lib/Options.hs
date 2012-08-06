module Options where

data Options = Options
  { optInput :: FilePath
  , optOutput :: FilePath
  , optTopNode :: String
  , optClockAsAutomaton :: Bool
  , optDebug :: Bool
  , optDumpScade :: Bool
  , optDumpLama :: Bool
  , optDumpRewrite :: Bool
  , optShowHelp :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optOutput             = "-"
  , optTopNode            = ""
  , optClockAsAutomaton   = True
  , optDebug              = False
  , optDumpScade          = False
  , optDumpLama           = False
  , optDumpRewrite        = False
  , optShowHelp           = False
  }