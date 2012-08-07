module Options where

import Data.Set as Set

data InlineScope =
  InlineStateScope
  deriving (Eq, Ord, Show)

data InlineOptions =
  InlineOptions
  { inlineActive :: Bool
  , inlineDepth :: Int
  , inlineBranches :: Int -- ^ How often is a variable allowed to be inlined?
  , inlineAlwaysSimple :: Bool
    -- ^ Simple expressions (constants, variables) are always inlined.
    -- Overrides inlineBranches.
  , inlineScopes :: Set InlineScope
  } deriving Show

defaultInlineOptions :: InlineOptions
defaultInlineOptions =
  InlineOptions
  { inlineActive = False
  , inlineDepth = 10
  , inlineBranches = 1
  , inlineAlwaysSimple = True
  , inlineScopes = Set.singleton InlineStateScope
  }

data Options = Options
  { optInput :: FilePath
  , optOutput :: FilePath
  , optTopNode :: String
  , optClockAsAutomaton :: Bool
  , optInline :: InlineOptions
  , optDebug :: Bool
  , optDumpScade :: Bool
  , optDumpLama :: Bool
  , optDumpRewrite :: Bool
  , optShowHelp :: Bool
  } deriving Show

defaultOptions :: Options
defaultOptions = Options
  { optInput              = "-"
  , optOutput             = "-"
  , optTopNode            = ""
  , optClockAsAutomaton   = True
  , optInline             = defaultInlineOptions
  , optDebug              = False
  , optDumpScade          = False
  , optDumpLama           = False
  , optDumpRewrite        = False
  , optShowHelp           = False
  }

activateInlining :: Options -> Options
activateInlining opts = opts { optInline = (optInline opts) {inlineActive = True} }