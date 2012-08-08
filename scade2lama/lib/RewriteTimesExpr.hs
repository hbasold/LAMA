module RewriteTimesExpr (rewrite) where

import Data.Generics.Schemes (everywhere)
import Data.Generics.Aliases (mkT)

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.Scade.Syntax as S

timesOpDefSource :: String
timesOpDefSource =
  "node times_behavior (n : int; c : bool) returns (o : bool)\n" ++
  "var\n" ++
  "  v3, v4 : int;" ++
  "let" ++
  "  v4 = n -> pre (v3);" ++
  "  v3 = if (v4 < 0)" ++
  "       then v4" ++
  "       else (if c then v4 - 1 else v4);" ++
  "  o = c and (v3 = 0);" ++
  "tel"

timesOpDef :: Declaration
timesOpDef = head $ scade $ alexScanTokens timesOpDefSource

rewrite :: [Declaration] -> [Declaration]
rewrite decls = timesOpDef : (everywhere (mkT rewriteTimes) decls)

rewriteTimes :: Expr -> Expr
rewriteTimes (S.TimesExpr n c) =
  S.ApplyExpr (S.PrefixOp . S.PrefixPath $ Path ["times_behavior"]) [n, c]
rewriteTimes e = e

