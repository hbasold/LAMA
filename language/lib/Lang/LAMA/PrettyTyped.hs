module Lang.LAMA.PrettyTyped where

import Text.PrettyPrint

import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Identifier

prettyType :: Ident i => Type i -> Doc
prettyType (GroundType t) = prettyBaseType t
prettyType (NamedType x) = text $ identPretty x
prettyType (ArrayType t n) = prettyBaseType t <> (brackets $ integer $ toInteger n)
prettyType (Prod ts) = case ts of
  [] -> text "1"
  [t] -> prettyType t
  (t':ts') -> foldr (\t doc -> doc <> text " X " <> prettyType t) (prettyType t') ts'

prettyBaseType :: BaseType -> Doc
prettyBaseType BoolT = text "bool"
prettyBaseType IntT = text "int"
prettyBaseType RealT = text "real"
prettyBaseType (SInt n) = text "sint" <> (brackets $ integer $ toInteger n)
prettyBaseType (UInt n) = text "uint" <> (brackets $ integer $ toInteger n)

prettyTyped :: Ident i => (e (Typed i e) -> Doc) -> Typed i e -> Doc
prettyTyped p t = p (untyped t) <+> colon <+> prettyType (getType t)

-----

prettyConstExpr :: Ident i => ConstExpr i -> Doc
prettyConstExpr = prettyTyped prettyConstExpr'
  where
    prettyConstExpr' (Const c) = prettyConst c
    prettyConstExpr' (ConstRecord (RecordConstr x v)) =
      (ptext $ identString x) <> (braces $ hcat $ punctuate comma $ map prettyConstExpr v)
    prettyConstExpr' (ConstTuple (Tuple v)) =
      parens $ hcat $ punctuate comma $ map prettyConstExpr v

prettyConst :: Constant i -> Doc
prettyConst c = case untyped c of
  BoolConst v -> case v of
    True -> text "true"
    False -> text "false"
  IntConst v -> integer v
  RealConst v -> rational v
  SIntConst _ v -> integer v
  UIntConst _ v -> integer $ toInteger v
