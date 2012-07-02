module Lang.LAMA.PrettyTyped where

import Text.PrettyPrint

import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Identifier

prettyType :: Ident i => Type i -> Doc
prettyType (GroundType t) = prettyBaseType t
prettyType (EnumType x) = text $ identString x
prettyType (ArrayType t n) = prettyBaseType t <> (brackets $ integer $ toInteger n)
prettyType (ProdType ts) = case ts of
  [] -> text "1"
  [t] -> prettyType t
  (t':ts') -> foldr (\t doc -> doc <> text " * " <> prettyType t) (prettyType t') ts'

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
    prettyConstExpr' (ConstEnum x) = text $ identString x
    prettyConstExpr' (ConstProd (Prod vs)) =
      parens $ hcat $ punctuate comma $ map prettyConstExpr vs
    prettyConstExpr' (ConstArray (Array vs)) =
      brackets $ hcat $ punctuate comma $ map prettyConstExpr vs

prettyConst :: Constant i -> Doc
prettyConst c = case untyped c of
  BoolConst v -> case v of
    True -> text "true"
    False -> text "false"
  IntConst v -> integer v
  RealConst v -> rational v
  SIntConst _ v -> integer v
  UIntConst _ v -> integer $ toInteger v
