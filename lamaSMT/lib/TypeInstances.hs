module TypeInstances where

import Lang.LAMA.Types

deriving instance Typeable BaseType

instance SMTType (Type i) where
  type SMTAnnotation (Type i) = (Type i)
  getSort _ t = L.Symbol $ typeStr t
    where
      typeStr (GroundType BoolT) = "Bool"
      typeStr (GroundType IntT) = "Int"
      typeStr (GroundType RealT) = "Real"
      typeStr _ = error "type not implemented"
  declareType u _ = [(typeOf u, return ())]

instance SMTValue Natural where
  unmangle (L.Symbol "zero") _ = return $ Just $ fromInteger 0
  unmangle (L.List [L.Symbol "succ", r]) a = fmap (fmap (+1)) $ unmangle r a
  unmangle _ _ = return Nothing

  mangle (view -> Zero) _ = L.Symbol "zero"
  mangle (view -> Succ n) a = L.List [L.Symbol "succ", mangle n a]