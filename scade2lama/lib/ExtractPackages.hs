{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
module ExtractPackages (Package(..), PackageMap, extractPackages, prettyPackage, getOpType) where

import Development.Placeholders

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Typeable
import Data.Data

import Text.PrettyPrint

import Control.Monad.State as ST
import Control.Monad.Error (MonadError(..))

import Language.Scade.Syntax as S
import Language.Scade.Pretty as S

import Lookup

data Package = Package
               { pkgTypes :: [TypeDecl]
               , pkgSubPackages :: PackageMap
               , pkgUserOps :: Map String Declaration
               , pkgConsts :: [ConstDecl]
               } deriving (Show, Typeable, Data)

type PackageMap = Map String Package

prettyPackage :: Package -> Doc
prettyPackage = prettyScade . mkDecls
  where
    mkDecls p =
      let pkgDecls = map (\(n, p) -> PackageDecl Nothing n (mkDecls p)) . Map.toList $ pkgSubPackages p
          opDecls = Map.elems $ pkgUserOps p
      in [TypeBlock $ pkgTypes p, ConstBlock $ pkgConsts p] ++ opDecls ++ pkgDecls

emptyPackage :: Package
emptyPackage = Package [] Map.empty Map.empty []

addPackage :: String -> Package -> Package -> Package
addPackage n sub p
  = p { pkgSubPackages = Map.insert n sub (pkgSubPackages p) }

putDecl :: Declaration -> Result ()
putDecl (TypeBlock ts) = modify (\p -> p { pkgTypes = (pkgTypes p) ++ ts })
putDecl op@(UserOpDecl {}) = modify (\p -> p { pkgUserOps = Map.insert (userOpName op) op (pkgUserOps p) })
putDecl (ConstBlock cs) = modify (\p -> p { pkgConsts = (pkgConsts p) ++ cs })
putDecl d = error $ "Should have already been done" ++ show d

-- | Extracts all packages
extractPackages :: [Declaration] -> Package
extractPackages ds = execState (extractDecls ds) emptyPackage

type Result = ST.State Package

openPackage :: String -> Result a -> Result a
openPackage n m =
  do curr <- get
     put emptyPackage
     x <- m
     new <- get
     put $ addPackage n new curr
     return x

extractDecls :: [Declaration] -> Result ()
extractDecls = mapM_ extractDecl

extractDecl :: Declaration -> Result ()
extractDecl (PackageDecl _vis n ds)
  = openPackage n $ extractDecls ds
extractDecl d = putDecl d

findPackage :: Package -> [String] -> Maybe Package
findPackage curr [] = Just curr
findPackage curr (p:ps) =
  case Map.lookup p $ pkgSubPackages curr of
    Nothing -> Nothing
    Just next -> findPackage next ps

getOpType :: MonadError String m => Path -> [Package] -> m TypeExpr
getOpType (Path p) pkgs =
  let o = last p
      p' = init p
      mpkg = msum $ map (flip findPackage p')  pkgs
  in case mpkg of
    Nothing -> throwError $ "Unknow path " ++ show p'
    Just pkg ->
      do op <- lookupErr ("Unknown operator " ++ o) o $ pkgUserOps pkg
         case userOpReturns op of
          [VarDecl [_] t _ _] -> return t
          _ -> $notImplemented