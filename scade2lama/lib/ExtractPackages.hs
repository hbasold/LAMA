module ExtractPackages (Package(..), PackageMap, extract) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State as ST

import Language.Scade.Syntax as S

data Package = Package
               { pkgTypes :: [TypeDecl]
               , pkgSubPackages :: PackageMap
               , pkgUserOps :: Map String Declaration
               , pkgConsts :: [ConstDecl]
               } deriving Show

type PackageMap = Map String Package

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
extract :: [Declaration] -> Package
extract ds = execState (extractDecls ds) emptyPackage

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
