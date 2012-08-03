{-# LANGUAGE FlexibleContexts #-}
module TransformMonads where

import qualified  Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.String (fromString)

import Control.Monad.State (MonadState(..), StateT(..), gets, modify)
import Control.Monad.Error (MonadError(..), ErrorT(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Monad.Writer (MonadWriter(..), WriterT(..))

import qualified Language.Scade.Syntax as S
import qualified Lang.LAMA.Structure.SimpIdentUntyped as L
import qualified Lang.LAMA.Identifier as L
import qualified Lang.LAMA.Types as L

import VarGen
import ExtractPackages as Extract

lookupErr :: (MonadError e m, Ord k) => e -> k -> Map k v -> m v
lookupErr err k m = case Map.lookup k m of
  Nothing -> throwError err
  Just v -> return v

type Type = L.Type L.SimpIdent
type TypeAlias = L.TypeAlias L.SimpIdent

data Decls = Decls {
     types :: Map TypeAlias (Either Type L.EnumDef),
     -- | Maps an identifier to the declared nodes in the current package
     nodes :: Map L.SimpIdent L.Node,
     -- | Default expressions for variables
     defaults :: Map L.SimpIdent L.Expr,
     -- | Initial values for variables used in last expressions
     lastInits :: Map L.SimpIdent (Either L.ConstExpr L.Expr),
     -- | Subpackages
     packages :: Map L.SimpIdent Decls,
     constants :: [S.ConstDecl]
  } deriving Show

emptyDecls :: Decls
emptyDecls = Decls Map.empty Map.empty Map.empty Map.empty Map.empty []

data ScadePackages = ScadePackages
                     { global :: Package
                     , current :: Package
                     } deriving Show

type PackageEnv = ReaderT ScadePackages VarGen
type TransM = StateT Decls (ErrorT String PackageEnv)

runTransM :: TransM a -> Package -> Either String (a, Decls)
runTransM m p = (flip evalVarGen 50)
                . (flip runReaderT (ScadePackages p p))
                . runErrorT
                . (flip runStateT emptyDecls)
                $ m

askGlobalPkg :: (MonadReader ScadePackages m) => m Package
askGlobalPkg = reader global

askCurrentPkg :: (MonadReader ScadePackages m) => m Package
askCurrentPkg = reader current

localPkg :: (MonadReader ScadePackages m) => (Package -> Package) -> m a -> m a
localPkg f = local (\ps -> ps { current = f $ current ps })

-- | Executes an action with a local state. The resulting state
-- is then combined with that befor using the given function
-- (comb newState oldState).
localState :: MonadState s m => (s -> s -> s) -> (s -> s) -> m a -> m a
localState comb f m =
  do curr <- get
     put $ f curr
     x <- m
     new <- get
     put $ comb new curr
     return x

updatePackage :: L.SimpIdent -> Decls -> Decls -> Decls
updatePackage n p ds = ds { packages = Map.adjust (const p) n $ packages ds }

createPackage :: L.SimpIdent -> TransM Decls
createPackage p = gets packages >>= return . Map.findWithDefault emptyDecls p

-- | Opens a package using the given reader action.
openPackage :: [String] -> TransM a -> TransM a
openPackage [] m = m
openPackage (p:ps) m =
  do scadePkg <- lookupErr ("Unknown package " ++ p) p =<< fmap pkgSubPackages askCurrentPkg
     let p' = fromString p
     pkg <- createPackage p'
     localState (updatePackage p') (const pkg)
       . localPkg (const scadePkg)
       $ openPackage ps m

-- | Checks if there is a node with the given name in the current package
packageHasNode :: L.SimpIdent -> TransM Bool
packageHasNode x = gets nodes >>= return . Map.member x

addDefaults :: Map L.SimpIdent L.Expr -> TransM ()
addDefaults defs = modify $ \decls ->
  decls { defaults = defaults decls `Map.union` defs }

addLastInits :: Map L.SimpIdent (Either L.ConstExpr L.Expr) -> TransM ()
addLastInits inits = modify $ \decls ->
  decls { lastInits = lastInits decls `Map.union` inits }

-- | Extends TransM by a writer which tracks used nodes
type TrackUsedNodes = WriterT (Set S.Path) TransM

tellNode :: MonadWriter (Set S.Path) m => S.Path -> m ()
tellNode = tell . Set.singleton
