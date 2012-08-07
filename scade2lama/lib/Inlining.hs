{-# LANGUAGE FlexibleContexts #-}
module Inlining where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (catMaybes, maybeToList)

import Data.Typeable
import Data.Generics.Schemes
import Data.Generics.Aliases

import Control.Monad.Reader (Reader, runReader, MonadReader(..), asks)

import Language.Scade.Syntax as S

import Options

rewrite :: (MonadReader Options m) => [Declaration] -> m [Declaration]
rewrite decls =
  do opts <- asks optInline
     if inlineActive opts
       then return $ (flip runReader opts) (inline opts decls)
       else return decls

inline :: InlineOptions -> [Declaration] -> Reader InlineOptions [Declaration]
inline opts = everywhereM (buildInline $ inlineScopes opts)

buildInline :: Typeable a => Set.Set InlineScope -> (a -> Reader InlineOptions a)
buildInline scopes = return `extM`
                     (inlineStateScope $ Set.member InlineStateScope scopes)

inlineStateScope :: Bool -> (State -> Reader InlineOptions State)
inlineStateScope active = if active then inlineState else return

inlineState :: State -> Reader InlineOptions State
inlineState s = inlineDataDef (stateData s) >>= \d' -> return $ s { stateData = d' }

inlineDataDef :: DataDef -> Reader InlineOptions DataDef
inlineDataDef def =
  let vars = Set.fromList . getLocals $ dataLocals def
      eqs = dataEquations def
      varDefs = getDefs vars eqs 
  in do (eqs', inlinedVars) <- inlineEquations varDefs eqs
        let vars' = removeInlined inlinedVars (dataLocals def)
        return def { dataLocals = vars', dataEquations = eqs' }        
  where
    getLocals :: [VarDecl] -> [String]
    getLocals = concat . map (map name . varNames)

    getDefs :: Set String -> [Equation] -> Map String (Expr, Bool)
    getDefs locals = foldl (getDef locals) Map.empty

    -- The map assigns to every local variable its defining expression
    -- together with the number of times it has been inlined and
    -- wether it is simple or not.
    getDef :: Set String -> Map String (Expr, Bool) -> Equation -> Map String (Expr, Bool)
    getDef locals defs (SimpleEquation [Named x] expr) =
      if x `Set.member` locals
      then Map.insert x (expr, isSimple expr) defs
      else defs
    getDef _ defs _ = defs

    removeInlined :: Set String -> [VarDecl] -> [VarDecl]
    removeInlined inlinedVars = foldl (\vds vd -> vds ++ maybeToList (remove inlinedVars vd)) []

    remove inlined vd =
      let vs = varNames vd
          vs' = filter (not . flip Set.member inlined . name) vs
      in case vs' of
        [] -> Nothing
        _ -> Just $ vd { varNames = vs' }

isSimple :: Expr -> Bool
isSimple (IdExpr _) = True
isSimple (ConstIntExpr _) = True
isSimple (ConstBoolExpr _) = True
isSimple (ConstFloatExpr _) = True
isSimple (ConstPolyIntExpr _ _) = True
isSimple _ = False

-- | Returns the modified equations and the variables that have been
-- inlined.
inlineEquations :: MonadReader InlineOptions m => Map String (Expr, Bool) -> [Equation] -> m ([Equation], Set String)
inlineEquations assigns eqs =
  do branches <- asks inlineBranches
     inlSimple <- asks inlineAlwaysSimple
     let occurences = count eqs
         fewBranches = Map.filter (<= branches) occurences
         simpleAssigns = if inlSimple then Map.filter snd assigns else Map.empty
         toInline = (assigns `Map.intersection` fewBranches) `Map.union` simpleAssigns
     return $ (catMaybes $ map (doInline toInline) eqs, Map.keysSet toInline)
  where
    count = everything (Map.unionWith (+)) (mkQ Map.empty countVarUsages)

    countVarUsages :: Expr -> Map String Int
    countVarUsages (IdExpr (Path [x])) = Map.singleton x 1
    countVarUsages _ = Map.empty

    doInline :: Map String (Expr, Bool) -> Equation -> Maybe Equation
    doInline toInline eq@(SimpleEquation [Named x] _)
      | x `Map.member` toInline = Nothing
      | otherwise = Just $ everywhere (mkT $ subst toInline) eq
    doInline toInline eq = Just $ everywhere (mkT $ subst toInline) eq

    subst :: Map String (Expr, Bool) -> Expr -> Expr
    subst s e@(IdExpr (Path [x])) =
      case Map.lookup x s of
        Just (e', _) -> e'
        Nothing -> e
    subst _ e = e