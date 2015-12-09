{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module Strategies.Invariant where

import Debug.Trace

import Data.Natural
import qualified Data.List as List
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe, isJust, fromJust)

import Control.Monad.State (MonadState(..), StateT, evalStateT, modify)
import Control.Monad.Writer (MonadWriter(..), WriterT, runWriterT)
import Control.Monad.IO.Class
import Control.Monad (when, filterM)
import Control.Arrow ((&&&))

import Language.SMTLib2

import Strategy
import LamaSMTTypes
import Definition
import Posets
import TransformEnv
import Model (Model, getModel)
import Strategies.BMC
import Internal.Monads

data GenerateHints =
     NoHints
     | LastInductionStep
     | AllInductionSteps
data Invar = Invar
               { depth :: Maybe Natural
               , printProgress :: Bool
               , printInvStats :: Bool
               , generateHints :: GenerateHints }

instance StrategyClass Invar where
  defaultStrategyOpts = Invar Nothing False False NoHints

  readOption (stripPrefix "depth=" -> Just d) indOpts =
    case d of
      "inf" -> indOpts { depth = Nothing }
      _     -> indOpts { depth = Just $ read d }
  readOption "progress" indOpts =
    indOpts { printProgress = True }
  readOption "invariant-stats" indOpts =
    indOpts { printInvStats = True }
  readOption (stripPrefix "hints" -> Just r) indOpts =
    case (stripPrefix "=" r) of
         Nothing    -> indOpts { generateHints = LastInductionStep }
         Just which -> case which of
              "all"  -> indOpts { generateHints = AllInductionSteps }
              "last" -> indOpts { generateHints = LastInductionStep }
              _      -> error $ "Invalid hint option: " ++ which
  readOption o _ = error $ "Invalid k-induction option: " ++ o

  check indOpts env defs =
    let baseK = 0
        vars  = varList env
    in do k1  <- freshVars vars
          n0  <- freshVars vars
          n1  <- freshVars vars
          assumeTrace defs (n0, n1)
          let s0 = InductState baseK (vars, k1) (n0, n1) (initGraph $ instSetBool env) Nothing (initChains $ instSetInt env) Nothing
          (r, hints) <- runWriterT
                $ (flip evalStateT s0)
                $ check' indOpts (getModel $ varEnv env) defs (Map.singleton baseK vars) [n0]
          case r of
               Unknown what h -> return $ Unknown what (h ++ hints)
               _ -> return r

-- | Checks the induction step and returns true if the invariant could be
-- proven
checkStep :: ProgDefs -> ([TypedExpr], [TypedExpr]) -> SMT Bool
checkStep defs vars =
  do assumeTrace defs vars
     let invs = invariantDef defs
     checkInvariant vars invs

-- | Holds current depth k and definitions of last k and n
data InductState = InductState
                   { kVal     :: Natural
                   , kDefs    :: ([TypedExpr], [TypedExpr])
                   , nDefs    :: ([TypedExpr], [TypedExpr])
                   , binPoset :: Maybe Poset
                   , binInv   :: Maybe Poset
                   , intPoset :: Maybe Poset
                   , intInv   :: Maybe Poset }
type KInductM i = StateT InductState (WriterT (Hints i) SMTErr)

-- | Checks the program against its invariant. If the invariant
-- does not hold in the base case, then a model is returned.
-- If the base case is fine, but the induction step is not, we
-- call next, which increases k. Finally, if also the induction
-- step can be proven, Nothing is returned.
check' :: Invar
       -> (Map Natural [TypedExpr] -> SMT (Model i))
       -> ProgDefs
       -> Map Natural [TypedExpr]
       -> [[TypedExpr]]
       -> KInductM i (StrategyResult i)
check' indOpts getModel defs pastVars pastNs =
  do InductState{..} <- get
     liftIO $ when (printProgress indOpts) (putStrLn $ "Depth " ++ show kVal)
     when (printInvStats indOpts) $ do invStats <- showInvStats
                                       liftIO $ putStrLn invStats
     rBMC <- bmcStep getModel defs pastVars kDefs
     case rBMC of
       Just m -> return $ Failure kVal m
       Nothing ->
         do let n0 = fst nDefs
                n1 = snd nDefs
                pastNs' = pastNs ++ [n1]
            n2 <- freshVars n1
            assertPrecond (n0, n1) $ invariantDef defs
            modify $ \indSt -> indSt { nDefs = (n1, n2) }
            heuristicInvariants indOpts defs pastNs
            (indSuccess, hints) <- liftSMT . stack $
              do r <- checkStep defs (n1, n2)
                 h <- retrieveHints (getModel pastVars) indOpts kVal r
                 return (r, h)
            tell hints
            let k' = succ kVal
            --if indSuccess
               --then return Success
               --else case depth indOpts of
            case depth indOpts of
              Nothing -> cont k' pastVars pastNs'
              Just l  ->
                if k' > l
                  then return $ Unknown ("Cancelled induction. Found no"
                                           ++" proof within given depth")
                                 []
                  else cont k' pastVars pastNs'
  where
    cont k' pastVars pNs =
      do indState@InductState{..} <- get
         let k1 = snd kDefs
             pastVars' = Map.insert k' k1 pastVars
         k2 <- freshVars k1
         put $ indState { kVal = k', kDefs = (k1, k2) }
         check' indOpts getModel defs pastVars' pNs
    showInvStats = do
      InductState{..} <- get
      let boolStat = getPosetStats $ fromMaybe (fromJust binInv) binPoset
          intStat  = getPosetStats $ fromMaybe (fromJust intInv) intPoset
      return $ (if isJust binPoset then "Possible boolean invariants: " ++ boolStat else "Boolean invariants: " ++ boolStat) ++ "\n" ++ (if isJust intPoset then "Possible integer invariants: " ++ intStat else "Integer invariants: " ++ intStat)

heuristicInvariants :: Invar -> ProgDefs -> [[TypedExpr]] -> KInductM i ()
heuristicInvariants indOpts defs pastNs = do
  InductState{..} <- get
  if (isJust binPoset)
  then
    do binPoset' <- filterC (fromJust binPoset) kDefs
       case binPoset' of
         Just b  -> modify $ \indSt -> indSt { binPoset = Just b }
         Nothing -> do liftIO $ when (printInvStats indOpts) $ putStrLn "Trying to prove inductive boolean invariants..."
                       binInv' <- checkInvariantStep (fromJust binPoset) nDefs pastNs defs

                       assertPoset id nDefs binInv'
                       modify $ \indSt -> indSt { binPoset = Nothing, binInv = Just binInv' }
  else
    assertPoset id nDefs $ fromJust binInv
  if (isJust intPoset)
  then
    do intPoset' <- filterC (fromJust intPoset) kDefs
       case intPoset' of
         Just i  -> modify $ \indSt -> indSt { intPoset = Just i }
         Nothing -> do liftIO $ when (printInvStats indOpts) $ putStrLn "Trying to prove inductive integer invariants..."
                       intInv' <- checkInvariantStep (fromJust intPoset) nDefs pastNs defs
                       assertPoset id nDefs intInv'
                       modify $ \indSt -> indSt { intPoset = Nothing, intInv = Just intInv' }
  else
    assertPoset id nDefs $ fromJust intInv

filterC :: MonadSMT m => Poset -> ([TypedExpr], [TypedExpr]) -> m (Maybe Poset)
filterC g@(PosetGraph v e) args =
  liftSMT $ do push
               assertPoset not' args g
               r  <- checkSat
               if r
                 then do v0' <- mapM (filterM (\a -> evalBoolTerm args a >>= return . not)) v
                         v1' <- mapM (filterM $ evalBoolTerm args) v
                         pop
                         return $ Just $ buildNextGraph (v0', v1') e
                  else pop >> return Nothing
filterC i@(PosetChains cs m) args =
  liftSMT $ do push
               assertPoset not' args i
               r  <- checkSat
               if r
                 then do let nodes = concat cs
                         part <- mapM (partitionChainNode args) nodes
                         pop
                         return $ Just $ buildNextChain $ concat part
                  else pop >> return Nothing

partitionChainNode :: MonadSMT m => ([TypedExpr], [TypedExpr]) -> ChainNode -> m [ChainNode]
partitionChainNode args node = do values <- mapM (evalIntTerm args) $ snd node
                                  let comb = zip values (snd node)
                                      part = List.groupBy (\(a,_) (b,_) -> a == b) $ List.sort comb
                                  return $ map (\n -> (fst node ++ [fst (head n)], map snd n)) part

checkInvariantStep :: MonadSMT m => Poset -> ([TypedExpr], [TypedExpr]) -> [[TypedExpr]] -> ProgDefs -> m Poset

checkInvariantStep g args pastVars defs = liftSMT $ do
  push
  mapM (\a -> assertPoset id (a,a) g) $ pastVars
  assumeTrace defs args
  g' <- checkInvariantStep' g
  pop
  return g'
  where
    checkInvariantStep' graph@(PosetGraph v e) = do
      push
      assertPoset not' args graph
      r <- checkSat
      if r
        then do v0' <- mapM (filterM (\a -> evalBoolTerm args a >>= return . not)) v
                v1' <- mapM (filterM $ evalBoolTerm args) v
                pop
                graph' <- checkInvariantStep' $ buildNextGraph (v0', v1') e
                return graph'
         else pop >> return graph
    checkInvariantStep' chains@(PosetChains cs m) = do
      push
      assertPoset not' args chains
      r <- checkSat
      if r
        then do let nodes = concat cs
                part <- mapM (partitionChainNode args) nodes
                pop
                chains' <- checkInvariantStep' $ buildNextChain $ concat part
                return chains'
        else pop >> return chains

-- | If requested, gets a model for the induction step
retrieveHints :: SMT (Model i)
              -> Invar
              -> Natural
              -> Bool
              -> SMT [(Hint i)]
retrieveHints getModel indOpts k success =
  case (generateHints  &&& depth) indOpts of
       (NoHints          , _      ) -> return []
       (LastInductionStep, Nothing) -> return []
       (LastInductionStep, Just l ) ->
         if not success && succ k > l
         then getModel >>= \m -> return [Hint (show k) m]
         else return []
       (AllInductionSteps, _      ) ->
         getModel >>= \m -> return [Hint (show k) m]
