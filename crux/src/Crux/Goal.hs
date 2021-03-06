{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# Language ImplicitParams #-}
{-# Language MultiWayIf #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}
{-# Language ViewPatterns #-}

module Crux.Goal where

import Control.Concurrent.Async (async, asyncThreadId, waitAnyCatch)
import Control.Exception (throwTo, SomeException, displayException)
import Control.Lens ((^.), view)
import qualified Control.Lens as L
import Control.Monad (forM, forM_, unless, when)
import Data.Either (partitionEithers)
import qualified Data.Foldable as F
import Data.IORef
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Void
import           Prettyprinter
import           System.Exit (ExitCode(ExitSuccess))
import qualified System.Timeout as ST

import What4.Interface (notPred, printSymExpr,asConstantPred,getConfiguration)
import What4.Config (setOpt, getOptionSetting)
import qualified What4.Interface as WI
import What4.SatResult(SatResult(..))
import What4.Expr (ExprBuilder, GroundEvalFn(..), BoolExpr)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, getUnsatCore )
import What4.Protocol.SMTWriter( mkFormula, assumeFormulaWithFreshName
                               , assumeFormula, smtExprGroundEvalFn )
import qualified What4.Solver as WS
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackend, withSolverProcess, enableOnlineBackend )
import Lang.Crucible.Simulator.SimError
        ( SimError(..), SimErrorReason(..) )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)
import Lang.Crucible.Panic (panic)

import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common
import Crux.ProgressBar


-- | Simplify the proved goals.
provedGoalsTree ::
  ( IsSymInterface sym
  ) =>
  SimCtxt personality sym p ->
  Maybe (Goals (Assumption sym) (Assertion sym, ProofResult (Either (Assumption sym) (Assertion sym)))) ->
  IO (Maybe (ProvedGoals (Either AssumptionReason SimError)))
provedGoalsTree ctxt = traverse (go [])
  where
  go asmps gs =
    case gs of
      Assuming ps gs1 -> goAsmp asmps ps gs1

      Prove (p,r) -> return $ proveToGoal ctxt asmps p r

      ProveConj g1 g2 -> Branch <$> go asmps g1 <*> go asmps g2

  goAsmp asmps Seq.Empty gs = go asmps gs
  goAsmp asmps (ps Seq.:|> p) gs =
        case p ^. labeledPredMsg of
          ExploringAPath from to -> AtLoc from to <$> goAsmp (p : asmps) ps gs
          _                      -> goAsmp (p : asmps) ps gs


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1  -> countGoals gs1
    Prove _         -> 1
    ProveConj g1 g2 -> countGoals g1 + countGoals g2

countTotalGoals :: ProvedGoals a -> Int
countTotalGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countTotalGoals gs1
    Branch gs1 gs2 -> countTotalGoals gs1 + countTotalGoals gs2
    Goal _ _ _ _ -> 1

countDisprovedGoals :: ProvedGoals a -> Int
countDisprovedGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countDisprovedGoals gs1
    Branch gs1 gs2 -> countDisprovedGoals gs1 + countDisprovedGoals gs2
    Goal _ _ _ (NotProved _ (Just _)) -> 1
    Goal _ _ _ (NotProved _ Nothing) -> 0
    Goal _ _ _ (Proved _) -> 0

countUnknownGoals :: ProvedGoals a -> Int
countUnknownGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countUnknownGoals gs1
    Branch gs1 gs2 -> countUnknownGoals gs1 + countUnknownGoals gs2
    Goal _ _ _ (NotProved _ Nothing) -> 1
    Goal _ _ _ (NotProved _ (Just _)) -> 0
    Goal _ _ _ (Proved _) -> 0

countProvedGoals :: ProvedGoals a -> Int
countProvedGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countProvedGoals gs1
    Branch gs1 gs2 -> countProvedGoals gs1 + countProvedGoals gs2
    Goal _ _ _ (NotProved _ _) -> 0
    Goal _ _ _ (Proved _) -> 1

countIncompleteGoals :: ProvedGoals a -> Int
countIncompleteGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countIncompleteGoals gs1
    Branch gs1 gs2 -> countIncompleteGoals gs1 + countIncompleteGoals gs2
    Goal _ (SimError _ (ResourceExhausted _), _) _ (NotProved _ Nothing) -> 1
    Goal _ _ _ _ -> 0


proveToGoal ::
  (IsSymInterface sym) =>
  SimCtxt personality sym p ->
  [Assumption sym] ->
  Assertion sym ->
  ProofResult (Either (Assumption sym) (Assertion sym)) ->
  ProvedGoals (Either AssumptionReason SimError)
proveToGoal _ allAsmps p pr =
  case pr of
    NotProved ex cex -> Goal (map showLabPred allAsmps) (showLabPred p) False (NotProved ex cex)
    Proved xs ->
      let xs' = map (either (Left . (view labeledPredMsg)) (Right . (view labeledPredMsg))) xs in
      case partitionEithers xs of
        (asmps, [])  -> Goal (map showLabPred asmps) (showLabPred p) True (Proved xs')
        (asmps, _:_) -> Goal (map showLabPred asmps) (showLabPred p) False (Proved xs')

 where
 showLabPred x = (x^.labeledPredMsg, show (printSymExpr (x^.labeledPred)))


isResourceExhausted :: LabeledPred p SimError -> Bool
isResourceExhausted (view labeledPredMsg -> SimError _ (ResourceExhausted _)) = True
isResourceExhausted _ = False

updateProcessedGoals ::
  LabeledPred p SimError ->
  ProofResult a ->
  ProcessedGoals ->
  ProcessedGoals
updateProcessedGoals _ (Proved _) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , provedGoals = 1 + provedGoals pgs
     }

updateProcessedGoals res (NotProved _ _) pgs | isResourceExhausted res =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , incompleteGoals = 1 + incompleteGoals pgs
     }

updateProcessedGoals _ (NotProved _ (Just _)) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , disprovedGoals = 1 + disprovedGoals pgs
     }

updateProcessedGoals _ (NotProved _ Nothing) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs }

-- | Discharge a tree of proof obligations ('Goals') by using a non-online solver
--
-- This function traverses the 'Goals' tree while keeping track of a collection
-- of assumptions in scope for each goal.  For each proof goal encountered in
-- the tree, it creates a fresh solver connection using the provided solver
-- adapter.
--
-- This is in contrast to 'proveGoalsOnline', which uses an online solver
-- connection with scoped assumption frames.  This function allows using a wider
-- variety of solvers (i.e., ones that don't have support for online solving)
-- and would in principle enable parallel goal evaluation (though the tree
-- structure makes that a bit trickier, it isn't too hard).
--
-- Note that this function uses the same symbolic backend ('ExprBuilder') as the
-- symbolic execution phase, which should not be a problem.
proveGoalsOffline :: forall st sym p asmp t fs personality
                   . (?outputConfig :: OutputConfig, sym ~ ExprBuilder t st fs, HasModel personality)
                  => [WS.SolverAdapter st]
                  -> CruxOptions
                  -> SimCtxt personality sym p
                  -> (Maybe (GroundEvalFn t) -> LPred sym SimError -> IO (Doc Void))
                  -> Maybe (Goals (LPred sym asmp) (LPred sym SimError))
                  -> IO (ProcessedGoals, Maybe (Goals (LPred sym asmp) (LPred sym SimError, ProofResult (Either (LPred sym asmp) (LPred sym SimError)))))
proveGoalsOffline _adapter _opts _ctx _explainFailure Nothing = return (ProcessedGoals 0 0 0 0, Nothing)
proveGoalsOffline adapters opts ctx explainFailure (Just gs0) = do
  goalNum <- newIORef (ProcessedGoals 0 0 0 0)
  (start,end,finish) <-
     if view quiet ?outputConfig then
       return (\_ -> return (), return (), return ())
     else
       prepStatus "Checking: " (countGoals gs0)
  gs <- go (start,end) goalNum [] gs0
  nms <- readIORef goalNum
  finish
  return (nms, Just gs)

  where
    failfast = proofGoalsFailFast opts

    go :: (Integer -> IO (), IO ())
       -> IORef ProcessedGoals
       -> [Seq.Seq (LPred sym asmp)]
       -> Goals (LPred sym asmp) (LPred sym SimError)
       -> IO (Goals (LPred sym asmp) (LPred sym SimError, ProofResult (Either (LPred sym asmp) (LPred sym SimError))))
    go (start,end) goalNum assumptionsInScope gs =
      case gs of
        Assuming ps gs1 -> do
          res <- go (start,end) goalNum (ps : assumptionsInScope) gs1
          return (Assuming ps res)

        ProveConj g1 g2 -> do
          g1' <- go (start,end) goalNum assumptionsInScope g1
          numDisproved <- disprovedGoals <$> readIORef goalNum
          if failfast && numDisproved > 0
            then return g1'
            else ProveConj g1' <$> go (start,end) goalNum assumptionsInScope g2

        Prove p -> do
          start . totalProcessedGoals =<< readIORef goalNum

          -- Conjoin all of the in-scope assumptions, the goal, then negate and
          -- check sat with the adapter
          let sym = ctx ^. ctxSymInterface
          assumptions <- WI.andAllOf sym (L.folded . id) (fmap (^. labeledPred) (mconcat assumptionsInScope))
          goal <- notPred sym (p ^. labeledPred)

          res <- dispatchSolversOnGoalAsync (goalTimeout opts) adapters $ runOneSolver p assumptionsInScope assumptions goal
          end
          case res of
            Right details -> do
              modifyIORef' goalNum (updateProcessedGoals p details)
              case details of
                NotProved _ (Just _) ->
                  when (failfast && not (isResourceExhausted p)) $
                    sayOK "Crux" "Counterexample found, skipping remaining goals"
                _                  -> return ()
              return (Prove (p, details))
            Left es -> do
              modifyIORef' goalNum (updateProcessedGoals p (NotProved mempty Nothing))
              let allExceptions = unlines (displayException <$> es)
              fail allExceptions

    runOneSolver :: LPred sym SimError
                 -> [Seq.Seq (LPred sym asmp)]
                 -> BoolExpr t
                 -> BoolExpr t
                 -> WS.SolverAdapter st
                 -> IO (ProofResult (Either (LPred sym asmp) a))
    runOneSolver p assumptionsInScope assumptions goal adapter = do
      -- NOTE: We don't currently provide a method for capturing the output
      -- sent to offline solvers.  We would probably want a file per goal per adapter.
      let logData = WS.defaultLogData
      WS.solver_adapter_check_sat adapter (ctx ^. ctxSymInterface) logData [assumptions, goal] $ \satRes ->
        case satRes of
          Unsat _ -> do
            -- NOTE: We don't have an easy way to get an unsat core here
            -- because we don't have a solver connection.
            let core = fmap Left (F.toList (mconcat assumptionsInScope))
            return (Proved core)
          Sat (evalFn, _) -> do
            let model = ctx ^. cruciblePersonality . personalityModel
            vals <- evalModel evalFn model
            explain <- explainFailure (Just evalFn) p
            return (NotProved explain (Just (ModelView vals)))
          Unknown -> do
            explain <- explainFailure Nothing p
            return (NotProved explain Nothing)

dispatchSolversOnGoalAsync :: forall a s time.
                              (RealFrac time)
                           => Maybe time
                           -> [WS.SolverAdapter s]
                           -> (WS.SolverAdapter s -> IO (ProofResult a))
                           -> IO (Either [SomeException] (ProofResult a))
dispatchSolversOnGoalAsync mtimeoutSeconds adapters withAdapter = do
  asyncs <- forM adapters (async . withAdapter)
  await asyncs []
  where
    await [] es = return $ Left es
    await as es = do
      mresult <- withTimeout $ waitAnyCatch as
      case mresult of
        Just (a, result) -> do
          let as' = filter (/= a) as
          case result of
            Left  exc ->
              await as' (exc : es)
            Right r@(Proved _) -> do
              mapM_ kill as'
              return $ Right r
            Right r@(NotProved _ (Just _)) -> do
              mapM_ kill as'
              return $ Right r
            Right _ ->
              await as' es
        Nothing -> do
          mapM_ kill as
          return $ Right $ NotProved (pretty "(Timeout)") Nothing

    withTimeout action
      | Just seconds <- mtimeoutSeconds = ST.timeout (round seconds * 1000000) action
      | otherwise = Just <$> action

    -- `cancel` from async blocks until the canceled thread has terminated.
    kill a = throwTo (asyncThreadId a) ExitSuccess


-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
--
-- NOTE: This function takes an explicit symbolic backend as an argument, even
-- though the symbolic backend used for symbolic execution is available in the
-- 'SimCtxt'.  We do that so that we can use separate solvers for path
-- satisfiability checking and goal discharge.
proveGoalsOnline ::
  ( sym ~ OnlineBackend s solver fs
  , ast ~ SimError
  , OnlineSolver solver
  , goalSym ~ OnlineBackend s goalSolver fs
  , OnlineSolver goalSolver
  , HasModel personality
  , ?outputConfig :: OutputConfig
  ) =>
  goalSym ->
  CruxOptions ->
  SimCtxt personality sym p ->
  (Maybe (GroundEvalFn s) -> LPred sym ast -> IO (Doc Void)) ->
  Maybe (Goals (LPred sym asmp) (LPred sym ast)) ->
  IO (ProcessedGoals, Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast)))))

proveGoalsOnline _ _opts _ctxt _explainFailure Nothing =
     return (ProcessedGoals 0 0 0 0, Nothing)

proveGoalsOnline sym opts ctxt explainFailure (Just gs0) =
  do goalNum <- newIORef (ProcessedGoals 0 0 0 0)
     nameMap <- newIORef Map.empty
     when (unsatCores opts && yicesMCSat opts) $
       sayWarn "Crux" "Warning: skipping unsat cores because MC-SAT is enabled."
     (start,end,finish) <-
       if view quiet ?outputConfig then
         return (\_ -> return (), return (), return ())
       else
         prepStatus "Checking: " (countGoals gs0)

     -- make sure online features are enabled
     enableOpt <- getOptionSetting enableOnlineBackend (getConfiguration sym)
     _ <- setOpt enableOpt True

     res <- withSolverProcess sym (panic "proveGoalsOnline" ["Online solving not enabled!"]) $ \sp ->
              inNewFrame sp (go (start,end) sp goalNum gs0 nameMap)
     nms <- readIORef goalNum
     finish
     return (nms, Just res)
  where

  bindName nm p nameMap = modifyIORef nameMap (Map.insert nm p)

  hasUnsatCores = unsatCores opts && not (yicesMCSat opts)

  failfast = proofGoalsFailFast opts

  go (start,end) sp gn gs nameMap = do
    case gs of

      Assuming ps gs1 ->
        do forM_ ps $ \p ->
             unless (asConstantPred (p^.labeledPred) == Just True) $
              do nm <- doAssume =<< mkFormula conn (p ^. labeledPred)
                 bindName nm (Left p) nameMap
           res <- go (start,end) sp gn gs1 nameMap
           return (Assuming ps res)

      Prove p ->
        do start . totalProcessedGoals =<< readIORef gn
           nm <- doAssume =<< mkFormula conn =<< notPred sym (p ^. labeledPred)
           bindName nm (Right p) nameMap

           res <- check sp "proof"
           ret <- case res of
                      Unsat () ->
                        do namemap <- readIORef nameMap
                           core <- if hasUnsatCores
                                   then map (lookupnm namemap) <$> getUnsatCore sp
                                   else return (Map.elems namemap)
                           end
                           modifyIORef' gn (updateProcessedGoals p (Proved core))
                           return (Prove (p, (Proved core)))

                      Sat ()  ->
                        do f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality . personalityModel
                           vals <- evalModel f model
                           explain <- explainFailure (Just f) p
                           end
                           let gt = NotProved explain (Just (ModelView vals))
                           modifyIORef' gn (updateProcessedGoals p gt)
                           when (failfast && not (isResourceExhausted p)) $
                             (sayOK "Crux" "Counterexample found, skipping remaining goals.")
                           return (Prove (p, gt))
                      Unknown ->
                        do explain <- explainFailure Nothing p
                           end
                           let gt = NotProved explain Nothing
                           modifyIORef' gn (updateProcessedGoals p gt)
                           return (Prove (p, gt))
           return ret

      ProveConj g1 g2 ->
        do g1' <- inNewFrame sp (go (start,end) sp gn g1 nameMap)

           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.
           if failfast then
             do numDisproved <- disprovedGoals <$> readIORef gn
                if numDisproved > 0 then
                  return g1'
                else
                  ProveConj g1' <$> go (start,end) sp gn g2 nameMap
           else
             ProveConj g1' <$> go (start,end) sp gn g2 nameMap

    where
    conn = solverConn sp

    lookupnm namemap x =
      fromMaybe (error $ "Named predicate " ++ show x ++ " not found!")
                (Map.lookup x namemap)

    doAssume formula = do
      namemap <- readIORef nameMap
      if hasUnsatCores
      then assumeFormulaWithFreshName conn formula
      else assumeFormula conn formula >> return (Text.pack ("x" ++ show (Map.size namemap)))
