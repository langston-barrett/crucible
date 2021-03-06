{- |
Module           : Cruces.ExploreCrux
Description      : Wrappers for driving Crucibles with Crux
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Cruces.ExploreCrux where

import           Control.Monad.IO.Class
import           Control.Monad (when)
import           Control.Lens
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map
import           System.IO (Handle)

import           What4.Interface
import           What4.Config

import           Data.Parameterized.Pair(Pair)
import qualified Data.Parameterized.Context as Ctx
import           Lang.Crucible.FunctionHandle (HandleAllocator)
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.Simulator
import           Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import           Lang.Crucible.Backend

import qualified Crux
import           Crux.Model

import           Crucibles.SchedulingAlgorithm hiding (_exec, exec)
import           Crucibles.Execution
import           Crucibles.ExploreTypes
import           Crucibles.Primitives
import           Crucibles.Explore
import           Crucibles.Scheduler
import           Crucibles.Common

import           Crux.Goal (proveGoalsOnline)
import           Crux.Types (totalProcessedGoals, provedGoals)

-- | Callback for crucible-syntax exploration
exploreCallback :: forall alg.
  (?bound::Int, SchedulingAlgorithm alg) =>
  Crux.CruxOptions ->
  HandleAllocator ->
  Handle ->
  (forall s.
   (IsSymInterface s) =>
   s -> IO ( FnVal s Ctx.EmptyCtx C.UnitType
           , ExplorePrimitives (ThreadExec alg s () C.UnitType) s ()
           , [Pair C.TypeRepr C.GlobalVar]
           , FunctionBindings (ThreadExec alg s () C.UnitType) s ())
           ) ->
  Crux.SimulatorCallback
exploreCallback cruxOpts ha outh mkSym =
  Crux.SimulatorCallback $ \sym symOnline -> do
    (mainHdl, prims, globs, fns) <- mkSym sym
    let simCtx = initSimContext sym emptyIntrinsicTypes ha outh fns emptyExtensionImpl emptyExploration

        st0  = InitialState simCtx emptyGlobals defaultAbortHandler C.UnitRepr $
                   runOverrideSim C.UnitRepr (exploreOvr symOnline cruxOpts (regValue <$> callFnVal mainHdl emptyRegMap))

        feats = [scheduleFeature prims globs]

    return (Crux.RunnableStateWithExtensions st0 feats, \_ _ -> return mempty)

-- | Empty exploration state
emptyExploration :: SchedulingAlgorithm alg => Exploration alg ext C.UnitType sym
emptyExploration = Exploration { _exec      = initialExecutions
                               , _scheduler = s0
                               , _schedAlg  = initialAlgState
                               , _model     = emptyModel
                               , _num       = 0
                               , _gVars     = mempty
                               }
  where
    s0 = Scheduler { _threads      = V.fromList [EmptyThread]
                   , _retRepr      = C.UnitRepr
                   , mainCont      = return ()
                   , _activeThread = 0
                   , _numSwitches  = 0
                   }

-- | Wrap an override to produce a NEW override that will explore the executions of a concurrent program.
-- Must also use the 'scheduleFeature' 'ExecutionFeature'
exploreOvr :: forall sym ext alg ret rtp.
  (?bound::Int, IsSymInterface sym, IsSyntaxExtension ext, SchedulingAlgorithm alg, RegValue sym ret ~ ()) =>
  Maybe (Crux.SomeOnlineSolver sym) ->
  Crux.CruxOptions ->
  (forall rtp'. OverrideSim (Exploration alg ext ret sym) sym ext rtp' Ctx.EmptyCtx ret (RegValue sym ret)) ->
  OverrideSim (Exploration alg ext ret sym) sym ext rtp Ctx.EmptyCtx ret (RegValue sym ret)
exploreOvr symOnline cruxOpts mainAct =
  do sym     <- getSymInterface
     assmSt  <- liftIO $ saveAssumptionState sym
     verbOpt <- liftIO $ getOptionSetting verbosity $ getConfiguration sym
     verb    <- fromInteger <$> (liftIO $ getOpt verbOpt)
     loop verb assmSt

  where
    loop ::
      Int ->
      AssumptionState sym ->
      forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    loop verb assmSt =
      do reset verb assmSt
         exploreAPath
         retH verb assmSt

    checkGoals :: forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret Bool
    checkGoals = case symOnline of
      Just Crux.SomeOnlineSolver ->
        do sym <- getSymInterface
           ctx <- use stateContext
           todo <- liftIO $ getProofObligations sym
           let ?outputConfig = Crux.defaultOutputConfig { Crux._quiet = True }
           let cruxOpts' = cruxOpts { Crux.quietMode = True, Crux.simVerbose = 0 }
           (processed, _) <- liftIO $ proveGoalsOnline sym cruxOpts' ctx (\_ _ -> return mempty) todo
           let provedAll = totalProcessedGoals processed == provedGoals processed
           when provedAll $ liftIO $ clearProofObligations sym
           return provedAll
      Nothing -> return True

    retH :: Int -> AssumptionState sym -> forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    retH verb assmSt =
     do stateExpl.num %= (+1)
        exc          <- use stateExec
        stateExplAlg %= processExecution exc
        alg          <- use stateExplAlg

        when (verb > 2) $
           do liftIO $ putStrLn " == Begin Exploration =="
              liftIO $ putStrLn $ ppExecutions exc alg
              liftIO $ putStrLn " == End Exploration   ==\n"

        let amDone = fullyExplored (exc { _currentEventID = 0 }) alg
        provedAllGoals <- checkGoals

        if amDone || not provedAllGoals then
          return ()
        else
          loop verb assmSt

    exploreAPath :: forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    exploreAPath = mainAct

    reset ::  Int -> AssumptionState sym -> forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    reset verb assmSt =
      do stateExec.currentEventID .= 0
         -- Reset scheduler state
         stateExpl.scheduler.activeThread .= 0
         stateExpl.scheduler.threads      .= V.fromList [EmptyThread]
         stateExpl.scheduler %= \s -> s { mainCont = retH verb assmSt }
         stateExpl.scheduler.numSwitches  .= 0
         -- Per-run exploration bookkeeping
         runUpdateSchedAlg prepareNewExecution
         stateExec.birthdays              .= Map.fromList [(ThreadID 0, 0)]
