{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Crux.LLVM.Bugfinding
  ( bugfindingMain
  , translateAndLoop
  , Result.SomeBugfindingResult(..)
  , Result.FunctionSummary(..)
  , Result.printFunctionSummary
  ) where

import           Control.Lens ((^.), view, to)
import           Control.Monad (void, when)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable (for_)
import           Data.IORef
import           Data.List (isInfixOf)
import           Data.List.NonEmpty (NonEmpty((:|)))
import           Data.String (fromString)
import           Data.Text (Text)
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as TextIO
import           System.Exit (ExitCode(..))
import           System.FilePath( (</>) )

import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.Context as Ctx

import Lumberjack as LJ

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes


-- crucible-llvm
import Lang.Crucible.LLVM( llvmGlobals )
import Lang.Crucible.LLVM.MemModel (MemOptions,  withPtrWidth, LLVMAnnMap )
import Lang.Crucible.LLVM.Translation
        ( translateModule
        , transContext, cfgMap
        , ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )

import Lang.Crucible.LLVM.Errors (ppBB)
import Lang.Crucible.LLVM.MemModel.Partial (BoolAnn(BoolAnn))
import Lang.Crucible.LLVM.Extension( LLVM )

-- crux
import qualified Crux

import Crux.Log
import Crux.Config.Common

 -- local
import Crux.LLVM.Config
import Crux.LLVM.Overrides
import Crux.LLVM.Simulate (parseLLVM, setupSimCtxt, registerFunctions)

import Crux.LLVM.Bugfinding.Classify (partitionExplanations, classifyAssertion, classifyBadBehavior, Explanation(..), ppTruePositive, Uncertainty(..))
import Crux.LLVM.Bugfinding.Constraints (isEmpty, ppConstraints, emptyConstraints, Constraints(..))
import Crux.LLVM.Bugfinding.Context
import Crux.LLVM.Bugfinding.Errors.Panic (panic)
import Crux.LLVM.Bugfinding.FullType (MapToCrucibleType)
import Crux.LLVM.Bugfinding.Setup (logRegMap, setupExecution, SetupResult(SetupResult), SetupAssumption(SetupAssumption))
import Crux.LLVM.Bugfinding.Setup.Monad (ppSetupError)
import           Crux.LLVM.Bugfinding.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified Crux.LLVM.Bugfinding.Result as Result

-- TODO unsorted
import qualified What4.Interface as What4
import qualified Data.Text as Text
import qualified What4.ProgramLoc as What4
import qualified What4.FunctionName as What4
import Prettyprinter (Doc)
import Data.Void (Void)
import Data.Semigroup (Semigroup(sconcat))
import Data.List (intercalate)

class MonadIO m => HasIOLog m

instance HasIOLog IO

instance HasIOLog m => LJ.HasLog Text m where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

findFun ::
  (ArchOk arch, Logs) =>
  String -> ModuleCFGMap arch -> IO (Crucible.AnyCFG (LLVM arch))
findFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, anyCfg) -> pure anyCfg
    Nothing -> throwCError (MissingFun nm)

simulateLLVM ::
  ArchOk arch =>
  Crucible.HandleAllocator ->
  Context m arch argTypes ->
  IORef [Explanation m arch argTypes] ->
  Constraints m arch argTypes ->
  Crucible.CFG (LLVM arch) blocks (MapToCrucibleType arch argTypes) ret ->
  MemOptions ->
  Crux.SimulatorCallback
simulateLLVM halloc context explRef preconds cfg memOptions =
  Crux.SimulatorCallback $ \sym _maybeOnline ->
    do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ?ptrWidth]
       let trans = context ^. moduleTranslation
       let llvmCtxt = trans ^. transContext
       bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
       let ?lc = llvmCtxt^.llvmTypeCtx
       let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
       let simctx = (setupSimCtxt halloc sym memOptions llvmCtxt)
                      { Crucible.printHandle = view outputHandle ?outputConfig }

       setupResult <-
         liftIO $ setupExecution sym context preconds
       (mem, argAnnotations, assumptions, args) <-
         case setupResult of
           Left err -> panic "setupExecution" [show (ppSetupError err)]
           Right (SetupResult mem anns assumptions, args) ->
             pure (mem, anns, assumptions, args)

       -- Assume all predicates necessary to satisfy the deduced preconditions
       for_ assumptions
            (\(SetupAssumption _constraint predicate) ->
              liftIO $
                Crucible.addAssumption
                  sym
                  (Crucible.LabeledPred
                     predicate
                     (Crucible.AssumptionReason
                        (What4.mkProgramLoc
                           (What4.functionNameFromText (context ^. functionName))
                           What4.InternalPos)
                        "constraint")))

       let globSt = llvmGlobals llvmCtxt mem
       let initSt =
             Crucible.InitialState simctx globSt Crucible.defaultAbortHandler CrucibleTypes.UnitRepr $
               Crucible.runOverrideSim CrucibleTypes.UnitRepr $
                 do -- TODO(lb): Do this lazily
                    registerFunctions (context ^. llvmModule) trans
                    liftIO $ writeLogM ("Running " <> context ^. functionName <> " on arguments..." :: Text)
                    liftIO $ logRegMap context sym mem args
                    void $ Crucible.callCFG cfg args

       -- Diagnose errors and write back the results so they can be read in the
       -- outer loop
       let explainFailure _ gl =
             do bb <- readIORef bbMapRef
                case flip Map.lookup bb . BoolAnn =<<
                       What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
                  Nothing ->
                    case What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
                      Just ann ->
                        panic "simulateLLVM" ["Unexplained error: no error for annotation."]
                      Nothing ->
                        modifyIORef explRef . (:) $
                          case gl ^. Crucible.labeledPredMsg . to Crucible.simErrorReason of
                            Crucible.ResourceExhausted msg ->
                              ExExhaustedBounds msg
                            Crucible.AssertFailureSimError msg _ ->
                              if "Call to assert" `isInfixOf` msg  -- HACK
                              then
                                classifyAssertion
                                  sym
                                  (gl ^. Crucible.labeledPred)
                                  (gl ^. Crucible.labeledPredMsg . to Crucible.simErrorLoc)
                              else ExUncertain (UMissingAnnotation  (gl ^. Crucible.labeledPredMsg))
                            _ -> ExUncertain (UMissingAnnotation (gl ^. Crucible.labeledPredMsg))
                  Just badBehavior ->
                    do -- Helpful for debugging:
                       -- putStrLn "~~~~~~~~~~~"
                       -- putStrLn (show (ppBB badBehavior))
                       classifyBadBehavior context sym args argAnnotations badBehavior >>=
                         modifyIORef explRef . (:)
                return mempty

       return (Crux.RunnableState initSt, explainFailure)

runSimulator ::
  ( ?outputConfig ::  OutputConfig
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  Crucible.HandleAllocator ->
  Constraints m arch argTypes ->
  Crucible.CFG (LLVM arch) blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  MemOptions ->
  IO [Explanation m arch argTypes]
runSimulator context halloc preconditions cfg cruxOpts memOptions =
  do explRef <- newIORef []
     void $
      Crux.runSimulator
        cruxOpts
        (simulateLLVM
          halloc
          context
          explRef
          preconditions
          cfg
          memOptions)
     readIORef explRef

-- | The outer loop of bugfinding mode


bugfindingLoop ::
  ( ?outputConfig ::  OutputConfig
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  Crucible.CFG (LLVM arch) blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  MemOptions ->
  Crucible.HandleAllocator ->
  IO (BugfindingResult m arch argTypes)
bugfindingLoop context cfg cruxOpts memOptions halloc =
  do let emptyCs = emptyConstraints (Ctx.size (context ^. argumentFullTypes))
     let runSim preconds =
           runSimulator context halloc preconds cfg cruxOpts memOptions

     -- Loop, learning preconditions and reporting errors
     let loop truePositives preconditions uncertain resourceExhausted =
           do -- TODO(lb) We basically ignore symbolic assertion failures. Maybe
              -- configurably don't?
              (newTruePositives, newConstraints0, newUncertain, newResourceExhausted) <-
                partitionExplanations <$> runSim preconditions
              let newConstraints = sconcat (emptyCs :| newConstraints0)
              let allTruePositives = truePositives <> newTruePositives
              let allPreconditions = preconditions <> newConstraints
              let allUncertain = uncertain <> newUncertain
              let allResourceExhausted = resourceExhausted <> newResourceExhausted
              let result =
                    BugfindingResult
                      allUncertain
                      (Result.makeFunctionSummary
                         allPreconditions
                         allUncertain
                         allTruePositives
                         (not (null allResourceExhausted)))
              case (isEmpty newConstraints, newTruePositives, not (null newUncertain), not (null newResourceExhausted)) of
                (True, [], False, _) -> pure result
                (noNewConstraints, _, isUncertain, isExhausted) ->
                  do for_ newTruePositives
                          (\pos ->
                             do say "Crux" "TRUE (?) POSITIVE!"
                                say "Crux" (Text.unpack (ppTruePositive pos)))
                     if noNewConstraints || isUncertain || isExhausted
                     then pure result  -- We can't really go on
                     else
                       do say "Crux" "New preconditions:"
                          say "Crux" (show (ppConstraints newConstraints))
                          when (allPreconditions == preconditions) $
                            panic "bugfindingLoop" ["Redundant constraints!"]
                          loop allTruePositives allPreconditions allUncertain allResourceExhausted

     loop [] (emptyConstraints (Ctx.size (context ^. argumentFullTypes))) [] []


-- | Assumes the bitcode file has already been generated with @genBitCode@.
translateAndLoop ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO SomeBugfindingResult
translateAndLoop cruxOpts llvmOpts =
  do llvmMod <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
     halloc <- Crucible.newHandleAllocator
     Some trans <-
       let ?laxArith = laxArithmetic llvmOpts
           ?optLoopMerge = loopMerge llvmOpts
       in translateModule halloc llvmMod
     let entry = entryPoint llvmOpts
     llvmPtrWidth (trans ^. transContext)
       (\ptrW ->
          withPtrWidth
            ptrW
            (do Crucible.AnyCFG cfg <- liftIO $ findFun entry (cfgMap trans)
                case makeContext (Text.pack entry) (Crucible.cfgArgTypes cfg) llvmMod trans of
                  Left _ -> error "Error building context!"  -- TODO(lb)
                  Right (SomeContext context Refl) ->
                    SomeBugfindingResult <$>
                      bugfindingLoop
                        context
                        cfg
                        cruxOpts
                        (memOpts llvmOpts)
                        halloc))


-- | Assumes the bitcode file has already been generated with @genBitCode@.
bugfindingMain ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO ExitCode
bugfindingMain cruxOpts llvmOpts =
  do SomeBugfindingResult result <- translateAndLoop cruxOpts llvmOpts
     say "Crux" $ Text.unpack (Result.printFunctionSummary (summary result))
     return ExitSuccess
