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
  , BugfindingResult(..)
  ) where

import System.Exit
  ( ExitCode(..) )

import Data.String (fromString)
import Data.Foldable (for_)
import qualified Data.Map.Strict as Map
import Data.IORef
import Control.Lens ((^.), view)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)
import qualified Data.Text.IO as TextIO

import System.FilePath( (</>) )

import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.Context as Ctx

import Lumberjack as LJ

-- crucible
import Lang.Crucible.CFG.Core (CFG, AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle (HandleAllocator, newHandleAllocator)
import Lang.Crucible.Simulator
  ( runOverrideSim, callCFG
  , ExecState( InitialState )
  , defaultAbortHandler, printHandle
  )
import qualified Lang.Crucible.Backend as Crucible
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

import Crux.LLVM.Bugfinding.Classify (TruePositive, classify, Explanation(..), ppTruePositive)
import Crux.LLVM.Bugfinding.Constraints (isEmpty, ppConstraints, emptyConstraints, Constraints(..))
import Crux.LLVM.Bugfinding.Context
import Crux.LLVM.Bugfinding.Setup (logRegMap, setupExecution, SetupResult(SetupResult), SetupAssumption(SetupAssumption))

import qualified What4.Interface as What4
import qualified Data.Text as Text
import qualified What4.ProgramLoc as What4
import qualified What4.FunctionName as What4
import Data.List.NonEmpty (NonEmpty((:|)))

class MonadIO m => HasIOLog m

instance HasIOLog IO

instance HasIOLog m => LJ.HasLog Text m where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

findFun ::
  (ArchOk arch, Logs) =>
  String -> ModuleCFGMap arch -> IO (AnyCFG (LLVM arch))
findFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, anyCfg) -> pure anyCfg
    Nothing -> throwCError (MissingFun nm)

simulateLLVM ::
  ArchOk arch =>
  HandleAllocator ->
  Context arch argTypes ->
  IORef [TruePositive] ->
  IORef (Constraints argTypes) ->
  Constraints argTypes ->
  CFG (LLVM arch) blocks argTypes ret ->
  MemOptions ->
  Crux.SimulatorCallback
simulateLLVM halloc context truePositiveRef constraintsRef preconds cfg memOptions =
  Crux.SimulatorCallback $ \sym _maybeOnline ->
    do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ?ptrWidth]
       let trans = context ^. moduleTranslation
       let llvmCtxt = trans ^. transContext
       bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
       let ?lc = llvmCtxt^.llvmTypeCtx
       let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
       let simctx = (setupSimCtxt halloc sym memOptions llvmCtxt)
                      { printHandle = view outputHandle ?outputConfig }

       setupResult <-
         liftIO $ setupExecution sym context preconds
       (mem, argAnnotations, assumptions, args) <-
         case setupResult of
           Left _err -> error "BLAH ERROR!"
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
             InitialState simctx globSt defaultAbortHandler CrucibleTypes.UnitRepr $
               runOverrideSim CrucibleTypes.UnitRepr $
                 do -- TODO(lb): Do this lazily
                    registerFunctions (context ^. llvmModule) trans
                    liftIO $ writeLogM ("Running function on arguments..." :: Text)
                    liftIO $ logRegMap context sym mem args
                    void $ callCFG cfg args

       -- Diagnose errors and write back the results so they can be read in the
       -- outer loop
       let explainFailure _ gl =
             do bb <- readIORef bbMapRef
                case flip Map.lookup bb . BoolAnn =<<
                       What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
                  Nothing -> pure ()  -- TODO(lb)
                  Just badBehavior ->
                    classify context sym args argAnnotations badBehavior >>=
                      \case
                        ExTruePositive pos -> modifyIORef truePositiveRef (pos:)
                        ExMissingPreconditions constraints ->
                          modifyIORef constraintsRef (constraints <>)
                return mempty

       return (Crux.RunnableState initSt, explainFailure)

-- | The outer loop of bugfinding mode

data BugfindingResult argTypes
  = FoundBugs (NonEmpty TruePositive)
  | SafeWithPreconditions (Constraints argTypes)
  | AlwaysSafe

printBugfindingResult :: BugfindingResult argTypes -> Text
printBugfindingResult =
  \case
    FoundBugs bugs ->
      "There might be bugs in this function"
      <> foldMap ppTruePositive bugs
    SafeWithPreconditions preconditions ->
      "This function is safe assuming the following preconditions are met:\n"
      <> Text.pack (show (ppConstraints preconditions))
    AlwaysSafe -> "This function is always safe."

makeBugfindingResult :: Constraints argTypes -> [TruePositive] -> BugfindingResult argTypes
makeBugfindingResult preconditions truePositives =
  case (isEmpty preconditions, truePositives) of
    (True, []) -> AlwaysSafe
    (False, []) -> SafeWithPreconditions preconditions
    (_, t:ts) -> FoundBugs (t :| ts)

bugfindingLoop ::
  ( ?outputConfig ::  OutputConfig
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  CFG (LLVM arch) blocks argTypes ret ->
  CruxOptions ->
  MemOptions ->
  HandleAllocator ->
  IO (BugfindingResult argTypes)
bugfindingLoop context cfg cruxOpts memOptions halloc =
  do -- First translate the LLVM module into Crucible
     let emptyCs = emptyConstraints (Ctx.size (cfgArgTypes cfg))
     truePositiveRef <- newIORef []
     constraintsRef <- newIORef emptyCs

     let runSim preconds =
           Crux.runSimulator
             cruxOpts
             (simulateLLVM
                halloc
                context
                truePositiveRef
                constraintsRef
                preconds
                cfg
                memOptions)

     -- Loop, learning preconditions and reporting errors
     let loop truePositives preconditions =
           do writeIORef truePositiveRef []
              writeIORef constraintsRef emptyCs
              runSim preconditions
              newTruePositives <- readIORef truePositiveRef
              newConstraints <- readIORef constraintsRef
              let result = makeBugfindingResult preconditions truePositives
              case (isEmpty newConstraints, newTruePositives) of
                (True, []) ->
                  do say "Crux" "No errors!"
                     -- TODO(lb): Increase depth till max
                     pure result
                (isEmpty_, _) ->
                  do for_ newTruePositives
                          (\pos ->
                             do say "Crux" "TRUE (?) POSITIVE!"
                                say "Crux" (Text.unpack (ppTruePositive pos)))
                     if isEmpty_
                     then pure result
                     else
                       do say "Crux" "New preconditions:"
                          say "Crux" (show (ppConstraints newConstraints))
                          loop
                            (truePositives <> newTruePositives)
                            (preconditions <> newConstraints)

     loop [] (emptyConstraints (Ctx.size (cfgArgTypes cfg)))


-- | Assumes the bitcode file has already been generated with @genBitCode@.
translateAndLoop ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO (Some BugfindingResult)
translateAndLoop cruxOpts llvmOpts =
  do llvmMod <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
     halloc <- newHandleAllocator
     Some trans <-
       let ?laxArith = laxArithmetic llvmOpts
           ?optLoopMerge = loopMerge llvmOpts
       in translateModule halloc llvmMod
     let entry = entryPoint llvmOpts
     llvmPtrWidth (trans ^. transContext)
       (\ptrW ->
          withPtrWidth
            ptrW
            (do AnyCFG cfg <- liftIO $ findFun entry (cfgMap trans)
                let context =
                      case makeContext (Text.pack entry) (cfgArgTypes cfg) llvmMod trans of
                        Left _ -> error "Error building context!"  -- TODO(lb)
                        Right c -> c
                Some <$>
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
  do Some result <- translateAndLoop cruxOpts llvmOpts
     TextIO.putStrLn (printBugfindingResult result)
     return ExitSuccess