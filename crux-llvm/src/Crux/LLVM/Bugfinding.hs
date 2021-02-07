{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Crux.LLVM.Bugfinding (bugfindingLoop) where

import System.Exit
  ( ExitCode(..) )

import qualified Data.Text.IO as TextIO
import Data.String (fromString)
import qualified Data.Map.Strict as Map
import Data.IORef
import Control.Lens ((^.), view)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)

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
import Lang.Crucible.LLVM.MemModel ( withPtrWidth, LLVMAnnMap )
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

import Crux.LLVM.Bugfinding.Classify (classify, Explanation(..), ppExplanation)
import Crux.LLVM.Bugfinding.Constraints (emptyConstraints, Constraints(..))
import Crux.LLVM.Bugfinding.Context
import Crux.LLVM.Bugfinding.Setup (logRegMap, setupExecution)

import qualified What4.Interface as What4
import qualified Data.Text as Text

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
  (ArchOk arch) =>
  HandleAllocator ->
  Context arch argTypes ->
  IORef (Maybe (Explanation argTypes)) ->
  Constraints argTypes ->
  CFG (LLVM arch) blocks argTypes ret ->
  LLVMOptions ->
  Crux.SimulatorCallback
simulateLLVM halloc context explanationRef preconds cfg llvmOpts =
  Crux.SimulatorCallback $ \sym _maybeOnline ->
    do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ?ptrWidth]
       let trans = context ^. moduleTranslation
       let llvmCtxt = trans ^. transContext
       bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
       let ?lc = llvmCtxt^.llvmTypeCtx
       let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
       let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt)
                      { printHandle = view outputHandle ?outputConfig }

       setupResult <-
         liftIO $ setupExecution sym context preconds
       (mem, argAnnotations, args) <-
         case setupResult of
           Left _err -> error "BLAH ERROR!"
           Right tup -> pure tup
       let globSt = llvmGlobals llvmCtxt mem
       let initSt =
             InitialState simctx globSt defaultAbortHandler CrucibleTypes.UnitRepr $
               runOverrideSim CrucibleTypes.UnitRepr $
                 do -- TODO(lb): Do this lazily
                    registerFunctions (context ^. llvmModule) trans
                    liftIO $ writeLogM ("Running function on arguments..." :: Text)
                    liftIO $ logRegMap context sym mem args
                    void $ callCFG cfg args

       let explainFailure _ gl =
             do bb <- readIORef bbMapRef
                case flip Map.lookup bb . BoolAnn =<<
                       What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
                  Nothing -> pure ()
                  Just badBehavior ->
                    writeIORef explanationRef . Just =<<
                      classify sym args argAnnotations badBehavior
                return mempty

       return (Crux.RunnableState initSt, explainFailure)

-- | The outer loop of bugfinding mode

bugfindingLoop ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO ExitCode
bugfindingLoop cruxOpts llvmOpts =
  do -- First translate the LLVM module into Crucible
     llvmMod <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
     halloc <- newHandleAllocator
     Some trans <-
       let ?laxArith = laxArithmetic llvmOpts
           ?optLoopMerge = loopMerge llvmOpts
       in translateModule halloc llvmMod
     let entry = entryPoint llvmOpts
     llvmPtrWidth (trans ^. transContext) $
       \ptrW -> withPtrWidth ptrW $
         do AnyCFG cfg <- liftIO $ findFun entry (cfgMap trans)
            explanationRef <- newIORef Nothing
            let context =
                  case makeContext (Text.pack entry) (cfgArgTypes cfg) llvmMod trans of
                    Left _ -> error "Error building context!"  -- TODO(lb)
                    Right c -> c

            let runSim preconds =
                  Crux.runSimulator
                    cruxOpts
                    (simulateLLVM halloc context explanationRef preconds cfg llvmOpts)

            -- Loop, learning preconditions and reporting errors
            let loop preconditions =
                  do runSim preconditions
                     explanations <- readIORef explanationRef
                     case explanations of
                       Nothing ->
                         do say "Crux" "No errors!"
                           -- TODO(lb): Increase depth till max
                       Just explanation@(ExTruePositive _) ->
                         do say "Crux" (Text.unpack (ppExplanation explanation))
                       Just (ExMissingPreconditions newPreconditions) ->
                         loop (preconditions <> newPreconditions)

            loop (emptyConstraints (Ctx.size (cfgArgTypes cfg)))
            return ExitSuccess
