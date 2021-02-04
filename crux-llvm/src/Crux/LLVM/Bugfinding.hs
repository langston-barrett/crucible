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
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Bugfinding (bugfindingLoop) where

import System.Exit
  ( ExitCode(..) )

import Data.Foldable (for_)
import qualified Data.Text.IO as TextIO
import Data.String (fromString)
import qualified Data.Map.Strict as Map
import Data.IORef
import Control.Lens ((^.), view)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)

import System.FilePath( (</>) )

import qualified Text.LLVM.AST as L

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
import Lang.Crucible.LLVM.MemModel
        ( withPtrWidth, LLVMAnnMap
        , explainCex, CexExplanation(..)
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule
        , transContext, cfgMap
        , ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )

import Lang.Crucible.LLVM.Extension( LLVM )
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

-- crux
import qualified Crux

import Crux.Log
import Crux.Config.Common

 -- local
import Crux.LLVM.Config
import Crux.LLVM.Overrides
import Crux.LLVM.Simulate (parseLLVM, setupSimCtxt, registerFunctions)
import Crux.LLVM.Bugfinding.Classify (classify, Explanation, ppExplanation)
import Crux.LLVM.Bugfinding.Constraints (emptyConstraints, Constraints(..))
import Crux.LLVM.Bugfinding.Setup (setupExecution)

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
  L.Module ->
  LLVMTrans.ModuleTranslation arch ->
  IORef [Explanation] ->
  Constraints init ->
  CFG (LLVM arch) blocks init ret ->
  LLVMOptions ->
  Crux.SimulatorCallback
simulateLLVM halloc llvmMod trans explanationRef preconds cfg llvmOpts =
  Crux.SimulatorCallback $ \sym _maybeOnline ->
    do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ?ptrWidth]
       let llvmCtxt = trans ^. transContext
       bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
       let ?lc = llvmCtxt^.llvmTypeCtx
       let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
       let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt)
                      { printHandle = view outputHandle ?outputConfig }

       setupResult <-
         liftIO $ setupExecution sym llvmMod trans preconds (cfgArgTypes cfg)
       (args, mem) <-
         case setupResult of
           Left err -> error "BLAH ERROR!"
           Right tup -> pure tup
       let globSt = llvmGlobals llvmCtxt mem
       let initSt =
             InitialState simctx globSt defaultAbortHandler CrucibleTypes.UnitRepr $
               runOverrideSim CrucibleTypes.UnitRepr $
                 do -- TODO(lb): Do this lazily
                    registerFunctions llvmMod trans
                    void $ callCFG cfg args

       let explainFailure evalFn gl =
             do bb <- readIORef bbMapRef
                ex <- explainCex sym bb evalFn >>= \f -> f (gl ^. Crucible.labeledPred)
                case ex of
                  NoExplanation -> pure ()
                  DisjOfFailures bbs ->
                    writeIORef explanationRef
                      =<< mapM (classify sym args) bbs
                return mempty

       return (Crux.RunnableState initSt, explainFailure)

-- | The outer loop of bugfinding mode
bugfindingLoop ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO ExitCode
bugfindingLoop cruxOpts llvmOpts =
  do
     -- First translate the LLVM module into Crucible
     llvmMod <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
     halloc <- newHandleAllocator
     Some trans <-
       let ?laxArith = laxArithmetic llvmOpts
           ?optLoopMerge = loopMerge llvmOpts
       in translateModule halloc llvmMod
     llvmPtrWidth (trans ^. transContext) $
       \ptrW -> withPtrWidth ptrW $
         do AnyCFG cfg <- liftIO $ findFun (entryPoint llvmOpts) (cfgMap trans)
            explanationRef <- newIORef []
            let runSim preconds =
                  Crux.runSimulator
                    cruxOpts
                    (simulateLLVM halloc llvmMod trans explanationRef preconds cfg llvmOpts)
            -- Execute the function with no preconditions
            runSim (emptyConstraints (Ctx.size (cfgArgTypes cfg)))
            -- Loop, learning preconditions and reporting errors
            explanations <- readIORef explanationRef
            case explanations of
              [] ->
                do say "Crux" "No errors"
                  -- TODO(lb): Increase depth till max
              es ->
                do say "Crux" "Errors!"
                   for_ es $ \explanation ->
                     say "Crux" (show (ppExplanation explanation))
                   -- TODO(lb): Apply heuristics, report errors or try again
            return ExitSuccess
