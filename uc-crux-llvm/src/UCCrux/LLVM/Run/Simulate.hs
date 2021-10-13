{-
Module       : UCCrux.LLVM.Run.Simulate
Description  : Run the simulator once.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
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
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Run.Simulate
  ( UCCruxSimulationResult (..),
    defaultActions,
    registerOverridesPre,
    registerBasicOverridesPre,
    runSimulator,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), view, to)
import           Control.Monad (void, unless)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Reader (ask)
import           Data.Foldable (for_)
import           Data.IORef (IORef)
import qualified Data.IORef as IORef
import           Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Profunctor as Profunctor
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Context (Assignment)
import           Data.Parameterized.Some (Some)

import qualified What4.Expr.Builder as What4
import qualified What4.Interface as What4
import qualified What4.InterpretedFloatingPoint as What4
import qualified What4.ProgramLoc as What4

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM (llvmGlobalsToCtx)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate)
import qualified Lang.Crucible.LLVM.Intrinsics as LLVMIntrinsics
import           Lang.Crucible.LLVM.MemModel (MemImpl, HasLLVMAnn, LLVMAnnMap)
import           Lang.Crucible.LLVM.Translation (transContext, llvmMemVar, llvmTypeCtx)

import           Lang.Crucible.LLVM.MemModel.Partial (BoolAnn(BoolAnn))
import           Lang.Crucible.LLVM.Extension (LLVM)

-- crux
import qualified Crux
import qualified Crux.Types as Crux

import           Crux.Config.Common (CruxOptions)
import           Crux.Log (outputHandle)

 -- crux-llvm
import           Crux.LLVM.Config (LLVMOptions(..))
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Simulate (setupSimCtxt, registerFunctions)

 -- local
import           UCCrux.LLVM.Classify (classifyAssertion, classifyBadBehavior)
import           UCCrux.LLVM.Classify.Types (Located(Located), Explanation(..), Uncertainty(..))
import           UCCrux.LLVM.Constraints (Constraints, returnConstraints, relationalConstraints)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, functionName)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTranslation)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Module (getModule)
import           UCCrux.LLVM.Overrides.Basic (BasicLLVMOverride, getBasicLLVMOverride)
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName, unsoundSkipOverrides)
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName, unsoundOverrides)
import           UCCrux.LLVM.FullType.Type (FullType, MapToCrucibleType)
import           UCCrux.LLVM.PP (ppRegMap)
import qualified UCCrux.LLVM.Run.Simulate.Actions as Actions
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness(Unsoundness))
import           UCCrux.LLVM.Setup (SymValue, setupExecution, SetupResult(SetupResult))
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Setup.Monad (TypedSelector)
import           UCCrux.LLVM.Shape (Shape)
{- ORMOLU_ENABLE -}

-- | Create a 'Crux.SimulatorCallback' that sequences and passes data between
-- the given 'Actions.SimActions', and stores their final result in the given
-- 'IORef'.
mkCallback ::
  ArchOk arch =>
  Semigroup onError =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  -- | Where to store the results of analyzing errors
  IORef onError ->
  -- | Actions to run before and after simulation
  Actions.ForAllSymInterface (Actions.SomeSimActions (MapToCrucibleType arch argTypes) onError a) ->
  -- | Function to execute
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  LLVMOptions ->
  Crux.SimulatorCallback msgs
mkCallback appCtx modCtx funCtx halloc resultRef actions0 cfg llvmOpts =
  Crux.SimulatorCallback $ \sym _maybeOnline ->
    do
      let trans = modCtx ^. moduleTranslation
      let llvmCtxt = trans ^. transContext
      let memOptions = memOpts llvmOpts
      bbMapRef <- IORef.newIORef (Map.empty :: LLVMAnnMap sym)
      let ?lc = llvmCtxt ^. llvmTypeCtx
      let ?recordLLVMAnnotation =
            \an bb -> IORef.modifyIORef bbMapRef (Map.insert an bb)
      let ?intrinsicsOpts = intrinsicsOpts llvmOpts
      let ?memOpts = memOptions
      let simctx =
            (setupSimCtxt halloc sym memOptions (llvmMemVar llvmCtxt))
              { Crucible.printHandle = view outputHandle ?outputConfig
              }

      Actions.ForAllSymInterface (Actions.SomeSimActions actions) <-
        return actions0
      (args, mem, extra) <-
        Actions.runMakeArguments (Actions.makeArguments actions) sym

      let globSt = llvmGlobalsToCtx llvmCtxt mem
      let initSt =
            Crucible.InitialState simctx globSt Crucible.defaultAbortHandler CrucibleTypes.UnitRepr $
              Crucible.runOverrideSim CrucibleTypes.UnitRepr $
                do
                  -- TODO(lb): This could be more lazy: We could install only
                  -- those functions that are used by the program. It's an open
                  -- question whether this would be faster: it would mean more
                  -- superfluous errors when the program inevitably calls
                  -- functions that haven't yet been installed, but would mean
                  -- faster startup time generally, especially for large
                  -- programs where the vast majority of functions wouldn't be
                  -- called from any particular function. Needs some
                  -- benchmarking.
                  registerFunctions llvmOpts (modCtx ^. llvmModule . to getModule) trans Nothing
                  Actions.runPreSimulation (Actions.pre (Actions.prePost actions)) sym extra
                  liftIO $ (appCtx ^. log) Hi $ "Running " <> funCtx ^. functionName <> " on arguments..."
                  printed <- ppRegMap modCtx funCtx sym mem args
                  mapM_ (liftIO . (appCtx ^. log) Hi . Text.pack . show) printed
                  void $ Crucible.callCFG cfg args

      -- Diagnose errors and write back the results so they can be read in the
      -- outer loop
      let explainFailure _ gl =
            do bb <- IORef.readIORef bbMapRef
               let onError = Actions.onError (Actions.prePost actions)
               result <- Actions.runOnError onError sym extra bb gl
               IORef.modifyIORef resultRef (result <>)
               return mempty

      return (Crux.RunnableState initSt, explainFailure)

-- | Run the simulator on the given CFG in an environment set up by the actions,
-- the return the results computed by the actions (alongside the generic simulator
-- result).
simulateCFG ::
  ArchOk arch =>
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  Monoid onError =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  Actions.ForAllSymInterface (Actions.SomeSimActions (MapToCrucibleType arch argTypes) onError a) ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  IO (Crux.CruxSimulationResult, onError)
simulateCFG appCtx modCtx funCtx halloc actions0 cfg cruxOpts llvmOpts =
  do onErrorRef <- IORef.newIORef mempty
     cruxResult <-
       Crux.runSimulator
         cruxOpts
         ( mkCallback
             appCtx
             modCtx
             funCtx
             halloc
             onErrorRef
             actions0
             cfg
             llvmOpts
         )
     onError <- IORef.readIORef onErrorRef
     Actions.ForAllSymInterface (Actions.SomeSimActions actions) <-
       return actions0
     Actions.runPostSimulation (Actions.post (Actions.prePost actions)) onError _
     return (cruxResult, onError)

makeArgumentsFromConstraints ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Constraints m argTypes ->
  Actions.MakeArguments
    (MapToCrucibleType arch argTypes)
    sym
    ( Crucible.RegMap sym (MapToCrucibleType arch argTypes)
    , MemImpl sym
    , Map.Map
        (Some (What4.SymAnnotation sym))
        (Some (TypedSelector m arch argTypes))
    , Assignment (Shape m (SymValue sym arch)) argTypes
    )
makeArgumentsFromConstraints appCtx modCtx funCtx constraints =
  Actions.MakeArguments $
    \sym ->
       do setupResult <-
            liftIO $ setupExecution appCtx modCtx funCtx sym constraints
          (mem, argAnnotations, assumptions, argShapes, args) <-
            case setupResult of
              (SetupResult mem anns assumptions, (argShapes, args)) ->
                pure (mem, anns, assumptions, argShapes, args)
          -- Assume all predicates necessary to satisfy the deduced preconditions
          assume (funCtx ^. functionName) sym assumptions
          return (args, mem, (args, mem, argAnnotations, argShapes))

registerOverridesPre ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  [ OverrideTemplate
      (personality sym)
      sym
      arch
      (Crucible.RegEntry sym CrucibleTypes.UnitType)
      CrucibleTypes.EmptyCtx
      CrucibleTypes.UnitType
  ] ->
  Actions.PreSimulation (personality sym) sym b ()
registerOverridesPre appCtx modCtx overrides =
  Actions.PreSimulation $
    \_ _ ->
      do for_ overrides $
           \override ->
             liftIO $
               (appCtx ^. log) Hi $
                 Text.unwords
                   [ "Registering override for",
                     case LLVMIntrinsics.overrideTemplateMatcher override of
                       LLVMIntrinsics.ExactMatch nm -> Text.pack nm
                       LLVMIntrinsics.PrefixMatch nm ->
                         "functions with prefix " <> Text.pack nm
                       LLVMIntrinsics.SubstringsMatch nms ->
                         "functions with names containing " <> Text.pack (show nms)
                   ] 
         LLVMIntrinsics.register_llvm_overrides
           (modCtx ^. llvmModule . to getModule)
           []
           overrides
           (modCtx ^. moduleTranslation . transContext)

registerBasicOverridesPre ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  [BasicLLVMOverride arch] ->
  Actions.PreSimulation (personality sym) sym b ()
registerBasicOverridesPre appCtx modCtx overrides =
  registerOverridesPre appCtx modCtx (map getBasicLLVMOverride overrides)

-- | Create overrides that skip execution of declared (but not defined)
-- functions and track information about their usage and return values in an
-- 'IORef'.
registerSkipOverrides ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  Constraints m argTypes ->
  Actions.PreSimulation
    (personality sym)
    sym
    ( IORef (Set SkipOverrideName)
    , IORef
        (Map.Map
          (Some (What4.SymAnnotation sym))
          (Some (TypedSelector m arch argTypes)))
    )
    ()
registerSkipOverrides appCtx modCtx constraints =
  do let trans = modCtx ^. moduleTranslation
     sOverrides <-
       Actions.PreSimulation $
         \sym (skipOverrideRef, skipReturnValueAnnotations) ->
           unsoundSkipOverrides
             appCtx
             modCtx
             sym
             trans
             skipOverrideRef
             skipReturnValueAnnotations
             (constraints ^. returnConstraints)
             (L.modDeclares (modCtx ^. llvmModule . to getModule))
     registerOverridesPre appCtx modCtx sOverrides

useSkipOverrides ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  Monoid onError =>
  AppContext ->
  ModuleContext m arch ->
  Constraints m argTypes ->
  Actions.PrePost
    (personality sym)
    sym
    onError
    ( IORef (Set SkipOverrideName)
    , IORef
        (Map.Map
          (Some (What4.SymAnnotation sym))
          (Some (TypedSelector m arch argTypes)))
    )
    (Set SkipOverrideName)
useSkipOverrides appCtx modCtx constraints =
  Actions.PrePost
    { Actions.pre = registerSkipOverrides appCtx modCtx constraints,
      Actions.onError = return mempty,
      Actions.post =
        do (usedRef, _) <- ask
           -- liftIO $ putStrLn . ("SKIP " ++) . show =<< IORef.readIORef usedRef
           liftIO (IORef.readIORef usedRef)
    }

registerUnsoundOverrides ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  Actions.PreSimulation (personality sym) sym (IORef (Set UnsoundOverrideName)) ()
registerUnsoundOverrides appCtx modCtx =
  registerBasicOverridesPre appCtx modCtx =<<
    (Actions.PreSimulation $
      \_sym unsoundOverrideRef ->
        return (unsoundOverrides (modCtx ^. moduleTranslation) unsoundOverrideRef))

useUnsoundOverrides ::
  Crucible.IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  Monoid onError =>
  AppContext ->
  ModuleContext m arch ->
  Actions.PrePost
    (personality sym)
    sym
    onError
    (IORef (Set UnsoundOverrideName))
    (Set UnsoundOverrideName)
useUnsoundOverrides appCtx modCtx =
  Actions.PrePost
    { Actions.pre = registerUnsoundOverrides appCtx modCtx,
      Actions.onError = return mempty,
      Actions.post = liftIO . IORef.readIORef =<< ask
    }


doClassify ::
  ArchOk arch =>
  Crucible.IsBoolSolver sym =>
  What4.IsInterpretedFloatExprBuilder sym =>
  (sym ~ What4.ExprBuilder t st fs) =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Actions.OnError
    sym
    ( Crucible.RegMap sym (MapToCrucibleType arch argTypes)
    , MemImpl sym
    , Map.Map
        (Some (What4.SymAnnotation sym))
        (Some (TypedSelector m arch argTypes))
    , Assignment (Shape m (SymValue sym arch)) argTypes
    , IORef (Set SkipOverrideName)
    , IORef
        (Map.Map
          (Some (What4.SymAnnotation sym))
          (Some (TypedSelector m arch argTypes)))
    )
    (Located (Explanation m arch argTypes))
doClassify appCtx modCtx funCtx =
  Actions.OnError $
    \sym (args, mem, argAnnotations, argShapes, skipOverrideRef, skipReturnValueAnnotations) bb gl ->
      do
        let loc = gl ^. Crucible.labeledPredMsg . to Crucible.simErrorLoc
        let ann = What4.getAnnotation sym (gl ^. Crucible.labeledPred)
        case flip Map.lookup bb . BoolAnn =<< ann of
          Nothing ->
            case ann of
              Just _ ->
                panic "simulateLLVM" ["Unexplained error: no error for annotation."]
              Nothing ->
                return $
                  case gl ^. Crucible.labeledPredMsg . to Crucible.simErrorReason of
                    Crucible.ResourceExhausted msg ->
                      Located loc (ExExhaustedBounds msg)
                    Crucible.AssertFailureSimError msg _ ->
                      if "Call to assert" `isInfixOf` msg -- HACK
                        then
                          classifyAssertion
                            sym
                            (gl ^. Crucible.labeledPred)
                            loc
                        else
                          Located
                            loc
                            (ExUncertain (UMissingAnnotation (gl ^. Crucible.labeledPredMsg)))
                    _ ->
                      Located
                        loc
                        (ExUncertain (UMissingAnnotation (gl ^. Crucible.labeledPredMsg)))
          Just badBehavior ->
            do
              -- Helpful for debugging:
              -- putStrLn "~~~~~~~~~~~"
              -- putStrLn (show (LLVMErrors.ppBB badBehavior))

              liftIO $ (appCtx ^. log) Hi ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior)))
              skipped <- IORef.readIORef skipOverrideRef
              liftIO $ (appCtx ^. log) Hi ("Skipped functions: " <> Text.pack (show skipped))
              retAnns <- IORef.readIORef skipReturnValueAnnotations
              classifyBadBehavior
                appCtx
                modCtx
                funCtx
                sym
                mem
                skipped
                (gl ^. Crucible.labeledPredMsg)
                args
                (Map.union argAnnotations retAnns)
                argShapes
                badBehavior

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.6
-- compatibility.
data UCCruxSimulationResult m arch (argTypes :: Ctx (FullType m)) = UCCruxSimulationResult
  { unsoundness :: Unsoundness,
    explanations :: [Located (Explanation m arch argTypes)]
  }

-- | The default set of actions that UC-Crux runs before and after performing
-- symbolic execution.
defaultActions ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  Crucible.IsBoolSolver sym =>
  What4.IsInterpretedFloatExprBuilder sym =>
  (sym ~ What4.ExprBuilder t st fs) =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Constraints m argTypes ->
  Actions.SimActions
    (MapToCrucibleType arch argTypes)
    (personality sym)
    sym
    [Located (Explanation m arch argTypes)]
    ( Crucible.RegMap sym (MapToCrucibleType arch argTypes)
    , MemImpl sym
    , Map.Map
        (Some (What4.SymAnnotation sym))
        (Some (TypedSelector m arch argTypes))
    , Assignment (Shape m (SymValue sym arch)) argTypes
    , IORef (Set UnsoundOverrideName)
    , IORef (Set SkipOverrideName)
    , IORef
        (Map.Map
          (Some (What4.SymAnnotation sym))
          (Some (TypedSelector m arch argTypes)))
    )
    ( Set UnsoundOverrideName
    , Set SkipOverrideName
    )
defaultActions appCtx modCtx funCtx constraints =
  (\(((), unsound), skip) -> (unsound, skip)) <$> actions
  where
    -- Start by constructing arguments from the given constraints
    mkArgs =
      Actions.SimActions
      { Actions.makeArguments =
          makeArgumentsFromConstraints appCtx modCtx funCtx constraints,
        Actions.prePost =
          Actions.PrePost
            { Actions.pre = return (),
              Actions.post = return ()
            }
      }

    -- Then register unsound (under-approximate) overrides and record which ones
    -- get used
    unsound =
      Actions.andThenWithIORef
        Set.empty
        mkArgs
        (useUnsoundOverrides appCtx modCtx)

    -- Then register overrides for declared functions and record which ones get
    -- used
    unsoundAndSkip =
      Actions.andThenWithIORefs
        Set.empty
        Map.empty
        unsound
        (useSkipOverrides appCtx modCtx constraints)

    -- Do a bunch of pipe-fitting to make the types line up and mix in
    -- classification.
    actions =
      Actions.addOnError
        (let reassoc1 (((a, b, c, d), e), (f, g)) = (a, b, c, d, e, f, g)
             reassoc2 (a, b, c, d, e, f, g) = (((a, b, c, d), e), (f, g))
         in Actions.shim reassoc1 reassoc2 unsoundAndSkip)
        (let dropOne (a, b, c, d, _e, f, g) = (a, b, c, d, f, g)
         in Profunctor.lmap dropOne ((:[]) <$> doClassify appCtx modCtx funCtx))

runSimulator ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  Constraints m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  IO (UCCruxSimulationResult m arch argTypes)
runSimulator appCtx modCtx funCtx halloc constraints cfg cruxOpts llvmOpts =
  do unless (null (constraints ^. relationalConstraints)) $
       panic "simulateLLVM" ["Unimplemented: relational constraints"]
     let actions =
           Actions.ForAllSymInterface
             (Actions.SomeSimActions
               (defaultActions appCtx modCtx funCtx constraints))
     (cruxResult, result) <-
       simulateCFG appCtx modCtx funCtx halloc actions cfg cruxOpts llvmOpts
     return $
       UCCruxSimulationResult
         (foldMap (\(unsound, skip, _expl) -> Unsoundness unsound skip) result)
         (case cruxResult of
           Crux.CruxSimulationResult Crux.ProgramIncomplete _ ->
               [ Located
                   What4.initializationLoc
                   (ExUncertain (UTimeout (funCtx ^. functionName)))
               ]
           _ -> map (\(_unsound, _skip, expl) -> expl) result)
