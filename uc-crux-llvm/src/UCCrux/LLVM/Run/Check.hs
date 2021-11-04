{-
Module           : UCCrux.LLVM.Run.Check
Description      : Check inferred function contracts. See 'inferThenCheck'.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Run.Check
  ( SomeCheckResult,
    checkInferredContracts,
    inferThenCheck
  )
where

{- ORMOLU_DISABLE -}
import           Data.IORef (IORef)
import qualified Data.IORef as IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import qualified Data.Text as Text
import           Data.Traversable (for)
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import           Data.Void (Void)

import qualified Prettyprinter as PP

import           Data.Parameterized.Context (Assignment)
import           Data.Parameterized.Some (Some(Some))

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.CFG.Core as Crucible
import           Lang.Crucible.FunctionHandle (HandleAllocator)

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (MemImpl, HasLLVMAnn)
import           Lang.Crucible.LLVM.Extension (LLVM)

-- crux
import           Crux.Config.Common (CruxOptions)
import qualified Crux.Log as Crux
import qualified Crux.Types as Crux

-- crux-llvm
import           Crux.LLVM.Config (LLVMOptions)
import qualified Crux.LLVM.Config as CruxLLVM
import           Crux.LLVM.Overrides (ArchOk)

-- local
import           UCCrux.LLVM.Constraints (Constraints, emptyConstraints)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), findFun)
import           UCCrux.LLVM.Context.Function (FunctionContext, makeFunctionContext, ppFunctionContextError)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType (FullTypeRepr, MapToCrucibleType)
import           UCCrux.LLVM.Module (DefnSymbol, FuncSymbol(FuncDefnSymbol), defnSymbolToString)
import qualified UCCrux.LLVM.Overrides.Check as Check
import           UCCrux.LLVM.Overrides.Check (CheckOverrideName, SomeCheckedConstraint)
import           UCCrux.LLVM.Overrides.Stack (Stack)
import           UCCrux.LLVM.Run.EntryPoints (EntryPoints, getEntryPoints)
import qualified UCCrux.LLVM.Run.Simulate as Sim
import qualified UCCrux.LLVM.Run.Loop as Loop
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Setup (SymValue)
import           UCCrux.LLVM.Shape (Shape)
{- ORMOLU_ENABLE -}

newtype GetSomeCheckOverrideResult m sym arch =
  GetSomeCheckOverrideResult
    (forall r.
     (forall argTypes.
      DefnSymbol m ->
      Assignment (FullTypeRepr m) argTypes ->
      [Check.CheckOverrideResult m sym arch argTypes] ->
      IO r) ->
     IO r)

-- | The result of checking inferred contracts
data CheckResult m arch argTypes =
  CheckResult
    { getCheckResult ::
        forall r.
        (forall sym.
         IsSymInterface sym =>
         sym ->
         -- | Pre-simulation memory
         MemImpl sym ->
         -- | Arguments passed to the entry point
         Assignment (Shape m (SymValue sym arch)) argTypes ->
         Crux.CruxSimulationResult ->
         Sim.UCCruxSimulationResult m arch argTypes ->
         [GetSomeCheckOverrideResult m sym arch] ->
         r) ->
        r
    }

data SomeCheckResult m arch =
  forall argTypes.
  SomeCheckResult
    { checkResultTypes :: Assignment (FullTypeRepr m) argTypes,
      checkResult :: CheckResult m arch argTypes
    }

data TypedConstraints m argTypes
  = TypedConstraints
      { tcConstraints :: Constraints m argTypes
      , tcTypes :: Assignment (FullTypeRepr m) argTypes
      }

checkInferredContracts_ ::
  forall m arch argTypes blocks ret msgs.
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  Constraints m argTypes ->
  -- | Entry point
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Inferred function contracts
  Map (DefnSymbol m) (Some (TypedConstraints m)) ->
  IO (CheckResult m arch argTypes)
checkInferredContracts_ appCtx modCtx funCtx halloc cruxOpts llOpts constraints cfg contracts =
   Sim.runSimulatorWithCallbacks
     appCtx
     modCtx
     funCtx
     halloc
     constraints
     cfg
     cruxOpts
     llOpts
     (Sim.SimulatorCallbacks $
       do ovs <- overrides
          return $
            Sim.SimulatorHooks
              { Sim.createOverrideHooks = map fst ovs
              , Sim.resultHook =
                \sym mem args cruxResult ucResult ->
                  return $
                    CheckResult $
                      \k -> k sym mem args cruxResult ucResult (map snd ovs)
              })
  where
    overrides ::
      IsSymInterface sym =>
      HasLLVMAnn sym =>
      IO [ ( Sim.SymCreateOverrideFn sym arch
           , GetSomeCheckOverrideResult m sym arch
           )
         ]
    overrides =
      for
        (Map.toList contracts)
        (\(func, (Some (TypedConstraints constraints types))) ->
           do CFGWithTypes cfg argFTys _retTy _varArgs <-
                pure (findFun modCtx (FuncDefnSymbol func))
              let ?memOpts = CruxLLVM.memOpts llOpts
              case testEquality argFTys types of
                Nothing -> panic "checkInferredContracts" []
                Just Refl ->
                  do ref <- IORef.newIORef []
                     return $
                       ( Sim.SymCreateOverrideFn $
                           \_sym ->
                             return $
                               Check.createCheckOverride
                                 appCtx
                                 modCtx
                                 ref
                                 types
                                 constraints
                                 cfg
                                 (FuncDefnSymbol func)
                       , GetSomeCheckOverrideResult
                           (\f -> f func argFTys =<< IORef.readIORef ref)
                       )
        )

-- | Postcondition: The keys of the returned 'Map' are exactly the
-- 'EntryPoints'.
checkInferredContracts ::
  forall m arch msgs.
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Where to begin symbolic execution
  EntryPoints m ->
  -- | Inferred function contracts
  Map (DefnSymbol m) (Some (TypedConstraints m)) ->
  IO (Map (DefnSymbol m) (SomeCheckResult m arch))
checkInferredContracts appCtx modCtx halloc cruxOpts llOpts entries contracts =
  fmap Map.fromList $
    for (getEntryPoints entries) $
      \entry ->
        do CFGWithTypes cfg argFTys _retTy _varArgs <-
             pure (findFun modCtx (FuncDefnSymbol entry))

           funCtx <-
             case makeFunctionContext modCtx entry argFTys (Crucible.cfgArgTypes cfg) of
               Left err ->
                 panic
                   "checkInferredContracts"
                   [Text.unpack (ppFunctionContextError err)]
               Right funCtxF -> return funCtxF
           result <-
            checkInferredContracts_
              appCtx
              modCtx
              funCtx
              halloc
              cruxOpts
              llOpts
              (emptyConstraints argFTys)
              cfg
              contracts
           return (entry, SomeCheckResult argFTys result)

-- | Infer preconditions for a group of functions, then for the ones that are
-- safe-with-preconditions, check their inferred preconditions by seeing if they
-- hold during symbolic execution from some (other) group of functions.
--
-- Postcondition:
-- * The keys of the first map are the 'EntryPoints' given for inference
-- * The keys of the second map are the 'EntryPoints' given for checking
inferThenCheck ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Functions to infer contracts for
  EntryPoints m ->
  -- | Entry points for checking inferred contracts
  EntryPoints m ->
  IO ( Map (DefnSymbol m) SomeBugfindingResult
     , Map (DefnSymbol m) (SomeCheckResult m arch)
     )
inferThenCheck appCtx modCtx halloc cruxOpts llOpts toInfer entries =
  do inferResult <-
       Loop.loopOnFunctions appCtx modCtx halloc cruxOpts llOpts toInfer
     checkResult <-
       checkInferredContracts appCtx modCtx halloc cruxOpts llOpts entries $
         Map.mapMaybe getConstraints inferResult
     return (inferResult, checkResult)
  where
    getConstraints (Result.SomeBugfindingResult types result _) =
      case Result.summary result of
        Result.AlwaysSafe {} -> Nothing
        Result.FoundBugs {} -> Nothing
        Result.SafeUpToBounds {} -> Nothing
        Result.Unclear {} -> Nothing
        Result.SafeWithPreconditions Result.DidHitBounds _ _ -> Nothing
        Result.SafeWithPreconditions Result.DidntHitBounds _unsound cs ->
          Just (Some (TypedConstraints cs types))

-- TODO: Some kind of reporting for violated constraints
-- Iterate over each CheckedConstraint. If the predicate (safety condition) is
-- falsifiable, add the constraint to the report.
