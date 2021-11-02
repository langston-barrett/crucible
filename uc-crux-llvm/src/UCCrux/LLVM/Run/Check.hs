{-
Module           : UCCrux.LLVM.Run.Check
Description      : Check inferred function contracts. See 'inferThenCheck'.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Run.Check
  ( CheckReport,
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
import           Lang.Crucible.LLVM.MemModel (MemImpl)

-- crux
import           Crux.Config.Common (CruxOptions)
import           Crux.Log as Crux

-- crux-llvm
import           Crux.LLVM.Config (LLVMOptions)
import           Crux.LLVM.Overrides (ArchOk)

-- local
import           UCCrux.LLVM.Constraints (Constraints, emptyConstraints)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), findFun)
import           UCCrux.LLVM.Context.Function (makeFunctionContext, ppFunctionContextError)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType (FullTypeRepr)
import           UCCrux.LLVM.Module (DefnSymbol, FuncSymbol(FuncDefnSymbol))
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

-- type SomeCheckedConstraint' m = Some (Some (Check.SomeCheckedConstraint m))

-- | The Doc here should be a representation of the RegValue that the constraint
--   was applied to
--
-- It'd be great to have more provenance information here (and so, in
-- CheckedConstraint), specifically, why was this constraint inferred for this
-- function? What kind of error, on what source line, does it help avoid?
--
-- Invariant: All the predicates here should be falsifiable
data CheckReport m
  = CheckReport (Map (DefnSymbol m) (Seq (Check.SomeCheckedConstraint' m, PP.Doc Void)))

createCheckReport ::
  IsSymInterface sym =>
  AppContext ->
  ModuleContext m arch ->
  sym ->
  -- | Initial LLVM memory (containing globals and functions)
  MemImpl sym ->
  -- | The arguments that were passed to the function
  Assignment (Shape m (SymValue sym arch)) argTypes ->
  IO (CheckReport m)
createCheckReport appCtx modCtx sym mem args =
  do undefined
  -- Iterate over each CheckedConstraint. If the predicate (safety condition) is
  -- falsifiable, add the constraint to the report.

data TypedConstraints m argTypes
  = TypedConstraints
      { tcConstraints :: Constraints m argTypes
      , tcTypes :: Assignment (FullTypeRepr m) argTypes
      }

-- | Postcondition: The keys of the returned 'Map' are exactly the
-- 'EntryPoints'.
checkInferredContracts ::
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
  IO (Map (DefnSymbol m) (CheckReport m))
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
           Sim.runSimulatorWithCallbacks
             appCtx
             modCtx
             funCtx
             halloc
             (emptyConstraints argFTys)
             cfg
             cruxOpts
             llOpts
             (Sim.SimulatorCallbacks $
               do ref <- IORef.newIORef Map.empty
                  return $
                    Sim.SimulatorHooks
                      { Sim.createOverrideHooks = overrides ref
                      , Sim.resultHook =
                        \sym _cruxResult _ucResult ->
                          -- TODO: Give access to mem, args to result cont.
                          (entry,) <$> createCheckReport appCtx modCtx sym undefined undefined
                      })
  where
    overrides ::
      IsSymInterface sym =>
      IORef (Map CheckOverrideName [(Stack sym, Seq (SomeCheckedConstraint m sym argTypes))]) ->
      [Sim.SymCreateOverrideFn sym arch]
    overrides ref =
      Map.foldMapWithKey
        (\func (Some (TypedConstraints constraints types)) ->
           do CFGWithTypes cfg argFTys _retTy _varArgs <-
                pure (findFun modCtx (FuncDefnSymbol func))
              case testEquality argFTys types of
                Nothing -> panic "checkInferredContracts" []
                Just Refl ->
                  return $
                    Sim.SymCreateOverrideFn $
                      \_sym ->
                        return $
                          Check.createCheckOverride
                            appCtx
                            modCtx
                            ref
                            types
                            constraints
                            _
                            (FuncDefnSymbol func)
        )
        contracts

summarize ::
  CheckReport m ->
  -- | The results we already collect:
  Map (DefnSymbol m) SomeBugfindingResult ->
  PP.Doc Void
summarize = undefined

-- | Gather 'SomeBugfindingResult' for each function in the 'EntryPoints', then
-- for the ones that are safe-with-preconditions, check their inferred
-- preconditions by seeing if they hold during symbolic execution from some
-- (other) 'EntryPoints'.
inferThenCheck ::
  Crux.Logs msgs =>
  SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Functions to infer contracts for
  EntryPoints m ->
  -- | Entry points for checking inferred contracts
  EntryPoints m ->
  IO (Map (DefnSymbol m) SomeBugfindingResult)
inferThenCheck appCtx modCtx halloc cruxOpts llOpts toInfer entries =
  do results <-
       Loop.loopOnFunctions appCtx modCtx halloc cruxOpts llOpts toInfer
     checkInferredContracts appCtx modCtx entries $
       Map.mapMaybe getConstraints results
     _
  where
    getConstraints (Result.SomeBugfindingResult result) =
      Some $
        case Result.summary result of
          Result.AlwaysSafe {} -> Nothing
          Result.FoundBugs {} -> Nothing
          Result.SafeUpToBounds {} -> Nothing
          Result.Unclear {} -> Nothing
          Result.SafeWithPreconditions Result.DidHitBounds _ _ -> Nothing
          Result.SafeWithPreconditions Result.DidntHitBounds _unsound cs ->
            Just cs
