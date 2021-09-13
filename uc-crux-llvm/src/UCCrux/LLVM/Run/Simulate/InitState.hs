{-
Module       : UCCrux.LLVM.Run.Simulate.InitState
Description  : Initialize the simulator state
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

This module is intended to be imported qualified.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Run.Simulate.InitState
  ( InitState(..),
    none,
    registerOverrides,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), to)

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (IntrinsicsOptions, register_llvm_overrides)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemOptions)
import           Lang.Crucible.LLVM.Translation (transContext)

import           Lang.Crucible.LLVM.Extension (LLVM)

 -- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

 -- local
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTranslation)
import           UCCrux.LLVM.Module (getModule)
import           UCCrux.LLVM.Overrides.Basic (BasicLLVMOverride, getBasicLLVMOverride)
{- ORMOLU_ENABLE -}

-- | A 'InitState' is an additional arbitrary action run before simulation
newtype InitState m =
  InitState
    { run ::
        forall p sym arch.
          ArchOk arch =>
          Crucible.IsSymInterface sym =>
          HasLLVMAnn sym =>
          (?lc :: TypeContext) =>
          (?intrinsicsOpts :: IntrinsicsOptions) =>
          (?memOpts :: MemOptions) =>
          ModuleContext m arch ->
          sym ->
          Crucible.OverrideSim
            p
            sym
            LLVM
            (Crucible.RegEntry sym CrucibleTypes.UnitType)
            CrucibleTypes.EmptyCtx
            CrucibleTypes.UnitType
            ()
    }

-- | A 'InitState' that doesn't do anything
none :: InitState m
none = InitState (\_ _ -> return ())

-- | A 'InitState' that registers additional overrides
registerOverrides ::
  [BasicLLVMOverride] ->
  InitState m
registerOverrides overrides =
  InitState $
    \modCtx _sym ->
      register_llvm_overrides
        (modCtx ^. llvmModule . to getModule)
        []
        (map getBasicLLVMOverride overrides)
        (modCtx ^. moduleTranslation . transContext)
