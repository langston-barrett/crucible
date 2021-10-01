{-
Module       : UCCrux.LLVM.Overrides.Basic
Description  : A 'BasicLLVMOverride' is one that's maximally polymorphic
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Overrides.Basic
  ( BasicLLVMOverride,
    makeBasicLLVMOverride,
    getBasicLLVMOverride
  )
where

{- ORMOLU_DISABLE -}
import           Lang.Crucible.Backend (IsSymInterface)

import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate)
{- ORMOLU_ENABLE -}

-- | An override that is compatible with any symbolic backend.
newtype BasicLLVMOverride arch =
  BasicLLVMOverride
    { getBasicLLVMOverride ::
        forall personality sym rtp l a.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        OverrideTemplate (personality sym) sym arch rtp l a
    }

makeBasicLLVMOverride ::
  (forall personality sym rtp l a.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   OverrideTemplate (personality sym) sym arch rtp l a) ->
  BasicLLVMOverride arch
makeBasicLLVMOverride = BasicLLVMOverride
