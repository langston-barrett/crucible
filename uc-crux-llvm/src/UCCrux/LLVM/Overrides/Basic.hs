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
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate)
{- ORMOLU_ENABLE -}

newtype BasicLLVMOverride =
  BasicLLVMOverride
    { getBasicLLVMOverride ::
        forall p sym arch rtp l a.
        OverrideTemplate p sym arch rtp l a
    }

makeBasicLLVMOverride :: (forall p sym arch rtp l a. OverrideTemplate p sym arch rtp l a) -> BasicLLVMOverride
makeBasicLLVMOverride = BasicLLVMOverride
