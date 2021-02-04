{-
Module       : Crux.LLVM.Bugfinding.Classify
Description  : Classify errors as true positives or due to missing preconditions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Classify
  ( Explanation(..)
  , TruePositive(..)
  , MissingPrecondition(..)
  , ppExplanation
  , classify
  ) where

import           Data.Text (Text)
-- import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

-- import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as LLVMErrors

data TruePositive
  -- TODO which
  = UninitializedStackVariable
  | Generic Text

data MissingPrecondition
  -- TODO which part
  = UnmappedArgumentPointer
  -- TODO which
  | UninitializedGlobal

data Explanation
  = ExTruePositive TruePositive
  | ExMissingPrecondition MissingPrecondition

ppExplanation :: Explanation -> Text
ppExplanation =
  \case
    ExTruePositive truePositive ->
      case truePositive of
        UninitializedStackVariable -> "Uninitialized stack variable"
        Generic text -> text
    ExMissingPrecondition missingPrecond ->
      case missingPrecond of
        UnmappedArgumentPointer -> "Uninitialized global"
        UninitializedGlobal -> "Unmapped pointer"


-- | Take an error that occurred during symbolic execution, classify it as a
-- true or false positive. If it is a false positive, deduce further
-- preconditions.
classify ::
  forall sym init.
  (Crucible.IsSymInterface sym) =>
  sym ->
  Crucible.RegMap sym init ->
  LLVMErrors.BadBehavior sym ->
  IO Explanation
classify sym args badBehavior =
  -- writeLogM ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior))) >>
  case badBehavior of
    LLVMErrors.BBUndefinedBehavior _ -> undefined
    LLVMErrors.BBMemoryError
      (LLVMErrors.MemoryError
        _op
        (LLVMErrors.NoSatisfyingWrite _ty ptr)) ->
          -- Was this pointer reachable from an argument to the function? If so,
          -- it's a missing precondtion. If not, we count it as an error.
          -- TODO(lb): More sophisticated reasoning needed.
          -- TODO(lb): anyFC
          if undefined sym ptr args
          then pure (ExMissingPrecondition UnmappedArgumentPointer)
          else pure (ExTruePositive (Generic "No write"))
    _ -> error "Unimplemented: explainError"
