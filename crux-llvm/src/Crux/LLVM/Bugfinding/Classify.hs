{-
Module       : Crux.LLVM.Bugfinding.Classify
Description  : Classify errors as true positives or due to missing preconditions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Bugfinding.Classify
  ( Explanation(..)
  , TruePositive(..)
  , ppExplanation
  , classify
  ) where

import           Control.Lens (to, (^.))
import           Control.Monad.IO.Class (liftIO, MonadIO)
import           Data.Text (Text)
import qualified Data.Text as Text

import           Lumberjack (writeLogM, HasLog)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

-- import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPointer
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as LLVMErrors

import           Crux.LLVM.Bugfinding.Constraints
import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Cursor (ppCursor)
import           Crux.LLVM.Bugfinding.Setup.Monad (TypedSelector(..))
import Data.Parameterized.Classes (IxedF'(ixF'))
import Data.Functor.Const (Const(getConst))

data TruePositive
  -- TODO which
  = UninitializedStackVariable
  | Generic Text

-- | An error is either a true positive, or a false positives due to some
-- missing preconditions.
data Explanation types
  = ExTruePositive TruePositive
  | ExMissingPreconditions (Constraints types)

ppExplanation :: Explanation types -> Text
ppExplanation =
  \case
    ExTruePositive truePositive ->
      case truePositive of
        UninitializedStackVariable -> "Uninitialized stack variable"
        Generic text -> text
    ExMissingPreconditions constraints -> "Missing constraints"


summarizeOp :: LLVMErrors.MemoryOp sym w -> (Maybe String, LLVMPointer.LLVMPtr sym w)
summarizeOp =
  \case
    LLVMErrors.MemLoadOp _storageType expl ptr _mem -> (expl, ptr)
    LLVMErrors.MemStoreOp _storageType expl ptr _mem -> (expl, ptr)
    LLVMErrors.MemStoreBytesOp expl ptr _sz _mem -> (expl, ptr)
    LLVMErrors.MemCopyOp (destExpl, dest) (_srcExpl, _src) _len _mem -> (destExpl, dest)
    LLVMErrors.MemLoadHandleOp _llvmType expl ptr _mem -> (expl, ptr)
    LLVMErrors.MemInvalidateOp _whatIsThisParam expl ptr _size _mem -> (expl, ptr)


-- | Take an error that occurred during symbolic execution, classify it as a
-- true or false positive. If it is a false positive, deduce further
-- preconditions.
classify ::
  forall m sym arch argTypes.
  ( Crucible.IsSymInterface sym
  , MonadIO m
  , HasLog Text m
  ) =>
  Context arch argTypes ->
  sym ->
  Crucible.RegMap sym argTypes {-^ Function arguments -} ->
  MapF (What4.SymAnnotation sym) (TypedSelector argTypes)
    {-^ Term annotations (origins) -} ->
  LLVMErrors.BadBehavior sym {-^ Data about the error that occurred -} ->
  m (Explanation argTypes)
classify context sym (Crucible.RegMap args) annotations badBehavior =
  writeLogM ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior))) >>
  let
    getPtrOffsetAnn ::
      LLVMPointer.LLVMPtr sym w ->
      Maybe (TypedSelector argTypes (What4.BaseBVType w))
    getPtrOffsetAnn ptr =
      flip MapF.lookup annotations =<<
        What4.getAnnotation sym (LLVMPointer.llvmPointerOffset ptr)
    argName :: Ctx.Index argTypes tp -> String
    argName idx = context ^. argumentNames . ixF' idx . to getConst . to (maybe "<top>" Text.unpack)
  in
    case badBehavior of
      LLVMErrors.BBUndefinedBehavior
        (LLVMErrors.WriteBadAlignment ptr alignment) ->
          case (getPtrOffsetAnn (Crucible.unRV ptr)) of
            Just (TypedSelector (SelectArgument (Some idx) cursor) _typeRepr) ->
              do writeLogM $
                   Text.unwords
                     [ "Diagnosis: Read from a pointer with insufficient"
                     , "alignment in argument"
                     , "#" <> Text.pack (show (Ctx.indexVal idx))
                     , "at"
                     , Text.pack (show (ppCursor (argName idx) cursor))
                     ]
                 writeLogM $
                   Text.unwords
                     [ "Prescription: Add a precondition that the pointer"
                     , "is sufficiently aligned."
                     ]
                 return $
                   ExMissingPreconditions $
                     oneArgumentConstraint
                       (Ctx.size args)
                       idx
                       [ValueConstraint (Aligned alignment) cursor]
            Nothing -> error "Unimplemented: bad write align"
      LLVMErrors.BBUndefinedBehavior
        (LLVMErrors.ReadBadAlignment ptr alignment) ->
          case getPtrOffsetAnn (Crucible.unRV ptr) of
            Just (TypedSelector (SelectArgument (Some idx) cursor) _typeRepr) ->
              do writeLogM $
                   Text.unwords
                     [ "Diagnosis: Wrote to a pointer with insufficient"
                     , "alignment in argument"
                     , "#" <> Text.pack (show (Ctx.indexVal idx))
                     , "at"
                     , Text.pack (show (ppCursor (argName idx) cursor))
                     ]
                 writeLogM $
                   Text.unwords
                     [ "Prescription: Add a precondition that the pointer"
                     , "is sufficiently aligned."
                     ]
                 return $
                   ExMissingPreconditions $
                     oneArgumentConstraint
                       (Ctx.size args)
                       idx
                       [ValueConstraint (Aligned alignment) cursor]
            Nothing -> error "Unimplemented: bad read align"
      LLVMErrors.BBMemoryError
        (LLVMErrors.MemoryError
          (summarizeOp -> (_expl, ptr))
          LLVMErrors.UnwritableRegion) ->
            case getPtrOffsetAnn ptr of
              Just (TypedSelector (SelectArgument (Some idx) cursor) _typeRepr) ->
                -- TODO: Double check that it really was unmapped not read-only
                -- or something?
                do writeLogM $
                      Text.unwords
                        [ "Diagnosis: Read from an unmapped pointer in argument"
                        , "#" <> Text.pack (show (Ctx.indexVal idx))
                        , "at"
                        , Text.pack (show (ppCursor (argName idx) cursor))
                        ]
                   writeLogM $
                     Text.unwords
                       [ "Prescription: Add a precondition that the pointer"
                       , "points to allocated memory."
                       ]
                   return $
                     ExMissingPreconditions $
                       oneArgumentConstraint
                         (Ctx.size args)
                         idx
                         [ValueConstraint Allocated cursor]
              Just (TypedSelector (SelectGlobal _symbol _cursor) _typeRepr) ->
                error "Unimplemented: Global"
              -- TODO(lb): Something about globals, probably?
              Nothing -> error ("Unimplemented:" ++ show (LLVMPointer.ppPtr ptr))
      LLVMErrors.BBMemoryError
        (LLVMErrors.MemoryError
          _op
          (LLVMErrors.NoSatisfyingWrite _storageType ptr)) ->
            case getPtrOffsetAnn ptr of
              Just (TypedSelector (SelectArgument (Some idx) cursor) _typeRepr) ->
                do writeLogM $
                     Text.unwords
                       [ "Diagnosis: Read from an uninitialized pointer in argument"
                       , "#" <> Text.pack (show (Ctx.indexVal idx))
                       , "at"
                       , Text.pack (show (ppCursor (argName idx) cursor))
                       ]
                   writeLogM $
                     Text.unwords
                       [ "Prescription: Add a precondition that the pointer"
                       , "points to initialized memory."
                       ]
                   return $
                     ExMissingPreconditions $
                       oneArgumentConstraint
                         (Ctx.size args)
                         idx
                         [ValueConstraint Initialized cursor]
              Just (TypedSelector (SelectGlobal _symbol _cursor) _typeRepr) ->
                error "Unimplemented: Global"
              -- TODO(lb): Something about globals, probably?
              Nothing -> error ("Unimplemented:" ++ show (LLVMPointer.ppPtr ptr))
      _ -> pure $ ExTruePositive (Generic "Unknown error (assuming true positive)")
