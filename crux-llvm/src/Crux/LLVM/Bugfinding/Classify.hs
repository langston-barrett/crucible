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
  , partitionExplanations
  , TruePositive(..)
  , ppTruePositive
  , ppExplanation
  , classify
  ) where

import           Control.Applicative ((<|>))
import           Control.Lens (to, (^.))
import           Control.Monad.IO.Class (MonadIO)
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (maybeToList)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))
import           Data.Void (Void)

import           Prettyprinter (Doc)

import           Lumberjack (writeLogM, HasLog)

import           Data.Parameterized.Classes (IxedF'(ixF'), ShowF)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (foldMapFC)

import qualified What4.Interface as What4
import qualified What4.Expr.Builder as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import           Lang.Crucible.LLVM.Errors (ppBB)
import qualified Lang.Crucible.LLVM.Errors.MemoryError as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as LLVMErrors

import           Crux.LLVM.Bugfinding.Constraints
import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Cursor (ppCursor, SomeInSelector(SomeInSelector))
import           Crux.LLVM.Bugfinding.FullType (MapToCrucibleType, IsPtrRepr(..), isPtrRepr)
import           Crux.LLVM.Bugfinding.Setup.Monad (TypedSelector(..))
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)

data TruePositive
  -- TODO which
  = UninitializedStackVariable

-- | An error is either a true positive, a false positive due to some missing
-- preconditions, or unknown.
data Explanation m arch types
  = ExTruePositive TruePositive
  | ExMissingPreconditions (Constraints m arch types)
  | ExUnclassified (Doc Void)
  -- ^ We don't (yet) know what to do about this error

partitionExplanations ::
  [Explanation m arch types] -> ([TruePositive], [Constraints m arch types], [Doc Void])
partitionExplanations = go [] [] []
  where go ts cs ds =
          \case
            [] -> (ts, cs, ds)
            (ExTruePositive t:xs) ->
              let (ts', cs', ds') = go ts cs ds xs
              in (t:ts', cs', ds')
            (ExMissingPreconditions c:xs) ->
              let (ts', cs', ds') = go ts cs ds xs
              in (ts', c:cs', ds')
            (ExUnclassified d:xs) ->
              let (ts', cs', ds') = go ts cs ds xs
              in (ts', cs', d:ds')

ppTruePositive :: TruePositive -> Text
ppTruePositive =
  \case
    UninitializedStackVariable -> "Uninitialized stack variable"

ppExplanation :: Explanation m arch types -> Text
ppExplanation =
  \case
    ExTruePositive truePositive -> ppTruePositive truePositive
    ExMissingPreconditions constraints ->
      "Missing preconditions:" <> Text.pack (show (ppConstraints constraints))
    ExUnclassified doc -> "Unclassified/unknown error:\n" <> Text.pack (show doc)

summarizeOp :: LLVMErrors.MemoryOp sym w -> (Maybe String, LLVMPtr.LLVMPtr sym w)
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
  forall f m sym arch argTypes t st fs.
  ( Crucible.IsSymInterface sym
  , sym ~ What4.ExprBuilder t st fs  -- needed for asApp
  , MonadIO f
  , HasLog Text f
  , ShowF (What4.SymAnnotation sym)
  ) =>
  Context m arch argTypes ->
  sym ->
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) {-^ Function arguments -} ->
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))
    {-^ Term annotations (origins) -} ->
  LLVMErrors.BadBehavior sym {-^ Data about the error that occurred -} ->
  f (Explanation m arch argTypes)
classify context sym (Crucible.RegMap _args) annotations badBehavior =
  writeLogM ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior))) >>
  let
    getPtrOffsetAnn ::
      LLVMPtr.LLVMPtr sym w ->
      Maybe (Some (TypedSelector m arch argTypes))
    getPtrOffsetAnn ptr =
      flip Map.lookup annotations . Some =<<
        What4.getAnnotation sym (LLVMPtr.llvmPointerOffset ptr)
    getPtrBlockAnn ::
      LLVMPtr.LLVMPtr sym w ->
      Maybe (Some (TypedSelector m arch argTypes))
    getPtrBlockAnn ptr =
      flip Map.lookup annotations . Some =<<
        What4.getAnnotation sym (LLVMPtr.llvmPointerBlock ptr)
    getAnyPtrOffsetAnn ::
      LLVMPtr.LLVMPtr sym w ->
      [Some (TypedSelector m arch argTypes)]
    getAnyPtrOffsetAnn ptr =
      case What4.asApp (LLVMPtr.llvmPointerOffset ptr) of
        Nothing -> []
        Just app ->
          foldMapFC
            (\expr -> maybeToList (flip Map.lookup annotations . Some =<<
                                     What4.getAnnotation sym expr))
            app
    argName :: Ctx.Index argTypes tp -> String
    argName idx = context ^. argumentNames . ixF' idx . to getConst . to (maybe "<top>" Text.unpack)
    unclass =
      do writeLogM ("Couldn't classify error." :: Text)
         pure $ ExUnclassified (ppBB badBehavior)
  in
    case badBehavior of
      LLVMErrors.BBUndefinedBehavior
        (LLVMErrors.WriteBadAlignment ptr alignment) ->
          case getPtrOffsetAnn (Crucible.unRV ptr) of
            Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
              do writeLogM $
                   Text.unwords
                     [ "Diagnosis: Read from a pointer with insufficient"
                     , "alignment in argument"
                     , "#" <> Text.pack (show (Ctx.indexVal idx))
                     , "at"
                     , Text.pack (show (ppCursor (argName idx) cursor))
                     , "(" <> Text.pack (show (LLVMPtr.ppPtr (Crucible.unRV ptr))) <> ")"
                     ]
                 writeLogM $
                   Text.unwords
                     [ "Prescription: Add a precondition that the pointer"
                     , "is sufficiently aligned."
                     ]
                 case isPtrRepr ftRepr of
                   Nothing -> panic "classify" ["Expected pointer type"]
                   Just (IsPtrRepr Refl) ->
                     return $
                       ExMissingPreconditions $
                         oneArgumentConstraint
                           (Ctx.size (context ^. argumentFullTypes))
                           idx
                           (Set.singleton
                               (SomeValueConstraint
                                 (ValueConstraint
                                   (context ^. argumentFullTypes . ixF' idx)
                                   cursor
                                   (Aligned alignment))))
            _ -> unclass
      LLVMErrors.BBUndefinedBehavior
        (LLVMErrors.ReadBadAlignment ptr alignment) ->
          case getPtrOffsetAnn (Crucible.unRV ptr) of
            Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
              do writeLogM $
                   Text.unwords
                     [ "Diagnosis: Wrote to a pointer with insufficient"
                     , "alignment in argument"
                     , "#" <> Text.pack (show (Ctx.indexVal idx))
                     , "at"
                     , Text.pack (show (ppCursor (argName idx) cursor))
                     , "(" <> Text.pack (show (LLVMPtr.ppPtr (Crucible.unRV ptr))) <> ")"
                     ]
                 writeLogM $
                   Text.unwords
                     [ "Prescription: Add a precondition that the pointer"
                     , "is sufficiently aligned."
                     ]
                 case isPtrRepr ftRepr of
                   Nothing -> panic "classify" ["Expected pointer type"]
                   Just (IsPtrRepr Refl) ->
                     return $
                       ExMissingPreconditions $
                         oneArgumentConstraint
                           (Ctx.size (context ^. argumentFullTypes))
                           idx
                           (Set.singleton
                             (SomeValueConstraint
                               (ValueConstraint
                               (context ^. argumentFullTypes . ixF' idx)
                               cursor
                               (Aligned alignment))))
            _ -> unclass
      LLVMErrors.BBMemoryError
        (LLVMErrors.MemoryError
          (summarizeOp -> (_expl, ptr))
          LLVMErrors.UnwritableRegion) ->
            case getPtrOffsetAnn ptr of
              Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                -- TODO: Double check that it really was unmapped not read-only
                -- or something?
                do writeLogM $
                      Text.unwords
                        [ "Diagnosis: Write to an unmapped pointer in argument"
                        , "#" <> Text.pack (show (Ctx.indexVal idx))
                        , "at"
                        , Text.pack (show (ppCursor (argName idx) cursor))
                        , "(allocation: " <> Text.pack (show (What4.printSymExpr (LLVMPtr.llvmPointerBlock ptr)))  <> ")"
                        , "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                        ]
                   writeLogM $
                     Text.unwords
                       [ "Prescription: Add a precondition that the pointer"
                       , "points to allocated memory."
                       ]
                   case isPtrRepr ftRepr of
                     Nothing -> panic "classify" ["Expected pointer type"]
                     Just (IsPtrRepr Refl) ->
                       return $
                         ExMissingPreconditions $
                           oneArgumentConstraint
                             (Ctx.size (context ^. argumentFullTypes))
                             idx
                             (Set.singleton
                               (SomeValueConstraint
                                (ValueConstraint
                                 (context ^. argumentFullTypes . ixF' idx)
                                 cursor
                                 Allocated)))
              -- TODO(lb): Something about globals, probably?
              _ -> unclass
      LLVMErrors.BBMemoryError
        (LLVMErrors.MemoryError
          _op
          (LLVMErrors.NoSatisfyingWrite _storageType ptr)) ->
            case (getPtrBlockAnn ptr, getAnyPtrOffsetAnn ptr) of
              (Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor))))
                , _) ->
                do writeLogM $
                     Text.unwords
                       [ "Diagnosis: Read from an uninitialized pointer in argument"
                       , "#" <> Text.pack (show (Ctx.indexVal idx))
                       , "at"
                       , Text.pack (show (ppCursor (argName idx) cursor))
                       , "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                       ]
                   writeLogM $
                     Text.unwords
                       [ "Prescription: Add a precondition that the pointer"
                       , "points to initialized memory."
                       ]
                   case isPtrRepr ftRepr of
                     Nothing -> panic "classify" ["Expected pointer type"]
                     Just (IsPtrRepr Refl) ->
                       return $
                         ExMissingPreconditions $
                           oneArgumentConstraint
                             (Ctx.size (context ^. argumentFullTypes))
                             idx
                             (Set.singleton
                               (SomeValueConstraint
                                (ValueConstraint
                                 (context ^. argumentFullTypes . ixF' idx)
                                 cursor
                                 Initialized)))
              (Nothing, [Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))]) ->
                do writeLogM $
                     Text.unwords
                       [ "Diagnosis: Read from an uninitialized pointer calculated"
                       , "from a pointer in argument"
                       , "#" <> Text.pack (show (Ctx.indexVal idx))
                       , "at"
                       , Text.pack (show (ppCursor (argName idx) cursor))
                       , "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                       ]
                   writeLogM $
                     Text.unwords
                       [ "Prescription: Add a precondition that the pointer"
                       , "points to initialized memory."
                       ]
                   case isPtrRepr ftRepr of
                     Nothing -> panic "classify" ["Expected pointer type"]
                     Just (IsPtrRepr Refl) ->
                       return $
                         ExMissingPreconditions $
                           oneArgumentConstraint
                             (Ctx.size (context ^. argumentFullTypes))
                             idx
                             (Set.singleton
                               (SomeValueConstraint
                                (ValueConstraint
                                 (context ^. argumentFullTypes . ixF' idx)
                                 cursor
                                 Initialized)))
              _ -> unclass
      _ -> unclass
