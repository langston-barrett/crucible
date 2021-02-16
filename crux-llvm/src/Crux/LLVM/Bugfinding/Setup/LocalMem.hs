{-
Module       : Crux.LLVM.Bugfinding.Setup.LocalMem
Description  : A wrapper around 'LLVM.MemImpl'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

A wrapper around 'LLVMMem.MemImpl' that keeps track of allocations and what's
been stored to them.

We could instead rely on 'LLVMMem.doLoad', however, the code that supports
'LLVMMem.doLoad' is very complex, must handle symbolic values, and requires more
from the callee, and requires more from the caller. The case of the @Setup@
monad should only be dealing with concrete pointers, and it should be able to
retrieve previously-allocated values without fear of failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.LocalMem
  ( LocalMem(..)
  , makeLocalMem
  , globalMem
  , TypedRegEntry(..)

  -- * Operations
  , load
  , maybeMalloc
  , store
  ) where

import           Control.Lens (Simple, Lens, lens, (^.))
import           Control.Monad (join)
import           Control.Monad.IO.Class (liftIO)
import           Data.BitVector.Sized (mkBV)
import           Data.Functor.Compose (Compose(Compose, getCompose))
import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import           Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import           Lang.Crucible.LLVM.DataLayout (noAlignment, DataLayout, maxAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.MemModel (StorageType)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType, memTypeSize)

import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.FullType (FullType(FTPtr), FullTypeRepr(FTPtrRepr), ToCrucibleType, ToBaseType, toFullRepr)
import           Crux.LLVM.Bugfinding.Setup.Annotation (Annotation, makeAnnotation)

data TypedRegEntry arch sym ft =
  forall full. TypedRegEntry (FullTypeRepr full arch ft) (Crucible.RegEntry sym (ToCrucibleType ft))

data LocalMem arch sym
  = LocalMem
      { _localMem :: MapF (Annotation arch sym) (Compose Maybe (TypedRegEntry arch sym))
      -- The keys are always BaseBV annotations, but those aren't Ord
      , _globalMem :: LLVMMem.MemImpl sym
      }

makeLocalMem :: LLVMMem.MemImpl sym -> LocalMem arch sym
makeLocalMem mem =
  LocalMem
    { _localMem = MapF.empty
    , _globalMem = mem
    }

localMem :: Simple Lens (LocalMem arch sym) (MapF (Annotation arch sym) (Compose Maybe (TypedRegEntry arch sym)))
localMem = lens _localMem (\s v -> s { _localMem = v })

globalMem :: Simple Lens (LocalMem arch sym) (LLVMMem.MemImpl sym)
globalMem = lens _globalMem (\s v -> s { _globalMem = v })

-- | Retrieve a pre-existing annotation for a pointer, or make a new one.
getAnnotation ::
  ( Crucible.IsSymInterface sym
  ) =>
  proxy arch ->
  sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  IO ( What4.SymAnnotation sym (CrucibleTypes.BaseBVType (ArchWidth arch))
     , LLVMMem.LLVMPtr sym (ArchWidth arch)
     )
getAnnotation _proxy sym ptr =
  case What4.getAnnotation sym (LLVMMem.llvmPointerOffset ptr) of
    Just annotation -> pure (annotation, ptr)
    Nothing -> liftIO $ LLVMMem.annotatePointerOffset sym ptr

mkPtrRepr :: FullTypeRepr full arch ft -> FullTypeRepr full arch ('FTPtr ft)
mkPtrRepr fullTypeRepr =
  FTPtrRepr (toFullRepr fullTypeRepr) (toFullRepr fullTypeRepr) fullTypeRepr

load ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem arch sym ->
  sym ->
  FullTypeRepr full arch ft ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Maybe (TypedRegEntry arch sym ft)
load _proxy mem sym ftRepr ptr =
  case What4.getAnnotation sym (LLVMMem.llvmPointerOffset ptr) of
    Just ann ->
      join $ getCompose <$>
        MapF.lookup (makeAnnotation (mkPtrRepr ftRepr) ann) (mem ^. localMem)
    Nothing -> Nothing

malloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem arch sym ->
  sym ->
  DataLayout ->
  FullTypeRepr full arch ft ->
  MemType ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem arch sym)
malloc proxy mem sym dl ftRepr memType =
  do (ptr, globalMem') <-
       liftIO $
         do sizeBv <-
              What4.bvLit
                sym
                ?ptrWidth
                (mkBV ?ptrWidth (bytesToInteger (memTypeSize dl memType)))
            LLVMMem.doMalloc
              sym
              LLVMMem.HeapAlloc  -- TODO(lb): Change based on arg/global
              LLVMMem.Mutable  -- TODO(lb): Change based on arg/global
              "crux-llvm bugfinding auto-setup"
              (mem ^. globalMem)
              sizeBv
              (maxAlignment dl) -- TODO is this OK?
     (annotation, ptr') <- getAnnotation proxy sym ptr
     pure (ptr', mem { _globalMem = globalMem'
                     , _localMem =
                        MapF.insert
                          (makeAnnotation (mkPtrRepr ftRepr) annotation)
                          (Compose Nothing)
                          (mem ^. localMem)
                     })

maybeMalloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem arch sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  sym ->
  DataLayout ->
  FullTypeRepr full arch ft ->
  MemType ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem arch sym)
maybeMalloc proxy mem ptr sym dl fullTypeRepr memType =
  case load proxy mem sym fullTypeRepr ptr of
    Just _ -> pure (ptr, mem)
    Nothing -> malloc proxy mem sym dl fullTypeRepr memType

store ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem arch sym ->
  sym ->
  FullTypeRepr full arch ft ->
  StorageType ->
  Crucible.RegEntry sym (ToCrucibleType ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem arch sym)
store proxy mem sym fullTypeRepr storageType regEntry@(Crucible.RegEntry typeRepr regValue) ptr =
  do (annotation, ptr') <- getAnnotation proxy sym ptr
     globalMem' <- LLVMMem.doStore sym (mem ^. globalMem) ptr' typeRepr storageType noAlignment regValue
     pure $
       ( ptr'
       , mem { _globalMem = globalMem'
             , _localMem =
                 MapF.insert
                   (makeAnnotation (mkPtrRepr fullTypeRepr) annotation)
                   (Compose (Just (TypedRegEntry fullTypeRepr regEntry)))
                   (mem ^. localMem)
             }
       )
