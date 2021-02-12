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

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.LocalMem
  ( LocalMem(..)
  , makeLocalMem
  , globalMem

  -- * Operations
  , load
  , maybeMalloc
  , store
  ) where

import           Control.Lens (Simple, Lens, lens, (^.))
import           Control.Monad (join)
import           Control.Monad.IO.Class (liftIO)
import           Data.BitVector.Sized (mkBV)
import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.Parameterized.Some (Some(Some))

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

data LocalMem sym
  = LocalMem
      { _localMem :: Map (Some (What4.SymAnnotation sym)) (Maybe (Some (Crucible.RegEntry sym)))
      , _globalMem :: LLVMMem.MemImpl sym
      }

makeLocalMem :: LLVMMem.MemImpl sym -> LocalMem sym
makeLocalMem mem =
  LocalMem
    { _localMem = Map.empty
    , _globalMem = mem
    }

localMem :: Simple Lens (LocalMem sym) (Map (Some (What4.SymAnnotation sym)) (Maybe (Some (Crucible.RegEntry sym))))
localMem = lens _localMem (\s v -> s { _localMem = v })

globalMem :: Simple Lens (LocalMem sym) (LLVMMem.MemImpl sym)
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

load ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem sym ->
  sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Maybe (Some (Crucible.RegEntry sym))
load _proxy mem sym ptr =
  case What4.getAnnotation sym (LLVMMem.llvmPointerOffset ptr) of
    Just annotation -> join $ Map.lookup (Some annotation) (mem ^. localMem)
    Nothing -> Nothing

malloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem sym ->
  sym ->
  DataLayout ->
  MemType ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem sym)
malloc proxy mem sym dl memType =
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
                        Map.insert
                          (Some annotation)
                          Nothing
                          (mem ^. localMem)
                     })

maybeMalloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  sym ->
  DataLayout ->
  MemType ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem sym)
maybeMalloc proxy mem ptr sym dl memType =
  case load proxy mem sym ptr of
    Just _ -> pure (ptr, mem)
    Nothing -> malloc proxy mem sym dl memType

store ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem sym ->
  sym ->
  StorageType ->
  Crucible.RegEntry sym tp ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem sym)
store proxy mem sym storageType regEntry@(Crucible.RegEntry typeRepr regValue) ptr =
  do (annotation, ptr') <- getAnnotation proxy sym ptr
     globalMem' <- LLVMMem.doStore sym (mem ^. globalMem) ptr' typeRepr storageType noAlignment regValue
     pure $
       ( ptr'
       , mem { _globalMem = globalMem'
             , _localMem =
                 Map.insert
                   (Some annotation)
                   (Just (Some regEntry))
                   (mem ^. localMem)
             }
       )
