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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import           Data.Kind (Type)

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
import           Lang.Crucible.LLVM.MemType (memTypeSize)

import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.FullType (FullTypeRepr(FTPtrRepr), PartTypeRepr(PTFullRepr), ToCrucibleType)
import           Crux.LLVM.Bugfinding.FullType.MemType (toMemType)
import           Crux.LLVM.Bugfinding.Setup.Annotation (Annotation, makeAnnotation)

data TypedRegEntry m arch sym ft =
  TypedRegEntry (FullTypeRepr m ft) (Crucible.RegEntry sym (ToCrucibleType arch ft))

data LocalMem (m :: Type) arch sym
  = LocalMem
      { _localMem :: MapF (Annotation m arch sym) (Compose Maybe (TypedRegEntry m arch sym))
      -- The keys are always BaseBV annotations, but those aren't Ord
      , _globalMem :: LLVMMem.MemImpl sym
      }

makeLocalMem :: LLVMMem.MemImpl sym -> LocalMem m arch sym
makeLocalMem mem =
  LocalMem
    { _localMem = MapF.empty
    , _globalMem = mem
    }

localMem :: Simple Lens (LocalMem m arch sym) (MapF (Annotation m arch sym) (Compose Maybe (TypedRegEntry m arch sym)))
localMem = lens _localMem (\s v -> s { _localMem = v })

globalMem :: Simple Lens (LocalMem m arch sym) (LLVMMem.MemImpl sym)
globalMem = lens _globalMem (\s v -> s { _globalMem = v })

-- | Retrieve a pre-existing annotation for a pointer, or make a new one.
getAnnotation ::
  ( Crucible.IsSymInterface sym
  ) =>
  proxy arch ->
  sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  IO ( What4.SymAnnotation sym CrucibleTypes.BaseNatType
     , LLVMMem.LLVMPtr sym (ArchWidth arch)
     )
getAnnotation _proxy sym ptr =
  case What4.getAnnotation sym (LLVMMem.llvmPointerBlock ptr) of
    Just annotation -> pure (annotation, ptr)
    Nothing -> liftIO $ LLVMMem.annotatePointerBlock sym ptr

load ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem m arch sym ->
  sym ->
  FullTypeRepr m ft ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Maybe (TypedRegEntry m arch sym ft)
load _proxy mem sym ftRepr ptr =
  case What4.getAnnotation sym (LLVMMem.llvmPointerBlock ptr) of
    Just ann ->
      join $ getCompose <$>
        MapF.lookup (makeAnnotation (FTPtrRepr $ PTFullRepr ftRepr) ann) (mem ^. localMem)
    Nothing -> Nothing

malloc ::
  forall m arch sym ft proxy.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem m arch sym ->
  sym ->
  DataLayout ->
  FullTypeRepr m ft ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem m arch sym)
malloc proxy mem sym dl ftRepr =
  do (ptr, globalMem') <-
       liftIO $
         do sizeBv <-
              What4.bvLit
                sym
                ?ptrWidth
                (mkBV ?ptrWidth (bytesToInteger (memTypeSize dl (toMemType ftRepr))))
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
                          (makeAnnotation (FTPtrRepr $ PTFullRepr ftRepr) annotation)
                          (Compose Nothing)
                          (mem ^. localMem)
                     })

maybeMalloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem m arch sym ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  sym ->
  DataLayout ->
  FullTypeRepr m ft ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem m arch sym)
maybeMalloc proxy mem ptr sym dl fullTypeRepr =
  case load proxy mem sym fullTypeRepr ptr of
    Just _ -> pure (ptr, mem)
    Nothing -> malloc proxy mem sym dl fullTypeRepr

store ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  proxy arch ->
  LocalMem m arch sym ->
  sym ->
  FullTypeRepr m ft ->
  StorageType ->
  Crucible.RegEntry sym (ToCrucibleType arch ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  IO (LLVMMem.LLVMPtr sym (ArchWidth arch), LocalMem m arch sym)
store proxy mem sym fullTypeRepr storageType regEntry@(Crucible.RegEntry typeRepr regValue) ptr =
  do (annotation, ptr') <- getAnnotation proxy sym ptr
     globalMem' <- LLVMMem.doStore sym (mem ^. globalMem) ptr' typeRepr storageType noAlignment regValue
     pure $
       ( ptr'
       , mem { _globalMem = globalMem'
             , _localMem =
                 MapF.insert
                   (makeAnnotation (FTPtrRepr $ PTFullRepr fullTypeRepr) annotation)
                   (Compose (Just (TypedRegEntry fullTypeRepr regEntry)))
                   (mem ^. localMem)
             }
       )
