-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Concretize
-- Description      : Get a feasible concrete memory from a model
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- TODO: docs! refer to existing conc of regval
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.MemModel.Concretize
  ( ConcAlloc(..)
  , ConcMem(..)
  , concMem
  ) where

-- TODO sort
import qualified What4.Expr.GroundEval as W4GE
import Data.Word (Word8)
import Data.Vector (Vector, MVector)
import Data.IntMap (IntMap)
import qualified Lang.Crucible.LLVM.MemModel.MemLog as Mem
import Lang.Crucible.LLVM.DataLayout (EndianForm, Alignment)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Control.Monad (foldM)
import Numeric.Natural (Natural)
import Lang.Crucible.Panic (panic)
import Data.Sequence (Seq)
import qualified Data.Vector as Vec
import qualified Data.BitVector.Sized as BV
import What4.Expr (Expr)
import What4.Interface (SymExpr, SymNat)
import qualified Data.Sequence as Seq
import qualified What4.Interface as W4
import Control.Monad.ST (RealWorld)
import qualified Data.Vector.Mutable as MVec

data ConcAllocStorage vecTy
  = UnboundedStorage (Seq (Maybe Word8))
  | BoundedStorage (vecTy (Maybe Word8))

type MutConcAllocStorage = ConcAllocStorage (MVector RealWorld)

data ConcAlloc vecTy
  = ConcAlloc
    { concAllocAlign :: Alignment
    , concAllocFreed :: Maybe String
    , concAllocMut :: Mem.Mutability
    , concAllocType :: Mem.AllocType
    , concAllocSrcLoc :: String
    , concAllocStorage :: ConcAllocStorage vecTy
    }

type MutConcAlloc = ConcAlloc (MVector RealWorld)

newtype ConcMemState vecTy
  = ConcMemState { getConcMemState :: IntMap (ConcAlloc vecTy) }

emptyConcMemState :: ConcMemState vecTy
emptyConcMemState = ConcMemState IntMap.empty

type MutConcMemState = ConcMemState (MVector RealWorld)

data ConcMem
  = ConcMem
    { concMemAllocs :: ConcMemState Vector
    , concMemEndianForm :: EndianForm
    }

concMem ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  Mem.Mem sym ->
  IO ConcMem
concMem gFn mem = do
  -- SAFETY: TODO
  concAllocs <- unsafeFreezeMemState =<< concMemState gFn (Mem._memState mem)
  pure $
    ConcMem
    { concMemAllocs = concAllocs
    , concMemEndianForm = Mem.memEndianForm mem
    }

concMemState ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  Mem.MemState sym ->
  IO MutConcMemState
concMemState gFn =
  \case
    Mem.EmptyMem _ _ changes ->
      applyMemChanges gFn changes emptyConcMemState
    Mem.StackFrame _ _ _name changes memState ->
      applyMemChanges gFn changes =<< concMemState gFn memState
    Mem.BranchFrame _ _ changes memState ->
      applyMemChanges gFn changes =<< concMemState gFn memState

applyMemChanges ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  Mem.MemChanges sym ->
  MutConcMemState ->
  IO MutConcMemState
applyMemChanges gFn changes concState = do
  (allocs, writes) <- pure changes
  concState' <- applyMemAllocs gFn concState allocs
  applyMemWrites gFn concState' writes

---------------------------------------------------------------------
-- * Allocation

applyMemAllocs ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Mem.MemAllocs sym ->
  IO (ConcMemState (MVector RealWorld))
applyMemAllocs gFn concState =
  \case
    Mem.MemAllocs [] -> pure concState
    Mem.MemAllocs (a : as) -> do
      -- "Changes are stored in order, with more recent changes closer to the
      -- head of the list", so we apply the last first.
      concState' <- applyMemAllocs gFn concState (Mem.MemAllocs as)
      applyMemAlloc gFn concState' a

applyMemAlloc ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Mem.MemAlloc sym ->
  IO MutConcMemState
applyMemAlloc gFn concState =
  \case
    Mem.Allocations allocs ->
      foldM
        (\st (blk, info) -> concAlloc gFn st blk info)
        concState
        (Map.toList allocs)
    Mem.MemFree nat name -> concFree gFn nat name concState
    Mem.AllocMerge cond tAllocs fAllocs -> do
      W4GE.GroundEvalFn gFn' <- pure gFn
      b <- gFn' cond
      applyMemAllocs gFn concState (if b then tAllocs else fAllocs)

concAlloc ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Natural ->
  Mem.AllocInfo sym ->
  IO MutConcMemState
concAlloc gFn (ConcMemState memMap) blockNum info =
  let idx = fromIntegral blockNum in
  case IntMap.lookup idx memMap of
    Just {} ->
      panic "concAlloc" ["Attempt to reuse block number " ++ show blockNum]
    Nothing -> do
      Mem.AllocInfo ty msz mut align srcLoc <- pure info
      storage <-
        case msz of
          Nothing -> pure (UnboundedStorage Seq.empty)
          Just sz -> do
            W4GE.GroundEvalFn gFn' <- pure gFn
            concSz <- gFn' sz
            let vecSz = fromIntegral (BV.asUnsigned concSz)
            vec <- MVec.replicate vecSz Nothing
            pure (BoundedStorage vec)
      let cAlloc =
            ConcAlloc
            { concAllocAlign = align
            , concAllocFreed = Nothing  -- not yet freed
            , concAllocMut = mut
            , concAllocType = ty
            , concAllocSrcLoc = srcLoc
            , concAllocStorage = storage
            }
      pure (ConcMemState (IntMap.insert idx cAlloc memMap))

concFree ::
  (SymExpr sym ~ Expr t) =>
  W4GE.GroundEvalFn t ->
  SymNat sym ->
  String ->
  MutConcMemState ->
  IO MutConcMemState
concFree (W4GE.GroundEvalFn gFn) blk loc (ConcMemState concMap) = do
  blk' <- gFn (W4.natToIntegerPure blk)
  pure $
    ConcMemState $
      IntMap.update
        (\alloc -> Just (alloc { concAllocFreed = Just loc }))
        (fromIntegral blk')
        concMap

---------------------------------------------------------------------
-- * Writes

applyMemWrites ::
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Mem.MemWrites sym ->
  IO (MutConcMemState)
applyMemWrites gFn concState =
  \case
    Mem.MemWrites [] -> pure concState
    Mem.MemWrites (w : ws) -> do
      -- "Changes are stored in order, with more recent changes closer to the
      -- head of the list", so we apply the last first.
      concState' <- applyMemWrites gFn concState (Mem.MemWrites ws)
      applyMemWritesChunk gFn concState' w

applyMemWritesChunk ::
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Mem.MemWritesChunk sym ->
  IO MutConcMemState
applyMemWritesChunk gFn concState =
  \case
    Mem.MemWritesChunkFlat [] -> pure concState
    Mem.MemWritesChunkFlat (x : xs) -> do
      concState' <- applyMemWritesChunk gFn concState (Mem.MemWritesChunkFlat xs)
      applyMemWrite gFn concState' x
    Mem.MemWritesChunkIndexed writesMap ->
      applyIndexedWrites gFn concState writesMap

applyIndexedWrites ::
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  IntMap [Mem.MemWrite sym] ->
  IO MutConcMemState
applyIndexedWrites gFn concState writesMap =
  foldM
    (\st (blk, writes) -> applyWritesForBlock gFn st blk writes)
    concState
    (IntMap.toList writesMap)

applyWritesForBlock ::
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  IntMap.Key ->
  [Mem.MemWrite sym] ->
  IO MutConcMemState
applyWritesForBlock gFn concState@(ConcMemState concMap) blk writes =
  case IntMap.lookup blk concMap of
    Nothing -> pure concState
    Just alloc -> do
      alloc' <- applyWritesForAlloc gFn alloc writes
      pure (ConcMemState (IntMap.insert blk alloc' concMap))

applyWritesForAlloc ::
  W4GE.GroundEvalFn t ->
  MutConcAlloc ->
  [Mem.MemWrite sym] ->
  IO MutConcAlloc
applyWritesForAlloc gFn alloc writes =
  case concAllocMut alloc of
    Mem.Immutable -> pure alloc
    Mem.Mutable -> do
      storage <- applyWritesForStorage gFn (concAllocStorage alloc) writes
      pure (alloc { concAllocStorage = storage })

applyWritesForStorage ::
  W4GE.GroundEvalFn t ->
  MutConcAllocStorage ->
  [Mem.MemWrite sym] ->
  IO MutConcAllocStorage
applyWritesForStorage gFn storage writes =
  case storage of
    UnboundedStorage s ->
      UnboundedStorage <$> applyWritesForUnboundedStorage gFn s writes
    BoundedStorage v ->
      BoundedStorage <$> applyWritesForBoundedStorage gFn v writes

applyWritesForBoundedStorage ::
  W4GE.GroundEvalFn t ->
  MVector RealWorld (Maybe Word8) ->
  [Mem.MemWrite sym] ->
  IO (MVector RealWorld (Maybe Word8))
applyWritesForBoundedStorage gFn v =
  \case
    [] -> pure v
    (w : ws) -> do
      v' <- applyWritesForBoundedStorage gFn v ws
      applyWriteForBoundedStorage gFn v' w

applyWriteForBoundedStorage ::
  W4GE.GroundEvalFn t ->
  MVector RealWorld (Maybe Word8) ->
  Mem.MemWrite sym ->
  IO (MVector RealWorld (Maybe Word8))
applyWriteForBoundedStorage gFn v =
  \case
    Mem.MemWrite _ptr src -> _
    Mem.WriteMerge cond tWrites fWrites -> _

applyWritesForUnboundedStorage ::
  W4GE.GroundEvalFn t ->
  Seq (Maybe Word8) ->
  [Mem.MemWrite sym] ->
  IO (Seq (Maybe Word8))
applyWritesForUnboundedStorage = _

applyMemWrite ::
  W4GE.GroundEvalFn t ->
  MutConcMemState ->
  Mem.MemWrite sym ->
  IO MutConcMemState
applyMemWrite gFn concState = _

---------------------------------------------------------------------
-- * Freezing

unsafeFreezeMemState ::
  MutConcMemState ->
  IO (ConcMemState Vector)
unsafeFreezeMemState (ConcMemState concMap) =
  ConcMemState <$>
    traverse unsafeFreezeAlloc concMap

unsafeFreezeAlloc ::
  ConcAlloc (MVector RealWorld) ->
  IO (ConcAlloc Vector)
unsafeFreezeAlloc alloc = do
  storage' <- unsafeFreezeStorage (concAllocStorage alloc)
  pure (alloc { concAllocStorage = storage' })

unsafeFreezeStorage ::
  ConcAllocStorage (MVector RealWorld) ->
  IO (ConcAllocStorage Vector)
unsafeFreezeStorage =
  \case
    UnboundedStorage s -> pure (UnboundedStorage s)
    BoundedStorage v -> BoundedStorage <$> Vec.unsafeFreeze v
