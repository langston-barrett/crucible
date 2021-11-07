{-
Module           : UCCrux.LLVM.Bug
Description      : Representation of possible bugs
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}

module UCCrux.LLVM.Bug
  ( Bug,
    bugBehavior,
    bugLoc,
    makeBug,
    ppBug,
    BugBehavior(..),
    ppBugBehavior,
    UndefinedBehaviorTag,
    getUndefinedBehaviorTag,
    makeUndefinedBehaviorTag,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Functor.Const (Const(Const))

import qualified Prettyprinter as PP

import           Data.Parameterized.TraversableF (fmapF)

import qualified What4.ProgramLoc as What4

import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack, ppCallStack)
import           Lang.Crucible.LLVM.Errors (BadBehavior)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import           Lang.Crucible.LLVM.Errors.MemoryError (MemoryErrorReason)
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemErrors
import           Lang.Crucible.LLVM.Errors.UndefinedBehavior (UndefinedBehavior)
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB

import           UCCrux.LLVM.PP (ppProgramLoc)
{- ORMOLU_ENABLE -}

newtype UndefinedBehaviorTag =
  UndefinedBehaviorTag { getUndefinedBehaviorTag :: UndefinedBehavior (Const ()) }

makeUndefinedBehaviorTag :: UndefinedBehavior e -> UndefinedBehaviorTag
makeUndefinedBehaviorTag = UndefinedBehaviorTag . fmapF (const (Const ()))

instance Eq UndefinedBehaviorTag where
  UndefinedBehaviorTag t1 == UndefinedBehaviorTag t2 =
    case (t1, t2) of
      (UB.FreeBadOffset {}, UB.FreeBadOffset {}) -> True
      (UB.FreeUnallocated {}, UB.FreeUnallocated {}) -> True
      (UB.DoubleFree {}, UB.DoubleFree {}) -> True
      (UB.MemsetInvalidRegion {}, UB.MemsetInvalidRegion {}) -> True
      (UB.ReadBadAlignment {}, UB.ReadBadAlignment {}) -> True
      (UB.WriteBadAlignment {}, UB.WriteBadAlignment {}) -> True
      (UB.PtrAddOffsetOutOfBounds {}, UB.PtrAddOffsetOutOfBounds {}) -> True
      (UB.CompareInvalidPointer {}, UB.CompareInvalidPointer {}) -> True
      (UB.CompareDifferentAllocs {}, UB.CompareDifferentAllocs {}) -> True
      (UB.PtrSubDifferentAllocs {}, UB.PtrSubDifferentAllocs {}) -> True
      (UB.PointerIntCast {}, UB.PointerIntCast {}) -> True
      (UB.PointerUnsupportedOp {}, UB.PointerUnsupportedOp {}) -> True
      (UB.PointerFloatCast {}, UB.PointerFloatCast {}) -> True
      (UB.ComparePointerToBV {}, UB.ComparePointerToBV {}) -> True
      (UB.UDivByZero {}, UB.UDivByZero {}) -> True
      (UB.SDivByZero {}, UB.SDivByZero {}) -> True
      (UB.URemByZero {}, UB.URemByZero {}) -> True
      (UB.SRemByZero {}, UB.SRemByZero {}) -> True
      (UB.SDivOverflow {}, UB.SDivOverflow {}) -> True
      (UB.SRemOverflow {}, UB.SRemOverflow {}) -> True
      (UB.AbsIntMin  {}, UB.AbsIntMin  {}) -> True
      (UB.PoisonValueCreated {}, UB.PoisonValueCreated {}) -> True
      _ -> False

-- TODO
-- instance Ord UndefinedBehaviorTag where
--     compare (UndefinedBehaviorTag t1) (UndefinedBehaviorTag t2) = _

-- | This is different from 'Lang.Crucible.LLVM.Errors.BadBehavior' in that
-- it stores less data.
data BugBehavior
  = BBUndefinedBehaviorTag !UndefinedBehaviorTag
  | BBMemoryErrorReason MemoryErrorReason
  deriving (Eq)

ppBugBehavior :: BugBehavior -> PP.Doc ann
ppBugBehavior =
  \case
    BBUndefinedBehaviorTag (UndefinedBehaviorTag ub) -> UB.explain ub
    BBMemoryErrorReason mer -> MemErrors.ppMemoryErrorReason mer

-- | A possible bug: What it is, and where it can occur.
data Bug =
  Bug
    { bugBehavior :: BugBehavior
    , bugLoc :: !What4.ProgramLoc
    , bugCallStack :: !CallStack
    }
  deriving (Eq)

makeBug :: BadBehavior sym -> What4.ProgramLoc -> CallStack -> Bug
makeBug bb loc callStack =
  Bug
    { bugBehavior =
        case bb of
          LLVMErrors.BBUndefinedBehavior ub ->
            BBUndefinedBehaviorTag (makeUndefinedBehaviorTag ub)
          LLVMErrors.BBMemoryError (MemErrors.MemoryError _ rsn) ->
            BBMemoryErrorReason rsn,
      bugLoc = loc,
      bugCallStack = callStack
    }

ppBug :: Bug -> PP.Doc ann
ppBug (Bug bb loc callStack) =
  PP.vsep
    [ ppBugBehavior bb
    , PP.pretty "at" <> PP.pretty (ppProgramLoc loc)
    , PP.pretty "in context:"
    , PP.indent 2 (ppCallStack callStack)
    ]
