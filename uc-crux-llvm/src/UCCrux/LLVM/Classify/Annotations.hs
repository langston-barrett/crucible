{-
Module       : UCCrux.LLVM.Classify.Annotations
Description  : Utility functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Classify.Annotations
  ( -- * General expressions
    getTermAnn,
    getAnyTermAnn,

    -- * Pointers
    getPtrOffsetAnn,
    getPtrBlockAnn,
    getAnyPtrOffsetAnn,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (maybeToList)

import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (foldMapFC)

import qualified What4.Interface as What4
import qualified What4.Expr.Builder as What4

import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr

import           UCCrux.LLVM.Setup.Monad (TypedSelector(..))
{- ORMOLU_ENABLE -}

getTermAnn ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  What4.SymExpr sym tp ->
  Maybe (Some (TypedSelector m arch argTypes))
getTermAnn sym annotations expr =
  do
    ann <- What4.getAnnotation sym expr
    Map.lookup (Some ann) annotations

getAnyTermAnn ::
  ( What4.IsExprBuilder sym,
    sym ~ What4.ExprBuilder t st fs -- needed for asApp
  ) =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  What4.SymExpr sym tp ->
  [Some (TypedSelector m arch argTypes)]
getAnyTermAnn sym annotations expr =
  let subAnns =
        case What4.asApp expr of
          Nothing -> []
          Just app ->
            foldMapFC (maybeToList . getTermAnn sym annotations) app
   in case getTermAnn sym annotations expr of
        Just ann -> ann : subAnns
        Nothing -> subAnns

getPtrOffsetAnn ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  LLVMPtr.LLVMPtr sym w ->
  Maybe (Some (TypedSelector m arch argTypes))
getPtrOffsetAnn sym annotations ptr =
  getTermAnn sym annotations (LLVMPtr.llvmPointerOffset ptr)

getPtrBlockAnn ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  LLVMPtr.LLVMPtr sym w ->
  IO (Maybe (Some (TypedSelector m arch argTypes)))
getPtrBlockAnn sym annotations ptr =
  do
    int <- What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
    pure $ getTermAnn sym annotations int

getAnyPtrOffsetAnn ::
  ( What4.IsExprBuilder sym,
    sym ~ What4.ExprBuilder t st fs -- needed for asApp
  ) =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  LLVMPtr.LLVMPtr sym w ->
  [Some (TypedSelector m arch argTypes)]
getAnyPtrOffsetAnn sym annotations ptr =
  getAnyTermAnn sym annotations (LLVMPtr.llvmPointerOffset ptr)
