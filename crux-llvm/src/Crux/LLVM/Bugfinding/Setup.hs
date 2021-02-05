{-
Module       : Crux.LLVM.Bugfinding.Setup
Description  : Setting up memory and function args according to preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Bugfinding.Setup
  ( setupExecution
  ) where

import           Control.Lens ((^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import           Text.LLVM.AST as L

import           Lumberjack (HasLog, writeLogM)

import qualified Data.Parameterized.Context as Ctx

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Globals as LLVMGlobals
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.Constraints
import           Crux.LLVM.Bugfinding.Cursor
import           Crux.LLVM.Bugfinding.Setup.Monad

-- TODO unsorted
import qualified Data.Text as Text
import Data.Parameterized.TraversableFC (foldlMFC)

data ExecutionSetupError = ExecutionSetupError

showRegEntry ::
  forall proxy arch sym ty.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  Crucible.RegEntry sym ty ->
  Text
showRegEntry proxy regEntry =
  -- annotateTerm :: sym -> SymExpr sym tp -> IO (SymAnnotation sym tp, SymExpr sym tp)
  case CrucibleTypes.asBaseType (Crucible.regType regEntry) of
    CrucibleTypes.AsBaseType _baseTyRepr ->
      Text.pack (show (What4.printSymExpr (Crucible.regValue regEntry)))
    CrucibleTypes.NotBaseType ->
      case Crucible.regType regEntry of
        CrucibleTypes.UnitRepr -> "()"
        -- TODO(lb): More cases!
        -- LLVMMem.PtrRepr -> Text.pack (show (LLVMMem.ppPointer (Crucible.regValue regEntry)))
        -- LLVMMem.PtrRepr ->
        --   Text.pack (show (LLVMMem.ppPtr (Crucible.regValue regEntry)))
        -- CrucibleTypes.IntrinsicRepr
        --   (testEquality llvmPtrRepr -> Just Refl)
        --   (Ctx.Empty Ctx.:> (CrucibleTypes.asBaseType ->
        --                         CrucibleTypes.AsBaseType
        --                           bvRepr@(CrucibleTypes.BaseBVRepr _width))) ->
          -- error "Unreachable"
        _ -> "unimplemented"

annotatedTerm ::
  forall sym tp.
  (Crucible.IsSymInterface sym) =>
  sym ->
  CrucibleTypes.BaseTypeRepr tp ->
  Cursor ->
  Setup sym (What4.SymExpr sym tp)
annotatedTerm sym typeRepr cursor =
  do symbol <- freshSymbol
      -- TODO(lb): Is freshConstant correct here?
     (annotation, expr) <-
        liftIO $ What4.annotateTerm sym =<< What4.freshConstant sym symbol typeRepr
     addAnnotation annotation cursor typeRepr
     pure $ expr

generateMinimalValue ::
  forall proxy sym arch tp.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  sym ->
  CrucibleTypes.TypeRepr tp ->
  Cursor ->
  Setup sym (Crucible.RegValue sym tp)
generateMinimalValue _proxy sym typeRepr cursor =
  let unimplemented = error ("Unimplemented: " ++ show typeRepr) -- TODO(lb)
  in
    case CrucibleTypes.asBaseType typeRepr of
      CrucibleTypes.AsBaseType baseTypeRepr ->
        annotatedTerm sym baseTypeRepr cursor
      CrucibleTypes.NotBaseType ->
        case typeRepr of
          CrucibleTypes.UnitRepr -> return ()
          CrucibleTypes.AnyRepr ->
            -- TODO(lb): Should be made more complex
            return $ Crucible.AnyValue CrucibleTypes.UnitRepr ()

          LLVMMem.PtrRepr ->
            do liftIO . LLVMMem.llvmPointer_bv sym =<<
                 annotatedTerm sym (CrucibleTypes.BaseBVRepr ?ptrWidth) cursor
          CrucibleTypes.VectorRepr _containedTypeRepr -> unimplemented
          CrucibleTypes.StructRepr _containedTypes -> unimplemented
          _ -> unimplemented -- TODO(lb)

-- TODO(lb): Replace with "generate"
doGen ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  CrucibleTypes.CtxRepr init ->
  Setup sym (Crucible.RegMap sym init)
doGen proxy sym types =
  case Ctx.viewAssign types of
    Ctx.AssignEmpty -> pure Crucible.emptyRegMap
    Ctx.AssignExtend rest typeRepr ->
      do first <- generateMinimalValue proxy sym typeRepr Here
         rest_ <- doGen proxy sym rest
         pure $ Crucible.assignReg typeRepr first rest_

-- | Construct minimal arguments for a function based on the types.
generateMinimalArgs ::
  forall proxy arch sym types.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  CrucibleTypes.CtxRepr types  {-^ Argument Crucible types -} ->
  Setup sym (Crucible.RegMap sym types)
generateMinimalArgs proxy sym argTypes = do
  writeLogM ("Generating minimal arguments" :: Text)
  Crucible.RegMap args <- doGen proxy sym argTypes
  foldlMFC
    (\n arg ->
       do writeLogM (Text.unwords [ "Argument"
                                  , Text.pack (show n) <> ":"
                                  , showRegEntry proxy arg
                                  -- , "(type:"
                                  -- , Text.pack (show (Crucible.regType arg)) <> ")"
                                  ])
          return (n + 1))
    (0 :: Int)
    args

  return (Crucible.RegMap args)

setupExecution ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  , HasLog Text m
  , MonadIO m
  ) =>
  sym ->
  L.Module ->
  LLVMTrans.ModuleTranslation arch ->
  Constraints types ->
  -- Ctx.Assignment (Const L.Type) init {-^ Argument LLVM types -} ->
  CrucibleTypes.CtxRepr types  {-^ Argument Crucible types -} ->
  m (Either ExecutionSetupError (Crucible.RegMap sym types, LLVMMem.MemImpl sym))
setupExecution sym llvmMod moduleTrans _preconds argCrucibleTypes = do
  -- TODO(lb): More lazy here?
  let llvmCtxt = moduleTrans ^. LLVMTrans.transContext
  -- TODO: More lazy?
  mem <-
    let ?lc = llvmCtxt ^. LLVMTrans.llvmTypeCtx
    in liftIO $
         LLVMGlobals.populateAllGlobals sym (LLVMTrans.globalInitMap moduleTrans)
           =<< LLVMGlobals.initializeAllMemory sym llvmCtxt llvmMod
  (mem', _annotations, minimalArgs) <-
    runSetup mem $ generateMinimalArgs moduleTrans sym argCrucibleTypes
  -- TODO use preconds
  return $ Right (minimalArgs, mem')
