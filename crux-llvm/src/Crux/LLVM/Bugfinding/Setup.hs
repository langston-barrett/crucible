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

module Crux.LLVM.Bugfinding.Setup
  ( setupExecution
  , logRegMap
  ) where

import           Control.Lens ((^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import           Text.LLVM.AST as L

import           Lumberjack (HasLog, writeLogM)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.Map (MapF)

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
import Control.Monad (void)

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
        LLVMMem.PtrRepr -> Text.pack (show (LLVMMem.ppPtr (Crucible.regValue regEntry)))
        -- LLVMMem.PtrRepr ->
        --   Text.pack (show (LLVMMem.ppPtr (Crucible.regValue regEntry)))
        -- CrucibleTypes.IntrinsicRepr
        --   (testEquality llvmPtrRepr -> Just Refl)
        --   (Ctx.Empty Ctx.:> (CrucibleTypes.asBaseType ->
        --                         CrucibleTypes.AsBaseType
        --                           bvRepr@(CrucibleTypes.BaseBVRepr _width))) ->
          -- error "Unreachable"
        _ -> "unimplemented"

logRegMap ::
  forall m proxy arch sym ty.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  , HasLog Text m
  ) =>
  proxy arch ->
  Crucible.RegMap sym ty ->
  m ()
logRegMap proxy (Crucible.RegMap regmap) =
  void $
    foldlMFC
      (\n arg ->
        do writeLogM (Text.unwords [ "Argument"
                                    , Text.pack (show n) <> ":"
                                    , showRegEntry proxy arg
                                    -- TODO this is useless with annotations
                                    -- , "(type:"
                                    -- , Text.pack (show (Crucible.regType arg)) <> ")"
                                    ])
           return (n + 1))
      (0 :: Int)
      regmap


annotatedTerm ::
  forall sym tp argTypes.
  (Crucible.IsSymInterface sym) =>
  sym ->
  CrucibleTypes.BaseTypeRepr tp ->
  Selector argTypes ->
  Setup sym argTypes (What4.SymExpr sym tp)
annotatedTerm sym typeRepr selector =
  do symbol <- freshSymbol
      -- TODO(lb): Is freshConstant correct here?
     (annotation, expr) <-
        liftIO $ What4.annotateTerm sym =<< What4.freshConstant sym symbol typeRepr
     addAnnotation annotation selector typeRepr
     pure expr

generateMinimalValue ::
  forall proxy sym arch tp argTypes.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  sym ->
  CrucibleTypes.TypeRepr tp ->
  Selector argTypes ->
  Setup sym argTypes (Crucible.RegValue sym tp)
generateMinimalValue _proxy sym typeRepr selector =
  let unimplemented = error ("Unimplemented: " ++ show typeRepr) -- TODO(lb)
  in
    case CrucibleTypes.asBaseType typeRepr of
      CrucibleTypes.AsBaseType baseTypeRepr ->
        annotatedTerm sym baseTypeRepr selector
      CrucibleTypes.NotBaseType ->
        case typeRepr of
          CrucibleTypes.UnitRepr -> return ()
          CrucibleTypes.AnyRepr ->
            -- TODO(lb): Should be made more complex
            return $ Crucible.AnyValue CrucibleTypes.UnitRepr ()

          LLVMMem.PtrRepr ->
            do liftIO . LLVMMem.llvmPointer_bv sym =<<
                 annotatedTerm sym (CrucibleTypes.BaseBVRepr ?ptrWidth) selector
          CrucibleTypes.VectorRepr _containedTypeRepr -> unimplemented
          CrucibleTypes.StructRepr _containedTypes -> unimplemented
          _ -> unimplemented -- TODO(lb)

-- TODO(lb): Replace with "generate"
doGen ::
  forall proxy arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  CrucibleTypes.CtxRepr argTypes ->
  Setup sym argTypes (Crucible.RegMap sym argTypes)
doGen proxy sym argTypesRepr =
  Crucible.RegMap <$>
    Ctx.generateM
      (Ctx.size argTypesRepr)
      (\index ->
         let typeRepr = argTypesRepr Ctx.! index
         in Crucible.RegEntry typeRepr <$>
              generateMinimalValue
                proxy
                sym
                typeRepr
                (SelectArgument (Some index) Here))

generateMinimalArgs ::
  forall proxy arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  CrucibleTypes.CtxRepr argTypes  {-^ Argument Crucible types -} ->
  Setup sym argTypes (Crucible.RegMap sym argTypes)
generateMinimalArgs proxy sym argTypes = do
  writeLogM ("Generating minimal arguments" :: Text)
  args <- doGen proxy sym argTypes
  logRegMap proxy args
  return args

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
  Constraints argTypes ->
  -- Ctx.Assignment (Const L.Type) init {-^ Argument LLVM types -} ->
  CrucibleTypes.CtxRepr argTypes  {-^ Argument Crucible types -} ->
  m (Either ExecutionSetupError (LLVMMem.MemImpl sym, MapF (What4.SymAnnotation sym) (TypedSelector argTypes), Crucible.RegMap sym argTypes))
setupExecution sym llvmMod moduleTrans _preconds argCrucibleTypes = do
  -- TODO(lb): More lazy here?
  let llvmCtxt = moduleTrans ^. LLVMTrans.transContext
  -- TODO: More lazy?
  mem <-
    let ?lc = llvmCtxt ^. LLVMTrans.llvmTypeCtx
    in liftIO $
         LLVMGlobals.populateAllGlobals sym (LLVMTrans.globalInitMap moduleTrans)
           =<< LLVMGlobals.initializeAllMemory sym llvmCtxt llvmMod
  -- TODO do something with preconds
  Right <$>
    runSetup mem (generateMinimalArgs moduleTrans sym argCrucibleTypes)
