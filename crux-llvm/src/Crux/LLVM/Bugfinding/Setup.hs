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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup
  ( setupExecution
  ) where

import           Control.Lens ((^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Functor.Const (Const(..))
import           Data.Text (Text)
import           Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Globals as LLVMGlobals
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Overrides (ArchOk)

import qualified Lumberjack as LJ
import           Crux.LLVM.Bugfinding.Constraints
import           Crux.LLVM.Bugfinding.Cursor

data ExecutionSetupError = ExecutionSetupError

-- TODO: consider using annotateTerm to identify pointers, integers, etc.

setupExecution ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  , LJ.HasLog Text m
  , MonadIO m
  ) =>
  sym ->
  L.Module ->
  LLVMTrans.ModuleTranslation arch ->
  [Precondition] ->
  -- Ctx.Assignment (Const L.Type) init {-^ Argument LLVM types -} ->
  CrucibleTypes.CtxRepr init  {-^ Argument Crucible types -} ->
  m (Either ExecutionSetupError (Crucible.RegMap sym init, LLVMMem.MemImpl sym))
setupExecution sym llvmMod moduleTrans preconds _argCrucibleTypes = do
  -- TODO(lb): More lazy here?
  let llvmCtxt = moduleTrans ^. LLVMTrans.transContext
  -- TODO: More lazy?
  mem <-
    let ?lc = llvmCtxt ^. LLVMTrans.llvmTypeCtx
    in liftIO $
         LLVMGlobals.populateAllGlobals sym (LLVMTrans.globalInitMap moduleTrans)
           =<< LLVMGlobals.initializeAllMemory sym llvmCtxt llvmMod
  return $ Right (error "Unimplemented: setupExecution", mem)
