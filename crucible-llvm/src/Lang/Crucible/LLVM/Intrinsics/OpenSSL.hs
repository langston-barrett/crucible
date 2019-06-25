-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.OpenSSL
-- Description      : Override definitions for OpenSSL assembly functions
-- Copyright        : (c) Galois, Inc 2015-2019
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.OpenSSL where

import           Control.Lens ((^.), _1, _2)
import           Control.Monad.Reader
import qualified Text.LLVM.AST as L

import           Data.Parameterized.Context ( pattern (:>), pattern Empty )

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegMap

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Types (pattern SizeT)

import           Lang.Crucible.LLVM.Intrinsics.Common
import           Lang.Crucible.LLVM.Intrinsics.Libc

------------------------------------------------------------------------
-- ** Declarations

-- | In older versions of OpenSSL, this is implemented in assembly, so it never
--   appears in LLVM bitcode files. In later versions, it is replaced with memset:
--   https://github.com/openssl/openssl/commit/104ce8a9f02d250dd43c255eb7b8747e81b29422
--
--   Declaration: @void OPENSSL_cleanse(void *ptr, size_t len);@
--
openSSLCleanseOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
      (EmptyCtx ::> LLVMPointerType wptr
                ::> BVType wptr)
      UnitType
openSSLCleanseOverride =
  let nm = "OPENSSL_cleanse" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType L.Void
    , L.decName    = L.Symbol nm
    -- Note that C's void* becomes i8* in LLVM
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> SizeT)
  UnitRepr
  (\memOps sym args ->
    do let dest = args^._1
       val <- liftIO $
         RegEntry knownRepr <$> bvLit sym knownNat 0
       let len = args^._2
       volatile <- liftIO $
          RegEntry knownRepr <$> bvLit sym knownNat 0
       callMemset sym memOps dest val len volatile
       return ()
  )


