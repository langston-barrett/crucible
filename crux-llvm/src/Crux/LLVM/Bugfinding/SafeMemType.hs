{-
Module       : Crux.LLVM.Bugfinding.SafeMemType
Description  : A 'MemType' that is guaranteed to be compatible with a 'CrucibleType'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module Crux.LLVM.Bugfinding.SafeMemType
  ( safeMemType
  , memType
  ) where

import Crux.LLVM.Bugfinding.Errors.Panic (panic)

-- | A 'MemType' that is guaranteed to be compatible with a its 'CrucibleType'
newtype SafeMemType (tp :: CrucibleType) = SafeMemType MemType

safeMemType ::
  (HasPtrWidth wptr, ?lc :: TypeContext) =>
  CrucibleTypes.TypeRepr tp ->
  L.Type ->
  Maybe (SafeMemType tp)
safeMemType typeRepr lvmType =
  case liftMemType llvmType of
    Left _ -> Nothing
    Right memType ->
      do Some typeRepr' <- llvmTypeToRepr memType
         Refl <- testEquality typeRepr typeRepr'
         Just (SafeMemType memType)

memType :: SafeMemType tp -> MemType
memType (SafeMemType memType) = memType
