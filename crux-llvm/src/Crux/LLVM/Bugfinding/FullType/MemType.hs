{-
Module           : Crux.LLVM.Bugfinding.FullType.MemType
Description      : Interop between 'FullType' and 'MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Crux.LLVM.Bugfinding.FullType.MemType
  ( toMemType
  , toMemType'
  ) where

import           Data.Functor.Const (Const(Const))

import           Data.Parameterized.NatRepr (natValue)

import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))

import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.FullType.Type (FullTypeRepr(..), Full(Full))

toMemType :: FullTypeRepr 'Full arch ft -> MemType
toMemType =
  \case
    FTIntRepr _ natRepr -> IntType (natValue natRepr)
    FTPtrRepr _ _ ftRepr ->
      case toMemType' ftRepr of
        Left symType -> PtrType symType
        Right memType -> PtrType (MemType memType)
    FTArrayRepr _ natRepr fullTypeRepr ->
      ArrayType (natValue natRepr) (toMemType fullTypeRepr)
    FTFullStructRepr _ structInfo _ -> StructType structInfo

toMemType' :: FullTypeRepr full arch ft -> Either SymType MemType
toMemType' =
  \case
    FTIntRepr _ natRepr -> Right $ IntType (natValue natRepr)
    FTPtrRepr _ _ ftRepr ->
      case toMemType' ftRepr of
        Left symType -> Right (PtrType symType)
        Right memType -> Right (PtrType (MemType memType))
    FTArrayRepr _ natRepr fullTypeRepr ->
      case toMemType' fullTypeRepr of
        Left symType ->
          panic "toMemType" ["Impossible: Alias can't appear directly in Array"]
        Right memType -> Right (ArrayType (natValue natRepr) memType)
    FTFullStructRepr _ structInfo _ -> Right (StructType structInfo)
    FTPartStructRepr structInfo _ -> Right (StructType structInfo)
    FTAliasRepr (Const ident) -> Left (Alias ident)
