{-
Module           : Crux.LLVM.Bugfinding.FullType.ModuleTypes
Description      : A collection of types for a given module
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

See @toFullTypeM@.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Crux.LLVM.Bugfinding.FullType.ModuleTypes
  ( ModuleTypes
  , TypeLookupResult(..)
  , typeContext
  , makeModuleTypes
  , lookupType
  , processingType
  , finishedType
  ) where

import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Some (Some(Some))

import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Crux.LLVM.Bugfinding.FullType.Type (FullTypeRepr(..), FullType)

data ModuleTypes (m :: Type)
  = ModuleTypes
      { typeContext :: TypeContext
      , fullTypes :: Map L.Ident (Maybe (Some (FullTypeRepr m)))
      }

data TypeLookupResult m
  = forall ft. Found (FullTypeRepr m ft)
  | Processing
  | Missing

-- | The existential here makes the @FullType@ API safe.
makeModuleTypes :: TypeContext -> Some ModuleTypes
makeModuleTypes tc = Some (ModuleTypes tc Map.empty)

lookupType :: ModuleTypes m -> L.Ident -> TypeLookupResult m
lookupType (ModuleTypes _ fullTypes) ident =
  case Map.lookup ident fullTypes of
    Nothing -> Missing
    (Just (Just (Some ty))) -> Found ty
    (Just Nothing) -> Processing

finishedType :: ModuleTypes m -> L.Ident -> Some (FullTypeRepr m) -> ModuleTypes m
finishedType (ModuleTypes tc fullTypes) ident ty =
  ModuleTypes tc (Map.insert ident (Just ty) fullTypes)

processingType :: ModuleTypes m -> L.Ident -> ModuleTypes m
processingType (ModuleTypes tc fullTypes) ident =
  ModuleTypes tc (Map.insert ident Nothing fullTypes)
