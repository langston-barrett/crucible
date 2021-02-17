{-
Module       : Crux.LLVM.Bugfinding.Context
Description  : Global read-only context.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Crux.LLVM.Bugfinding.Context
  ( Context(..)
  , SomeContext(..)
  , ContextError(..)
  , makeContext
  , functionName
  , moduleTypes
  , argumentNames
  , argumentCrucibleTypes
  , argumentFullTypes
  , argumentMemTypes
  , argumentStorageTypes
  , llvmModule
  , moduleTranslation
  , withTypeContext
  ) where

import           Control.Lens ((^.), Simple, Lens, lens)
import           Data.Functor.Const (Const(Const, getConst))
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Monoid (getFirst, First(First))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))

import           Text.LLVM (Module)
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (forFC, fmapFC, TraversableFC(traverseFC))

import qualified Lang.Crucible.Types as CrucibleTypes
import           Lang.Crucible.LLVM.MemModel (toStorableType, StorageType)
import           Lang.Crucible.LLVM.MemType (fdArgTypes, MemType)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Run (withPtrWidthOf)

import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.FullType.Type (FullTypeRepr, MapToCrucibleType)
import           Crux.LLVM.Bugfinding.FullType.CrucibleType (SomeAssign(..), assignmentToFullType)
import           Crux.LLVM.Bugfinding.FullType.ModuleTypes (ModuleTypes)

data SomeContext arch argTypes'
  = forall m argTypes.
      SomeContext (Context m arch argTypes) (MapToCrucibleType arch argTypes :~: argTypes')

-- TODO(lb): Split into module-level and function-level?
data Context m arch argTypes =
  Context
    { _functionName :: Text
    , _moduleTypes :: ModuleTypes m
    , _argumentFullTypes :: Ctx.Assignment (FullTypeRepr m) argTypes
    , _argumentCrucibleTypes :: CrucibleTypes.CtxRepr (MapToCrucibleType arch argTypes)
    , _argumentMemTypes :: Ctx.Assignment (Const MemType) argTypes
    , _argumentStorageTypes :: Ctx.Assignment (Const StorageType) argTypes
    , _argumentNames :: Ctx.Assignment (Const (Maybe Text)) argTypes
    , _llvmModule :: Module
    , _moduleTranslation :: ModuleTranslation arch
    }

functionName :: Simple Lens (Context m arch argTypes) Text
functionName = lens _functionName (\s v -> s { _functionName = v })

moduleTypes :: Simple Lens (Context m arch argTypes) (ModuleTypes m)
moduleTypes = lens _moduleTypes (\s v -> s { _moduleTypes = v })

argumentNames :: Simple Lens (Context m arch argTypes) (Ctx.Assignment (Const (Maybe Text)) argTypes)
argumentNames = lens _argumentNames (\s v -> s { _argumentNames = v })

argumentCrucibleTypes :: Simple Lens (Context m arch argTypes) (CrucibleTypes.CtxRepr (MapToCrucibleType arch argTypes))
argumentCrucibleTypes = lens _argumentCrucibleTypes (\s v -> s { _argumentCrucibleTypes = v })

argumentFullTypes :: Simple Lens (Context m arch argTypes) (Ctx.Assignment (FullTypeRepr m) argTypes)
argumentFullTypes = lens _argumentFullTypes (\s v -> s { _argumentFullTypes = v })

argumentMemTypes :: Simple Lens (Context m arch argTypes) (Ctx.Assignment (Const MemType) argTypes)
argumentMemTypes = lens _argumentMemTypes (\s v -> s { _argumentMemTypes = v })

argumentStorageTypes :: Simple Lens (Context m arch argTypes) (Ctx.Assignment (Const StorageType) argTypes)
argumentStorageTypes = lens _argumentStorageTypes (\s v -> s { _argumentStorageTypes = v })

llvmModule :: Simple Lens (Context m arch argTypes) Module
llvmModule = lens _llvmModule (\s v -> s { _llvmModule = v })

moduleTranslation :: Simple Lens (Context m arch argTypes) (ModuleTranslation arch)
moduleTranslation = lens _moduleTranslation (\s v -> s { _moduleTranslation = v })

withTypeContext :: Context m arch argTypes -> ((?lc :: TypeContext) => a) -> a
withTypeContext context computation =
  let ?lc = context ^. moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
  in computation


data ContextError
  = MissingEntrypoint Text
  -- ^ Couldn't find 'L.Define' of entrypoint
  | BadLift Text
  -- ^ Couldn't lift types in declaration to 'MemType'
  | BadLiftArgs
  -- ^ Wrong number of arguments after lifting declaration
  | BadMemType MemType
  -- ^ Couldn't lift a 'MemType' to a 'StorageType'
  | FullTypeTranslation L.Ident

-- | This function does some precomputation of ubiquitously used values, and
-- some handling of what should generally be very rare errors.
makeContext ::
  forall arch argTypes.
  ArchOk arch =>
  Text ->
  CrucibleTypes.CtxRepr argTypes ->
  Module ->
  ModuleTranslation arch ->
  Either ContextError (SomeContext arch argTypes)
makeContext entry argTypes llvmMod trans =
  do def <-
       case List.find ((== L.Symbol (Text.unpack entry)) . L.defName)
                       (L.modDefines llvmMod) of
         Nothing -> Left (MissingEntrypoint entry)
         Just d -> Right d
     funDecl <-
       let ?lc = trans ^. LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
       in case LLVMTrans.liftDeclare (LLVMTrans.declareFromDefine def) of
             Left err -> Left (BadLift (Text.pack err))
             Right d -> Right d
     argMemTypes <-
       case maybeMapToContext
              (Ctx.size argTypes)
              (Map.fromList (zip [0..] (fdArgTypes funDecl))) of
         Just types -> Right types
         Nothing -> Left BadLiftArgs
     (SomeAssign
        (argFullTypes :: Ctx.Assignment (FullTypeRepr m) fullTypes)
        (moduleTypes :: ModuleTypes m)
        (Refl :: MapToCrucibleType arch fullTypes :~: argTypes)) <-
       let ?lc = trans ^. LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
       in case assignmentToFullType trans argTypes argMemTypes of
            Right fullTypes -> Right fullTypes
            Left ident -> Left (FullTypeTranslation ident)
     argMemTypes' <-
       case maybeMapToContext
              (Ctx.size argFullTypes)
              (Map.fromList (zip [0..] (fdArgTypes funDecl))) of
         Just types -> Right types
         Nothing -> Left BadLiftArgs
     argStorageTypes <-
       withPtrWidthOf trans $
         forFC
           argMemTypes'
           (\(Const memType) ->
              case toStorableType memType of
                Just storeTy -> Right (Const storeTy)
                Nothing -> Left (BadMemType memType))
     pure $
       SomeContext
         (Context
           { _functionName = entry
           , _moduleTypes = moduleTypes
           , _argumentFullTypes = argFullTypes
           , _argumentCrucibleTypes = argTypes
           , _argumentMemTypes = argMemTypes'
           , _argumentStorageTypes = argStorageTypes
           , _argumentNames =
               fmapFC
                 (Const . getFirst . getConst)
                 (mapToContext
                   (Ctx.size argFullTypes)
                   (fmap (First . Just) (debugInfoArgNames llvmMod def)))
           , _llvmModule = llvmMod
           , _moduleTranslation = trans
           })
         Refl

mapToContext ::
  Monoid a =>
  Ctx.Size items ->
  Map Int a ->
  Ctx.Assignment (Const a) items
mapToContext size mp =
  Ctx.generate
    size
    (\index -> Const (Map.findWithDefault mempty (Ctx.indexVal index) mp))

maybeMapToContext ::
  Ctx.Size items ->
  Map Int a ->
  Maybe (Ctx.Assignment (Const a) items)
maybeMapToContext size mp =
  traverseFC (fmap Const . getConst) $
    Ctx.generate
      size
      (\index -> Const (Map.lookup (Ctx.indexVal index) mp))

-- Stolen shamelessly from saw-script
-- TODO: Does it work though?
debugInfoArgNames :: L.Module -> L.Define -> Map Int Text
debugInfoArgNames m d =
    case Map.lookup "dbg" $ L.defMetadata d of
          Just (L.ValMdRef s) -> scopeArgs s
          _ -> Map.empty
  where
    scopeArgs :: Int -> Map Int Text
    scopeArgs s = go $ L.modUnnamedMd m
      where go :: [L.UnnamedMd] -> Map Int Text
            go [] = Map.empty
            go (L.UnnamedMd
                 { L.umValues =
                   L.ValMdDebugInfo
                     (L.DebugInfoLocalVariable
                       L.DILocalVariable
                       { L.dilvScope = Just (L.ValMdRef s')
                       , L.dilvArg = a
                       , L.dilvName = Just n
                       })}:xs) =
              if s == s' then Map.insert (fromIntegral a - 1) (Text.pack n) $ go xs else go xs
            go (_:xs) = go xs
