{-
Module       : Crux.LLVM.Bugfinding.Context
Description  : Global read-only context.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Context
  ( Context(..)
  , ContextError(..)
  , makeContext
  , functionName
  , argumentNames
  , argumentTypes
  , llvmModule
  , moduleTranslation
  ) where

import           Control.Lens (Simple, Lens, lens)
import           Data.Functor.Const (Const(Const, getConst))
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Monoid (getFirst, First(First))
import           Data.Text (Text)
import qualified Data.Text as Text

import           Text.LLVM (Module)
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (fmapFC)

import qualified Lang.Crucible.Types as CrucibleTypes
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)

-- TODO(lb): Split into module-level and function-level?
data Context arch argTypes =
  Context
    { _functionName :: Text
    , _argumentNames :: Ctx.Assignment (Const (Maybe Text)) argTypes
    , _argumentTypes :: CrucibleTypes.CtxRepr argTypes
    , _llvmModule :: Module
    , _moduleTranslation :: ModuleTranslation arch
    }

functionName :: Simple Lens (Context arch argTypes) Text
functionName = lens _functionName (\s v -> s { _functionName = v })

argumentNames :: Simple Lens (Context arch argTypes) (Ctx.Assignment (Const (Maybe Text)) argTypes)
argumentNames = lens _argumentNames (\s v -> s { _argumentNames = v })

argumentTypes :: Simple Lens (Context arch argTypes) (CrucibleTypes.CtxRepr argTypes)
argumentTypes = lens _argumentTypes (\s v -> s { _argumentTypes = v })

llvmModule :: Simple Lens (Context arch argTypes) Module
llvmModule = lens _llvmModule (\s v -> s { _llvmModule = v })

moduleTranslation :: Simple Lens (Context arch argTypes) (ModuleTranslation arch)
moduleTranslation = lens _moduleTranslation (\s v -> s { _moduleTranslation = v })

data ContextError
  = MissingEntrypoint Text
  -- ^ Couldn't find 'L.Define' of entrypoint

-- | This function does some precomputation of ubiquitously used values, and
-- some handling of what should generally be very rare errors.
makeContext ::
  forall arch argTypes.
  Text ->
  CrucibleTypes.CtxRepr argTypes ->
  Module ->
  ModuleTranslation arch ->
  Either ContextError (Context arch argTypes)
makeContext entry argTypes llvmMod trans =
  do def <-
       case List.find ((== L.Symbol (Text.unpack entry)) . L.defName)
                       (L.modDefines llvmMod) of
         Nothing -> Left (MissingEntrypoint entry)
         Just d -> Right d
     pure $
       Context
         { _functionName = entry
         , _argumentTypes = argTypes
         , _argumentNames =
             fmapFC
               (Const . getFirst . getConst)
               (mapToContext
                 (Ctx.size argTypes)
                 (fmap (First . Just) (debugInfoArgNames llvmMod def)))
         , _llvmModule = llvmMod
         , _moduleTranslation = trans
         }

mapToContext ::
  Monoid a =>
  Ctx.Size items ->
  Map Int a ->
  Ctx.Assignment (Const a) items
mapToContext size mp =
  Ctx.generate
    size
    (\index -> Const (Map.findWithDefault mempty (Ctx.indexVal index) mp))

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
              if s == s' then Map.insert (fromIntegral a) (Text.pack n) $ go xs else go xs
            go (_:xs) = go xs
