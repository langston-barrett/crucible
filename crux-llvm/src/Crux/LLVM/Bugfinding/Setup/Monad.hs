{-
Module       : Crux.LLVM.Bugfinding.Setup.Monad
Description  : Monad for setting up memory and function args.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.Monad
  ( Setup
  , SetupState
  , setupMem
  , TypedSelector(..)
  , freshSymbol
  , addAnnotation
  , runSetup
  ) where

import           Control.Lens ((.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Control.Monad.State.Strict (MonadState, StateT, runStateT, gets)
import           Control.Monad.Reader (ReaderT, runReaderT)

import           Text.LLVM.AST (DataLayout)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as What4

import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- TODO unsorted
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Cursor (Selector)
import           Crux.LLVM.Bugfinding.Context
import qualified Lang.Crucible.Backend as Crucible
import Lang.Crucible.LLVM.Extension (ArchWidth)
import Lang.Crucible.LLVM.DataLayout (noAlignment)

data TypedSelector argTypes tp =
  TypedSelector (Selector argTypes) (CrucibleTypes.BaseTypeRepr tp)

data SetupState sym argTypes =
  SetupState
    { _setupMem :: LLVMMem.MemImpl sym
    , _setupAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector argTypes)
      -- ^ This map tracks where a given expression originated from
    , _symbolCounter :: !Int
      -- ^ Counter for generating unique/fresh symbols
    }

setupMem :: Simple Lens (SetupState sym argTypes) (LLVMMem.MemImpl sym)
setupMem = lens _setupMem (\s v -> s { _setupMem = v })

setupAnnotations :: Simple Lens (SetupState sym argTypes) (MapF (What4.SymAnnotation sym) (TypedSelector argTypes))
setupAnnotations = lens _setupAnnotations (\s v -> s { _setupAnnotations = v })

symbolCounter :: Simple Lens (SetupState sym argTypes) Int
symbolCounter = lens _symbolCounter (\s v -> s { _symbolCounter = v })

newtype Setup arch sym argTypes a = Setup (ReaderT (Context arch argTypes) (StateT (SetupState sym argTypes) IO) a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadState (SetupState sym argTypes) (Setup arch sym argTypes)

instance LJ.HasLog Text (Setup arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

runSetup ::
  MonadIO m =>
  Context arch argTypes ->
  LLVMMem.MemImpl sym ->
  Setup arch sym argTypes a ->
  m (LLVMMem.MemImpl sym, MapF (What4.SymAnnotation sym) (TypedSelector argTypes), a)
runSetup context mem (Setup computation) = do
  (result, state) <-
    liftIO $
      runStateT
        (runReaderT computation context)
        (SetupState mem MapF.empty 0)
  pure (state ^. setupMem, state ^. setupAnnotations, result)

freshSymbol :: Setup arch sym argTypes What4.SolverSymbol
freshSymbol =
  do counter <- symbolCounter <+= 1
     pure $ What4.safeSymbol ("fresh" ++ show counter)

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  What4.SymAnnotation sym tp ->
  Selector argTypes ->
  CrucibleTypes.BaseTypeRepr tp ->
  Setup arch sym argTypes ()
addAnnotation ann selector typeRepr =
  setupAnnotations %= MapF.insert ann (TypedSelector selector typeRepr)

-- malloc ::
--   ( Crucible.IsSymInterface sym
--   , ArchOk arch
--   ) =>
--   sym ->
  -- Setup arch sym argTypes (LLVMMem.LLVMPtr _ (ArchWidth arch))
-- malloc sym = error "Unimplemented: malloc"
  -- do mem <- gets (view setupMem)
  --    sizeBv <- error "Unimplemented: malloc"
  --      -- liftIO $ What4.bvLit sym ?ptrWidth (mkBV ?ptrWidth (memTypeSize _ _))
  --    (ptr, mem') <-
  --      liftIO $
  --        LLVMMem.doMalloc
  --          sym
  --          LLVMMem.HeapAlloc  -- TODO(lb): Change based on arg/global
  --          LLVMMem.Mutable  -- TODO(lb): Change based on arg/global
  --          "crux-llvm bugfinding auto-setup"
  --          mem
  --          sizeBv
  --          noAlignment -- TODO is this OK?
  --    setupMem .= mem'
  --    pure ptr

{-
debugInfoArgNames :: LLVM.Module -> LLVM.Define -> Map Int Text
debugInfoArgNames m d =
    case Map.lookup "dbg" $ LLVM.defMetadata d of
          Just (LLVM.ValMdRef s) -> scopeArgs s
              _ -> Map.empty
  where
    scopeArgs :: Int -> Map Int Text
    scopeArgs s = go $ LLVM.modUnnamedMd m
      where go :: [LLVM.UnnamedMd] -> Map Int Text
            go [] = Map.empty
            go (LLVM.UnnamedMd
                 { LLVM.umValues =
                   LLVM.ValMdDebugInfo
                     (LLVM.DebugInfoLocalVariable
                       LLVM.DILocalVariable
                       { LLVM.dilvScope = Just (LLVM.ValMdRef s')
                       , LLVM.dilvArg = a
                       , LLVM.dilvName = Just n
                       })}:xs) =
              if s == s' then Map.insert (fromIntegral a) (Text.pack n) $ go xs else go xs
            go (_:xs) = go xs

stmtDebugDeclares :: [LLVM.Stmt] -> Map Int Location
stmtDebugDeclares [] = Map.empty
stmtDebugDeclares
  (LLVM.Result _
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares
  (LLVM.Effect
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares (_:stmts) = stmtDebugDeclares stmts
-}
