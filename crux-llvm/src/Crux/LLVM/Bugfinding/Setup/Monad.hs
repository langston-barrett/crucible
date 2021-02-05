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

module Crux.LLVM.Bugfinding.Setup.Monad
  ( Setup
  , SetupState
  , TypedSelector(..)
  , freshSymbol
  , addAnnotation
  , runSetup
  ) where

import           Control.Lens ((%=), (<+=), Simple, Lens, lens, (^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Control.Monad.State.Strict (MonadState, StateT, runStateT)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as What4

import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

import           Crux.LLVM.Bugfinding.Cursor (Selector)

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

newtype Setup sym argTypes a = Setup (StateT (SetupState sym argTypes) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadState (SetupState sym argTypes) (Setup sym argTypes)

instance LJ.HasLog Text (Setup sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

runSetup ::
  MonadIO m =>
  LLVMMem.MemImpl sym ->
  Setup sym argTypes a ->
  m (LLVMMem.MemImpl sym, MapF (What4.SymAnnotation sym) (TypedSelector argTypes), a)
runSetup mem (Setup computation) = do
  (result, state) <- liftIO $ runStateT computation (SetupState mem MapF.empty 0)
  pure (state ^. setupMem, state ^. setupAnnotations, result)

freshSymbol :: Setup sym argTypes What4.SolverSymbol
freshSymbol =
  do counter <- symbolCounter <+= 1
     pure $ What4.safeSymbol ("fresh" ++ show counter)

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  What4.SymAnnotation sym tp ->
  Selector argTypes ->
  CrucibleTypes.BaseTypeRepr tp ->
  Setup sym argTypes ()
addAnnotation ann selector typeRepr =
  setupAnnotations %= MapF.insert ann (TypedSelector selector typeRepr)
