{-
Module       : Crux.LLVM.Bugfinding.Setup.Monad
Description  : Monad for setting up memory and function args.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.Monad
  ( Setup
  , SetupError(..)
  , ppSetupError
  , SetupState
  , SetupAssumption(..)
  , SetupResult(..)
  , setupMem
  , modifyMem
  , TypedSelector(..)
  , freshSymbol
  , assume
  , addAnnotation
  , runSetup
  , seekType
  , storableType
  , malloc
  ) where

import           Control.Lens (to, (.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Control.Monad.Except (throwError, ExceptT, MonadError, runExceptT)
import           Control.Monad.Reader (MonadReader, ask)
import           Control.Monad.State.Strict (MonadState, gets)
import           Control.Monad.Writer (MonadWriter, tell)
import           Control.Monad.RWS (RWST, runRWST)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Constraints (Constraint, ppConstraint)

-- TODO unsorted
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Cursor (ppTypeSeekError, TypeSeekError, Selector, Cursor, seekMemType)
import Lang.Crucible.LLVM.DataLayout (maxAlignment)
import Data.BitVector.Sized (mkBV)
import Lang.Crucible.LLVM.MemType (SymType, MemType, memTypeSize)
import Lang.Crucible.LLVM.Bytes (bytesToInteger)
import Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))
import qualified Prettyprinter as PP
import           Prettyprinter (Doc)
import Data.Void (Void)

data TypedSelector argTypes tp =
  TypedSelector (Selector argTypes) (CrucibleTypes.BaseTypeRepr tp)

data SetupError argTypes
  = SetupTypeSeekError (TypeSeekError SymType)
  | SetupTypeTranslationError MemType
  | SetupBadConstraintSelector (Selector argTypes) MemType Constraint

ppSetupError :: SetupError argTypes -> Doc Void
ppSetupError =
  \case
    SetupTypeSeekError typeSeekError -> ppTypeSeekError typeSeekError
    SetupTypeTranslationError memType ->
      PP.pretty ("Couldn't translate MemType" :: Text) <> PP.viaShow memType
    SetupBadConstraintSelector _selector memType constraint ->
      PP.nest 2 $
        PP.vsep
          -- TODO print selector too
          [ PP.pretty ("Can't apply this constraint at this selector" :: Text)
          , "Type: " <> PP.viaShow memType
          , "Constraint: " <> ppConstraint constraint
          ]

data SetupAssumption sym
  = SetupAssumption
      { assumptionReason :: Constraint
      , assumptionPred :: What4.Pred sym
      }

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

newtype Setup arch sym argTypes a =
  Setup
    (ExceptT
      (SetupError argTypes)
      (RWST (Context arch argTypes)
            [SetupAssumption sym]
            (SetupState sym argTypes)
            IO)
      a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadError (SetupError argTypes) (Setup arch sym argTypes)
deriving instance MonadState (SetupState sym argTypes) (Setup arch sym argTypes)
deriving instance MonadReader (Context arch argTypes) (Setup arch sym argTypes)
deriving instance MonadWriter [SetupAssumption sym] (Setup arch sym argTypes)

instance LJ.HasLog Text (Setup arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

data SetupResult sym argTypes =
  SetupResult
    { resultMem :: LLVMMem.MemImpl sym
    , resultAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector argTypes)
    , resultAssumptions :: [SetupAssumption sym]
    }

runSetup ::
  MonadIO m =>
  Context arch argTypes ->
  LLVMMem.MemImpl sym ->
  Setup arch sym argTypes a ->
  m (Either (SetupError argTypes) (SetupResult sym argTypes, a))
runSetup context mem (Setup computation) = do
  result <-
    liftIO $
      runRWST (runExceptT computation) context (SetupState mem MapF.empty 0)
  pure $
    case result of
      (Left err, _, _) -> Left err
      (Right result', state, assumptions) ->
        Right ( SetupResult (state ^. setupMem)
                            (state ^. setupAnnotations)
                            assumptions
              , result'
              )

modifyMem ::
  (LLVMMem.MemImpl sym -> Setup arch sym argTypes (LLVMMem.MemImpl sym)) ->
  Setup arch sym argTypes ()
modifyMem f =
  do mem <- gets (view setupMem)
     mem' <- f mem
     setupMem .= mem'

freshSymbol :: Setup arch sym argTypes What4.SolverSymbol
freshSymbol =
  do counter <- symbolCounter <+= 1
     pure $ What4.safeSymbol ("fresh" ++ show counter)

assume ::
  Constraint ->
  What4.Pred sym ->
  Setup arch sym argTypes ()
assume constraint predicate = tell [SetupAssumption constraint predicate]

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  What4.SymAnnotation sym tp ->
  Selector argTypes ->
  CrucibleTypes.BaseTypeRepr tp ->
  Setup arch sym argTypes ()
addAnnotation ann selector typeRepr =
  setupAnnotations %= MapF.insert ann (TypedSelector selector typeRepr)

seekType ::
  Cursor ->
  MemType ->
  Setup arch sym argTypes MemType
seekType cursor memType =
  do context <- ask
     withTypeContext context $
       either (throwError . SetupTypeSeekError) pure (seekMemType cursor memType)

storableType :: ArchOk arch => MemType -> Setup arch sym argTypes LLVMMem.StorageType
storableType memType =
  maybe (throwError (SetupTypeTranslationError memType)) pure (LLVMMem.toStorableType memType)

malloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  sym ->
  MemType ->
  Setup arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
malloc sym memType =
  do context <- ask
     mem <- gets (view setupMem)
     let dl =
           context ^.
             moduleTranslation .
             LLVMTrans.transContext .
             LLVMTrans.llvmTypeCtx .
             to llvmDataLayout
     (ptr, mem') <-
       liftIO $
         do sizeBv <-
              What4.bvLit
                sym
                ?ptrWidth
                (mkBV ?ptrWidth (bytesToInteger (memTypeSize dl memType)))
            LLVMMem.doMalloc
              sym
              LLVMMem.HeapAlloc  -- TODO(lb): Change based on arg/global
              LLVMMem.Mutable  -- TODO(lb): Change based on arg/global
              "crux-llvm bugfinding auto-setup"
              mem
              sizeBv
              (maxAlignment dl) -- TODO is this OK?
     setupMem .= mem'
     pure ptr
