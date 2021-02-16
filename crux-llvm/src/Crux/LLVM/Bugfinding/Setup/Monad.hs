{-
Module       : Crux.LLVM.Bugfinding.Setup.Monad
Description  : Monad for setting up memory and function args.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.Monad
  ( Setup
  , SetupError(..)
  , ppSetupError
  , SetupState
  , SetupAssumption(..)
  , SetupResult(..)
  , setupMem
  , setupMemImpl
  , TypedSelector(..)
  , freshSymbol
  , assume
  , addAnnotation
  , runSetup
  , seekType
  , storableType
  , load
  , malloc
  , store
  ) where

import           Control.Lens (to, (.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Proxy (Proxy(Proxy))
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
import           Data.Parameterized.Some (Some)

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Constraints (Constraint, ppConstraint)
import           Crux.LLVM.Bugfinding.Setup.LocalMem (LocalMem, makeLocalMem, globalMem)
import qualified Crux.LLVM.Bugfinding.Setup.LocalMem as LocalMem
import           Crux.LLVM.Bugfinding.FullType.Type (FullType(FTPtr), FullTypeRepr, ToCrucibleType)

-- TODO unsorted
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Cursor (ppTypeSeekError, TypeSeekError, Selector, Cursor, seekMemType)
import Lang.Crucible.LLVM.MemType (SymType, MemType)
import Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))
import qualified Prettyprinter as PP
import           Prettyprinter (Doc)
import Data.Void (Void)

data TypedSelector arch argTypes tp =
  TypedSelector (Selector arch argTypes) (CrucibleTypes.BaseTypeRepr tp)

data SetupError arch argTypes
  = SetupTypeSeekError (TypeSeekError SymType)
  | SetupTypeTranslationError MemType
  | SetupBadConstraintSelector (Selector arch argTypes) MemType Constraint

ppSetupError :: SetupError arch argTypes -> Doc Void
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

data SetupState arch sym argTypes =
  SetupState
    { _setupMem :: LocalMem arch sym
    , _setupAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector arch argTypes)
      -- ^ This map tracks where a given expression originated from
    , _symbolCounter :: !Int
      -- ^ Counter for generating unique/fresh symbols
    }

makeSetupState :: LLVMMem.MemImpl sym -> SetupState arch sym argTypes
makeSetupState mem = SetupState (makeLocalMem mem) MapF.empty 0

setupMem :: Simple Lens (SetupState arch sym argTypes) (LocalMem arch sym)
setupMem = lens _setupMem (\s v -> s { _setupMem = v })

setupMemImpl :: SetupState arch sym argTypes -> (LLVMMem.MemImpl sym)
setupMemImpl = view (setupMem . globalMem)

setupAnnotations :: Simple Lens (SetupState arch sym argTypes) (MapF (What4.SymAnnotation sym) (TypedSelector arch argTypes))
setupAnnotations = lens _setupAnnotations (\s v -> s { _setupAnnotations = v })

symbolCounter :: Simple Lens (SetupState arch sym argTypes) Int
symbolCounter = lens _symbolCounter (\s v -> s { _symbolCounter = v })

newtype Setup arch sym argTypes a =
  Setup
    (ExceptT
      (SetupError arch argTypes)
      (RWST (Context arch argTypes)
            [SetupAssumption sym]
            (SetupState arch sym argTypes)
            IO)
      a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadError (SetupError arch argTypes) (Setup arch sym argTypes)
deriving instance MonadState (SetupState arch sym argTypes) (Setup arch sym argTypes)
deriving instance MonadReader (Context arch argTypes) (Setup arch sym argTypes)
deriving instance MonadWriter [SetupAssumption sym] (Setup arch sym argTypes)

instance LJ.HasLog Text (Setup arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

data SetupResult arch sym argTypes =
  SetupResult
    { resultMem :: LLVMMem.MemImpl sym
    , resultAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector arch argTypes)
    , resultAssumptions :: [SetupAssumption sym]
    }

runSetup ::
  MonadIO m =>
  Context arch argTypes ->
  LLVMMem.MemImpl sym ->
  Setup arch sym argTypes a ->
  m (Either (SetupError arch argTypes) (SetupResult arch sym argTypes, a))
runSetup context mem (Setup computation) = do
  result <-
    liftIO $
      runRWST (runExceptT computation) context (makeSetupState mem)
  pure $
    case result of
      (Left err, _, _) -> Left err
      (Right result', state, assumptions) ->
        Right ( SetupResult (state ^. to setupMemImpl)
                            (state ^. setupAnnotations)
                            assumptions
              , result'
              )

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
  Selector arch argTypes ->
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

modifyMem ::
  (LocalMem arch sym -> Setup arch sym argTypes (a, LocalMem arch sym)) ->
  Setup arch sym argTypes a
modifyMem f =
  do mem <- gets (view setupMem)
     (val, mem') <- f mem
     setupMem .= mem'
     pure val

_modifyMem_ ::
  (LocalMem arch sym -> Setup arch sym argTypes (LocalMem arch sym)) ->
  Setup arch sym argTypes ()
_modifyMem_ f = modifyMem (fmap ((),) . f)

malloc ::
  forall sym arch argTypes full ft.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr full arch (FTPtr ft) ->
  MemType ->
  (LLVMMem.LLVMPtr sym (ArchWidth arch)) ->
  Setup arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
malloc sym fullTypeRepr memType ptr =
  do context <- ask
     let dl =
           context ^.
             moduleTranslation .
             LLVMTrans.transContext .
             LLVMTrans.llvmTypeCtx .
             to llvmDataLayout
     ptr' <-
       modifyMem $
         \mem ->
           liftIO $ LocalMem.maybeMalloc (Proxy :: Proxy arch) mem ptr sym dl fullTypeRepr memType
     pure ptr'

store ::
  forall arch sym argTypes full ft.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr full arch ft ->
  MemType ->
  Crucible.RegEntry sym (ToCrucibleType ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
store sym fullTypeRepr memType regEntry ptr =
  do storageType <- storableType memType
     modifyMem $
       \mem ->
         liftIO $
           LocalMem.store (Proxy :: Proxy arch) mem sym fullTypeRepr storageType regEntry ptr

load ::
  forall arch sym argTypes full ft.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr full arch ft ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup arch sym argTypes (Maybe (LocalMem.TypedRegEntry arch sym ft))
load sym fullTypeRepr ptr =
  do mem <- gets (view setupMem)
     pure $ LocalMem.load (Proxy :: Proxy arch) mem sym fullTypeRepr ptr
