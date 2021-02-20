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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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
  , getAnnotation
  , annotatePointer
  , runSetup
  , storableType
  , load
  , malloc
  , store
  ) where

import           Control.Lens (to, (.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Control.Monad.Except (throwError, ExceptT, MonadError, runExceptT)
import           Control.Monad.Reader (MonadReader, ask)
import           Control.Monad.State.Strict (MonadState, gets)
import           Control.Monad.Writer (MonadWriter, tell)
import           Control.Monad.RWS (RWST, runRWST)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Constraints (Constraint)
import           Crux.LLVM.Bugfinding.Setup.LocalMem (LocalMem, makeLocalMem, globalMem)
import qualified Crux.LLVM.Bugfinding.Setup.LocalMem as LocalMem
import           Crux.LLVM.Bugfinding.FullType.Type (FullType(FTPtr), FullTypeRepr, ToCrucibleType, ToBaseType)
import           Crux.LLVM.Bugfinding.FullType.MemType (toMemType)

-- TODO unsorted
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Cursor (ppTypeSeekError, TypeSeekError, Selector, SomeInSelector(..))
import Lang.Crucible.LLVM.MemType (SymType, MemType)
import Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))
import qualified Prettyprinter as PP
import           Prettyprinter (Doc)
import Data.Void (Void)

data TypedSelector m arch argTypes ft =
  TypedSelector (FullTypeRepr m ft) (SomeInSelector m argTypes ft)

data SetupError m arch argTypes
  = SetupTypeSeekError (TypeSeekError SymType)
  | SetupTypeTranslationError MemType

ppSetupError :: SetupError m arch argTypes -> Doc Void
ppSetupError =
  \case
    SetupTypeSeekError typeSeekError -> ppTypeSeekError typeSeekError
    SetupTypeTranslationError memType ->
      PP.pretty ("Couldn't translate MemType" :: Text) <> PP.viaShow memType

data SetupAssumption m sym
  = SetupAssumption
      { assumptionReason :: Some (Constraint m)
      , assumptionPred :: What4.Pred sym
      }

data SetupState m arch sym argTypes =
  SetupState
    { _setupMem :: LocalMem m arch sym
    , _setupAnnotations :: Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))
      -- ^ This map tracks where a given expression originated from
    , _symbolCounter :: !Int
      -- ^ Counter for generating unique/fresh symbols
    }

makeSetupState :: LLVMMem.MemImpl sym -> SetupState m arch sym argTypes
makeSetupState mem = SetupState (makeLocalMem mem) Map.empty 0

setupMem :: Simple Lens (SetupState m arch sym argTypes) (LocalMem m arch sym)
setupMem = lens _setupMem (\s v -> s { _setupMem = v })

setupMemImpl :: SetupState m arch sym argTypes -> (LLVMMem.MemImpl sym)
setupMemImpl = view (setupMem . globalMem)

setupAnnotations :: Simple Lens (SetupState m arch sym argTypes) (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))
setupAnnotations = lens _setupAnnotations (\s v -> s { _setupAnnotations = v })

symbolCounter :: Simple Lens (SetupState m arch sym argTypes) Int
symbolCounter = lens _symbolCounter (\s v -> s { _symbolCounter = v })

newtype Setup m arch sym argTypes a =
  Setup
    (ExceptT
      (SetupError m arch argTypes)
      (RWST (Context m arch argTypes)
            [SetupAssumption m sym]
            (SetupState m arch sym argTypes)
            IO)
      a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadError (SetupError m arch argTypes) (Setup m arch sym argTypes)
deriving instance MonadState (SetupState m arch sym argTypes) (Setup m arch sym argTypes)
deriving instance MonadReader (Context m arch argTypes) (Setup m arch sym argTypes)
deriving instance MonadWriter [SetupAssumption m sym] (Setup m arch sym argTypes)

instance LJ.HasLog Text (Setup m arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

data SetupResult m arch sym argTypes =
  SetupResult
    { resultMem :: LLVMMem.MemImpl sym
    , resultAnnotations :: Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))
    , resultAssumptions :: [SetupAssumption m sym]
    }

runSetup ::
  MonadIO f =>
  Context m arch argTypes ->
  LLVMMem.MemImpl sym ->
  Setup m arch sym argTypes a ->
  f (Either (SetupError m arch argTypes) (SetupResult m arch sym argTypes, a))
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

freshSymbol :: Setup m arch sym argTypes What4.SolverSymbol
freshSymbol =
  do counter <- symbolCounter <+= 1
     pure $ What4.safeSymbol ("fresh" ++ show counter)

assume ::
  Constraint m ty ->
  What4.Pred sym ->
  Setup m arch sym argTypes ()
assume constraint predicate = tell [SetupAssumption (Some constraint) predicate]

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  Some (What4.SymAnnotation sym) ->
  Selector m argTypes inTy atTy {-^ Path to this value -} ->
  FullTypeRepr m atTy ->
  Setup m arch sym argTypes ()
addAnnotation ann selector fullTypeRepr =
  setupAnnotations %=
    Map.insert ann (Some (TypedSelector fullTypeRepr (SomeInSelector selector)))

-- | Retrieve a pre-existing annotation, or make a new one.
getAnnotation ::
  Crucible.IsSymInterface sym =>
  sym ->
  Selector m argTypes inTy atTy {-^ Path to this value -} ->
  FullTypeRepr m atTy ->
  What4.SymExpr sym (ToBaseType arch atTy) ->
  Setup m arch sym argTypes ( What4.SymAnnotation sym (ToBaseType arch atTy)
                            , What4.SymExpr sym (ToBaseType arch atTy)
                            )
getAnnotation sym selector fullTypeRepr expr =
  case What4.getAnnotation sym expr of
    Just annotation ->
      do addAnnotation (Some annotation) selector fullTypeRepr
         pure (annotation, expr)
    Nothing ->
      do (annotation, expr') <- liftIO $ What4.annotateTerm sym expr
         addAnnotation (Some annotation) selector fullTypeRepr
         pure (annotation, expr')

annotatePointer ::
  Crucible.IsSymInterface sym =>
  sym ->
  Selector m argTypes inTy atTy {-^ Path to this pointer -} ->
  FullTypeRepr m atTy ->
  LLVMMem.LLVMPtr sym w ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym w)
annotatePointer sym selector fullTypeRepr ptr =
  do let block = LLVMPtr.llvmPointerBlock ptr
     ptr' <-
       case What4.getAnnotation sym block of
         Just annotation ->
           do addAnnotation (Some annotation) selector fullTypeRepr
              pure ptr
         Nothing ->
           do (annotation, ptr') <- liftIO (LLVMPtr.annotatePointerBlock sym ptr)
              addAnnotation (Some annotation) selector fullTypeRepr
              pure ptr'
     let offset = LLVMPtr.llvmPointerOffset ptr'
     ptr'' <-
       case What4.getAnnotation sym offset of
         Just annotation ->
           do addAnnotation (Some annotation) selector fullTypeRepr
              pure ptr'
         Nothing ->
           do (annotation, ptr'') <- liftIO (LLVMPtr.annotatePointerOffset sym ptr)
              addAnnotation (Some annotation) selector fullTypeRepr
              pure ptr''
     pure ptr''

storableType :: ArchOk arch => MemType -> Setup m arch sym argTypes LLVMMem.StorageType
storableType memType =
  maybe (throwError (SetupTypeTranslationError memType)) pure (LLVMMem.toStorableType memType)

modifyMem ::
  (LocalMem m arch sym -> Setup m arch sym argTypes (a, LocalMem m arch sym)) ->
  Setup m arch sym argTypes a
modifyMem f =
  do mem <- gets (view setupMem)
     (val, mem') <- f mem
     setupMem .= mem'
     pure val

_modifyMem_ ::
  (LocalMem m arch sym -> Setup m arch sym argTypes (LocalMem m arch sym)) ->
  Setup m arch sym argTypes ()
_modifyMem_ f = modifyMem (fmap ((),) . f)

malloc ::
  forall m sym arch argTypes inTy atTy.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr m ('FTPtr atTy) ->
  Selector m argTypes inTy ('FTPtr atTy) {-^ Path to this pointer -} ->
  (LLVMMem.LLVMPtr sym (ArchWidth arch)) ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
malloc sym fullTypeRepr selector ptr =
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
           liftIO $ LocalMem.maybeMalloc (Proxy :: Proxy arch) mem ptr sym dl fullTypeRepr
     annotatePointer sym selector fullTypeRepr ptr'

store ::
  forall m arch sym argTypes ft.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr m ft ->
  Crucible.RegEntry sym (ToCrucibleType arch ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
store sym fullTypeRepr regEntry ptr =
  do storageType <- storableType (toMemType fullTypeRepr)
     modifyMem $
       \mem ->
         liftIO $
           LocalMem.store (Proxy :: Proxy arch) mem sym fullTypeRepr storageType regEntry ptr

load ::
  forall m arch sym argTypes ft.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  sym ->
  FullTypeRepr m ft ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup m arch sym argTypes (Maybe (LocalMem.TypedRegEntry m arch sym ft))
load sym fullTypeRepr ptr =
  do mem <- gets (view setupMem)
     pure $ LocalMem.load (Proxy :: Proxy arch) mem sym fullTypeRepr ptr
