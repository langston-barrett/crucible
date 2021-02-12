{-
Module       : Crux.LLVM.Bugfinding.Setup
Description  : Setting up memory and function args according to preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Bugfinding.Setup
  ( setupExecution
  , logRegMap
  , SetupAssumption(SetupAssumption)
  , SetupResult(SetupResult)
  ) where

import           Control.Lens (to, (^.), (%~))
import           Control.Monad (void)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Function ((&))
import           Data.Text (Text)

import           Lumberjack (HasLog, writeLogM)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Globals as LLVMGlobals
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans


import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.Constraints
import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Cursor
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.Setup.Monad

-- TODO unsorted
import Data.Proxy (Proxy(Proxy))
import qualified Data.Text as Text
import Data.Functor.Const (Const(getConst))
import Control.Monad.State (gets)
import Data.Parameterized.Classes (IxedF'(ixF'))
import Prettyprinter (Doc)
import Lang.Crucible.LLVM.MemType (MemType(PtrType))
import Data.Maybe (fromMaybe)
import Control.Monad.Error.Class (MonadError(throwError))
import Lang.Crucible.LLVM.TypeContext (asMemType)
import Lang.Crucible.LLVM.Extension (ArchWidth)

ppRegValue ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  LLVMMem.StorageType ->
  Crucible.RegEntry sym tp ->
  IO (Doc ann)
ppRegValue _proxy sym mem storageType (Crucible.RegEntry typeRepr regValue) =
  do val <-
       liftIO $
         LLVMMem.packMemValue sym storageType typeRepr regValue
     pure $
       LLVMMem.ppLLVMValWithGlobals
         sym
         (LLVMMem.memImplSymbolMap mem)
         val

logRegMap ::
  forall m arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  , MonadIO m
  , HasLog Text m
  ) =>
  Context arch argTypes ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegMap sym argTypes ->
  m ()
logRegMap context sym mem (Crucible.RegMap regmap) =
  Ctx.traverseWithIndex_
    (\index regEntry ->
      do let storageType =
               context ^. argumentStorageTypes . ixF' index . to getConst
         arg <-
           liftIO $
             ppRegValue (Proxy :: Proxy arch) sym mem storageType regEntry
         writeLogM $
           Text.unwords
             [ "Argument #" <> Text.pack (show (Ctx.indexVal index))
             , fromMaybe "" (context ^. argumentNames . ixF' index . to getConst) <> ":"
             , Text.pack (show arg)
             -- , "(type:"
             -- , Text.pack (show (Crucible.regType arg)) <> ")"
             ])
    regmap


annotatedTerm ::
  forall arch sym tp argTypes.
  (Crucible.IsSymInterface sym) =>
  sym ->
  CrucibleTypes.BaseTypeRepr tp ->
  Selector argTypes ->
  Setup arch sym argTypes (What4.SymExpr sym tp)
annotatedTerm sym typeRepr selector =
  do symbol <- freshSymbol
      -- TODO(lb): Is freshConstant correct here?
     (annotation, expr) <-
        liftIO $ What4.annotateTerm sym =<< What4.freshConstant sym symbol typeRepr
     addAnnotation annotation selector typeRepr
     pure expr

generateMinimalValue ::
  forall proxy sym arch tp argTypes.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  sym ->
  CrucibleTypes.TypeRepr tp ->
  Selector argTypes {-^ Path to this value -} ->
  Setup arch sym argTypes (Crucible.RegValue sym tp)
generateMinimalValue proxy sym typeRepr selector =
  case CrucibleTypes.asBaseType typeRepr of
    CrucibleTypes.AsBaseType baseTypeRepr ->
      annotatedTerm sym baseTypeRepr selector
    CrucibleTypes.NotBaseType ->
      case typeRepr of
        CrucibleTypes.UnitRepr -> return ()
        CrucibleTypes.AnyRepr ->
          -- TODO(lb): Should be made more complex
          return $ Crucible.AnyValue CrucibleTypes.UnitRepr ()
        LLVMMem.LLVMPointerRepr w ->
          do liftIO . LLVMMem.llvmPointer_bv sym =<<
                annotatedTerm sym (CrucibleTypes.BaseBVRepr w) selector
        CrucibleTypes.VectorRepr _containedTypeRepr ->
          -- TODO(lb): These are fixed size. What size should we generate?
          unin "Generating values of vector types"
        CrucibleTypes.StructRepr types ->
          Ctx.generateM
            (Ctx.size types)
            (\idx ->
               Crucible.RV <$>
                 -- TODO(lb): This selector is wrong
                 generateMinimalValue  proxy sym (types Ctx.! idx) selector)
        _ -> unin ("Generating values of this type: " ++ show typeRepr)
  where unin = unimplemented "generateMinimalValue"

generateMinimalArgs ::
  forall arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  Setup arch sym argTypes (Crucible.RegMap sym argTypes)
generateMinimalArgs context sym = do
  writeLogM $ "Generating minimal arguments for " <>
                context ^. functionName
  let argTypesRepr = context ^. argumentTypes
  args <-
    Crucible.RegMap <$>
      Ctx.generateM
        (Ctx.size argTypesRepr)
        (\index ->
          let typeRepr = argTypesRepr Ctx.! index
          in Crucible.RegEntry typeRepr <$>
                generateMinimalValue
                  (Proxy :: Proxy arch)
                  sym
                  typeRepr
                  (SelectArgument (Some index) Here))
  mem <- gets setupMemImpl
  logRegMap context sym mem args
  return args

-- | If this pointer already points to initialized memory, then just return the
-- value. Otherwise, allocate some memory and initialize it with a fresh, minimal
-- value.
--
-- TODO: Allow for array initialization
initialize ::
  forall arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  MemType ->
  Selector argTypes {-^ Top-level selector -} ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch), Some (Crucible.RegEntry sym))
initialize context sym pointedToType selector pointer =
  load sym pointer >>=
    \case
      Just val -> pure (pointer, val)
      Nothing ->
        withTypeContext context $
          LLVMTrans.llvmTypeAsRepr
            pointedToType
            (\tp ->  -- the Crucible type being pointed at
              do ptr <- malloc sym pointedToType pointer
                 pointedToVal <-
                   generateMinimalValue
                     (Proxy :: Proxy arch)
                     sym
                     tp
                     (selector & selectorCursor %~ Dereference)
                 ptr' <-
                   store sym pointedToType (Crucible.RegEntry tp pointedToVal) ptr
                 pure (ptr', Some (Crucible.RegEntry tp pointedToVal)))

constrainHere ::
  forall arch sym argTypes tp.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  Selector argTypes {-^ Top-level selector -} ->
  Constraint ->
  MemType ->
  Crucible.RegEntry sym tp ->
  Setup arch sym argTypes (Crucible.RegEntry sym tp)
constrainHere context sym selector constraint memType regEntry@(Crucible.RegEntry typeRepr regValue) =
  case constraint of
    Allocated ->
      case typeRepr of
        LLVMMem.PtrRepr ->
          Crucible.RegEntry typeRepr <$> malloc sym memType regValue
        _ -> throwError (SetupBadConstraintSelector selector memType constraint)
    Aligned alignment ->
      case typeRepr of
        LLVMMem.PtrRepr ->
          do assume constraint =<<
               liftIO (LLVMMem.isAligned sym ?ptrWidth regValue alignment)
             pure regEntry
        _ -> throwError (SetupBadConstraintSelector selector memType constraint)
    Initialized ->
      withTypeContext context $
        case (typeRepr, memType) of
          (LLVMMem.PtrRepr, PtrType (asMemType -> Right pointedToType)) ->
            do (ptr, _freshVal) <-
                 -- TODO(lb): This selector is wrong
                 initialize context sym pointedToType selector regValue
               pure $ Crucible.RegEntry typeRepr ptr
          _ -> throwError (SetupBadConstraintSelector selector memType constraint)
    _ -> unimplemented "constrainHere" ("Constraint:" ++ show (ppConstraint constraint))

constrainValue ::
  forall arch sym argTypes tp.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  Constraint ->
  Selector argTypes {-^ Parent selector for the cursor -} ->
  Cursor ->
  MemType {-^ The \"leaf\" 'MemType', passed directly to 'constrainHere' -} ->
  Crucible.RegEntry sym tp ->
  Setup arch sym argTypes (Crucible.RegEntry sym tp)
constrainValue context sym constraint selector cursor memType regEntry@(Crucible.RegEntry typeRepr regValue) =
  case cursor of
    Here -> constrainHere context sym selector constraint memType regEntry
    Dereference cursor' ->
      case typeRepr of
        LLVMMem.PtrRepr ->
          do -- If there's already a value behind this pointer, constrain that.
             -- Otherwise, allocate new memory, put a fresh value there, and constrain
             -- that.
             (ptr, Some pointedToValue) <-
               initialize context sym memType selector regValue
             void $ constrainValue context sym constraint selector cursor' memType pointedToValue
             pure $ Crucible.RegEntry typeRepr ptr
        _ -> throwError (SetupBadConstraintSelector selector memType constraint)
    _ -> unimplemented "constrainValue" "Non-top-level cursors"

constrainOneArgument ::
  forall arch sym argTypes tp.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  [ValueConstraint] ->
  Some (Ctx.Index argTypes) ->
  Crucible.RegEntry sym tp ->
  Setup arch sym argTypes (Crucible.RegEntry sym tp)
constrainOneArgument context sym constraints sidx@(Some idx) regEntry =
  -- TODO fold
  case constraints of
    [] -> pure regEntry
    (vc@(ValueConstraint constraint cursor):rest) ->
      do memType <-
           seekType cursor (context ^. argumentMemTypes . ixF' idx . to getConst)
         writeLogM ("Satisfying constraint: " <> Text.pack (show (ppValueConstraint vc)))
         constrainOneArgument context sym rest sidx
           =<< constrainValue
                 context
                 sym
                 constraint
                 (SelectArgument sidx cursor)
                 cursor
                 memType
                 regEntry

constrain ::
  forall arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context arch argTypes ->
  sym ->
  Constraints argTypes ->
  Crucible.RegMap sym argTypes ->
  Setup arch sym argTypes (Crucible.RegMap sym argTypes)
constrain context sym preconds (Crucible.RegMap args) =
  do writeLogM ("Establishing preconditions..." :: Text)
     args' <-
       Ctx.traverseWithIndex
         (\idx regEntry ->
            do writeLogM ("Modifying argument #" <> Text.pack (show (Ctx.indexVal idx)))
               constrainOneArgument
                 context
                 sym
                 (getConst (argConstraints preconds Ctx.! idx))
                 (Some idx)
                 regEntry)
         args
     return (Crucible.RegMap args')

setupExecution ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  , HasLog Text m
  , MonadIO m
  ) =>
  sym ->
  Context arch argTypes ->
  Constraints argTypes ->
  m (Either (SetupError argTypes) (SetupResult arch sym argTypes, Crucible.RegMap sym argTypes))
setupExecution sym context preconds = do
  -- TODO(lb): More lazy here?
  let moduleTrans = context ^. moduleTranslation
  let llvmCtxt = moduleTrans ^. LLVMTrans.transContext
  -- TODO: More lazy?
  mem <-
    withTypeContext context $
      liftIO $
        LLVMGlobals.populateAllGlobals sym (LLVMTrans.globalInitMap moduleTrans)
          =<< LLVMGlobals.initializeAllMemory sym llvmCtxt (context ^. llvmModule)
  runSetup context mem (constrain context sym preconds =<<
                          generateMinimalArgs context sym)
