{-
Module       : Crux.LLVM.Bugfinding.Setup
Description  : Setting up memory and function args according to preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
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
import           Control.Monad (void, unless)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Function ((&))
import           Data.Functor.Const (Const(Const, getConst))
import           Data.Functor.Compose (Compose(getCompose))
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Type.Equality ((:~:)(Refl), testEquality)

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
import           Crux.LLVM.Bugfinding.FullType.CrucibleType (SomeIndex(..), translateIndex, generateM, toCrucibleType)
import qualified Crux.LLVM.Bugfinding.FullType.CrucibleType as FTCT
import           Crux.LLVM.Bugfinding.FullType.Type (FullType(FTPtr), ToCrucibleType, MapToCrucibleType, ToBaseType, FullTypeRepr(..))
import           Crux.LLVM.Bugfinding.FullType.MemType (asFullType, toMemType)
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.Setup.Monad
import           Crux.LLVM.Bugfinding.Setup.LocalMem (TypedRegEntry(..))

-- TODO unsorted
import Data.Proxy (Proxy(Proxy))
import qualified Data.Text as Text
import Control.Monad.State (gets)
import Data.Parameterized.Classes (IxedF'(ixF'))
import Prettyprinter (Doc)
import Data.Maybe (fromMaybe)
import Control.Monad.Error.Class (MonadError(throwError))
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
  forall f m arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  , MonadIO f
  , HasLog Text f
  ) =>
  Context m arch argTypes ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) ->
  f ()
logRegMap context sym mem (Crucible.RegMap regmap) =
  Ctx.traverseWithIndex_
    (\index (Const storageType) ->
       case translateIndex (Proxy :: Proxy arch) (Ctx.size (context ^. argumentStorageTypes)) index of
         SomeIndex idx Refl ->
           do let regEntry = regmap Ctx.! idx
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
    (context ^. argumentStorageTypes)


annotatedTerm ::
  forall m arch sym inTy atTy argTypes.
  (Crucible.IsSymInterface sym) =>
  sym ->
  FullTypeRepr m atTy ->
  CrucibleTypes.BaseTypeRepr (ToBaseType arch atTy) ->
  Selector m argTypes inTy atTy {-^ Path to this value -} ->
  Setup m arch sym argTypes (What4.SymExpr sym (ToBaseType arch atTy))
annotatedTerm sym fullTypeRepr baseTypeRepr selector =
  do symbol <- freshSymbol
      -- TODO(lb): Is freshConstant correct here?
     (annotation, expr) <-
        liftIO $ What4.annotateTerm sym =<< What4.freshConstant sym symbol baseTypeRepr
     addAnnotation annotation selector fullTypeRepr baseTypeRepr
     pure expr

generateMinimalValue ::
  forall proxy m sym arch inTy atTy argTypes.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  sym ->
  FullTypeRepr m atTy ->
  Selector m argTypes inTy atTy {-^ Path to this value -} ->
  Setup m arch sym argTypes (Crucible.RegValue sym (ToCrucibleType arch atTy))
generateMinimalValue proxy sym fullTypeRepr selector =
  case fullTypeRepr of
    FTPtrRepr _fullTypeRepr' ->
      do liftIO . LLVMMem.llvmPointer_bv sym =<<
            annotatedTerm sym fullTypeRepr (CrucibleTypes.BaseBVRepr ?ptrWidth) selector
    -- CrucibleTypes.VectorRepr _containedTypeRepr ->
    --   -- TODO(lb): These are fixed size. What size should we generate?
    --   unin "Generating values of vector types"
    FTIntRepr w ->
      do liftIO . LLVMMem.llvmPointer_bv sym =<<
            annotatedTerm sym fullTypeRepr (CrucibleTypes.BaseBVRepr w) selector
    FTStructRepr _ (fields :: Ctx.Assignment (FullTypeRepr m) fieldTypes) ->
      do let
           convert ::
             forall ft.
             Ctx.Index fieldTypes ft ->
             FullTypeRepr m ft ->
             Setup m arch sym argTypes (Crucible.RegValue' sym (ToCrucibleType arch ft))
           convert idx ftRepr =
             Crucible.RV <$>
              generateMinimalValue proxy sym ftRepr
                (selector & selectorCursor %~ \cursor -> Field fields idx cursor)
         FTCT.SomeAssign' _ Refl fieldVals <-
           FTCT.assignmentToCrucibleTypeA proxy convert fields
         pure fieldVals
    _ -> unin ("Generating values of this type: " ++ show (toMemType fullTypeRepr))
  where unin = unimplemented "generateMinimalValue"

generateMinimalArgs ::
  forall m arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  Setup m arch sym argTypes (Crucible.RegMap sym (MapToCrucibleType arch argTypes))
generateMinimalArgs context sym = do
  writeLogM $ "Generating minimal arguments for " <>
                context ^. functionName
  let argTypesRepr = context ^. argumentCrucibleTypes
  args <-
    Crucible.RegMap <$>
      generateM
        (Proxy :: Proxy arch)
        (Ctx.size (context ^. argumentFullTypes))
        (\index _index' Refl ->
           case translateIndex (Proxy :: Proxy arch) (Ctx.size (context ^. argumentFullTypes)) index of
             SomeIndex index' Refl ->
              let typeRepr = argTypesRepr Ctx.! index'
                  ft = context ^. argumentFullTypes . ixF' index
              in Crucible.RegEntry typeRepr <$>
                    generateMinimalValue
                      (Proxy :: Proxy arch)
                      sym
                      ft
                      (SelectArgument index (Here ft)))
  mem <- gets setupMemImpl
  logRegMap context sym mem args
  return args

-- | If this pointer already points to initialized memory, then just return the
-- value. Otherwise, allocate some memory and initialize it with a fresh, minimal
-- value.
--
-- TODO: Allow for array initialization
initialize ::
  forall m arch sym argTypes inTy ft.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  FullTypeRepr m ('FTPtr ft) {-^ Type of pointer -} ->
  Selector m argTypes inTy ('FTPtr ft) {-^ Path to the pointer -} ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Setup m arch sym argTypes ( LLVMMem.LLVMPtr sym (ArchWidth arch)
                            , Crucible.RegEntry sym (ToCrucibleType arch ft)
                            )
initialize context sym (FTPtrRepr ptPointedTo) selector pointer =
  let ftPointedTo = asFullType (context ^. moduleTypes) ptPointedTo
  in load sym ftPointedTo pointer >>=
       \case
         Just (TypedRegEntry _fullTypeRepr' regEntry) -> pure (pointer, regEntry)
         Nothing ->
           do ptr <- malloc sym ftPointedTo pointer
              pointedToVal <-
                generateMinimalValue
                  (Proxy :: Proxy arch)
                  sym
                  ftPointedTo
                  (selector & selectorCursor %~ \cursor -> Dereference cursor)
              let tp = toCrucibleType (Proxy :: Proxy arch) ftPointedTo
              ptr' <-
                store sym ftPointedTo (Crucible.RegEntry tp pointedToVal) ptr
              pure (ptr', Crucible.RegEntry tp pointedToVal)

constrainHere ::
  forall m arch sym argTypes inTy atTy.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  Selector m argTypes inTy atTy {-^ Top-level selector -} ->
  Constraint m atTy ->
  FullTypeRepr m atTy ->
  Crucible.RegEntry sym (ToCrucibleType arch atTy) ->
  Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch atTy))
constrainHere context sym selector constraint fullTypeRepr regEntry@(Crucible.RegEntry typeRepr regValue) =
  do writeLogM ("Constraining value at: " <> Text.pack (show (ppCursor "<top>" (selector ^. selectorCursor))))
     writeLogM ("Constraint: " <> Text.pack (show (ppConstraint constraint)))
     let showMe ::
           forall ft' ann.
           FullTypeRepr m ft' ->
           Crucible.RegEntry sym (ToCrucibleType arch ft') ->
           Setup m arch sym argTypes (Doc ann)
         showMe fullTy regEnt =
           do mem <- gets setupMemImpl
              storableTy <- storableType (toMemType fullTy)
              liftIO $ ppRegValue (Proxy :: Proxy arch) sym mem storableTy regEnt
     case constraint of
       Allocated ->
         case fullTypeRepr of
           FTPtrRepr partTypeRepr ->
             do let fullTypeRepr' = asFullType (context ^. moduleTypes) partTypeRepr
                regEntry' <-
                  Crucible.RegEntry typeRepr <$>
                    malloc sym fullTypeRepr' regValue
                pretty <- showMe fullTypeRepr regEntry'
                writeLogM ("Constrained value: " <> Text.pack (show pretty))
                pure regEntry'
       Aligned alignment ->
         case typeRepr of
           LLVMMem.PtrRepr ->
             do assume constraint =<<
                  liftIO (LLVMMem.isAligned sym ?ptrWidth regValue alignment)
                pretty <- showMe fullTypeRepr regEntry
                writeLogM ("Constrained value: " <> Text.pack (show pretty))
                pure regEntry
           _ -> throwError (SetupBadConstraintSelector (SomeSelector selector) (toMemType fullTypeRepr) (Some constraint))
       Initialized ->
         case fullTypeRepr of
           FTPtrRepr partTypeRepr ->
             do let fullTypeRepr' = asFullType (context ^. moduleTypes) partTypeRepr
                (ptr, freshVal) <-
                  initialize context sym fullTypeRepr selector regValue
                let regEntry' = Crucible.RegEntry typeRepr ptr
                prettyPtr <- showMe fullTypeRepr regEntry'
                prettyVal <- showMe fullTypeRepr' freshVal
                writeLogM ("Initialized pointer: " <> Text.pack (show prettyPtr))
                writeLogM ("Pointed-to value: " <> Text.pack (show prettyVal))
                pure regEntry'
       _ -> unimplemented "constrainHere" ("Constraint:" ++ show (ppConstraint constraint))

constrainValue ::
  forall m arch sym argTypes inTy atTy atTy'.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  Constraint m atTy' {-^ Constraint on some sub-part of this value -} ->
  Cursor m atTy atTy' {-^ Cursor to the value we want to constrain -} ->
  Selector m argTypes inTy atTy {-^ Path to this value -} ->
  FullTypeRepr m atTy {-^ Type of this value -} ->
  Crucible.RegEntry sym (ToCrucibleType arch atTy) {-^ This value -} ->
  Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch atTy))
constrainValue context sym constraint cursor selector ftRepr regEntry@(Crucible.RegEntry typeRepr regValue) =
  case cursor of
    Here ftRepr' ->
      case testEquality ftRepr ftRepr' of
        Nothing -> panic "constrainValue" ["Mismatched type representatives"]
        Just _ -> constrainHere context sym selector constraint ftRepr regEntry
    Dereference _ ->
      case ftRepr of
        -- TODO
        FTPtrRepr (asFullType (context ^. moduleTypes) -> pointedToRepr) ->
          do -- If there's already a value behind this pointer, constrain that.
             -- Otherwise, allocate new memory, put a fresh value there, and constrain
             -- that.
             (ptr, pointedToValue) <-
               initialize context sym ftRepr selector regValue
             case dereference pointedToRepr cursor of
               -- This case is technically unreachable because we matched on
               -- Here above, but... it typechecks and makes GHC happy.
               Left Refl -> constrainHere context sym selector constraint ftRepr regEntry
               Right cursor' ->
                 do regEntry' <-
                      constrainValue
                       context
                       sym
                       constraint
                       cursor'
                       (selector & selectorCursor %~ Dereference)
                       pointedToRepr
                       pointedToValue
                    ptr' <- store sym pointedToRepr regEntry' ptr
                    pure $ Crucible.RegEntry typeRepr ptr'
        _ -> throwError (SetupBadConstraintSelector (SomeSelector selector) (toMemType ftRepr) (Some constraint))
    _ -> unimplemented "constrainValue" "Non-top-level cursors"

constrainOneArgument ::
  forall m arch sym argTypes inTy.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  [SomeValueConstraint m inTy] ->
  Ctx.Index argTypes inTy ->
  Crucible.RegEntry sym (ToCrucibleType arch inTy) ->
  Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch inTy))
constrainOneArgument context sym constraints idx regEntry =
  -- TODO fold
  case constraints of
    [] -> pure regEntry
    (SomeValueConstraint vc@(ValueConstraint ftRepr cursor constraint):rest) ->
      do writeLogM ("Satisfying constraint: " <> Text.pack (show (ppValueConstraint vc)))
         constrainOneArgument context sym rest idx
           =<< constrainValue
                 context
                 sym
                 constraint
                 cursor
                 (SelectArgument idx (Here ftRepr))
                 ftRepr
                 regEntry

constrain ::
  forall m arch sym argTypes.
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  ) =>
  Context m arch argTypes ->
  sym ->
  Constraints m arch argTypes ->
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) ->
  Setup m arch sym argTypes (Crucible.RegMap sym (MapToCrucibleType arch argTypes))
constrain context sym preconds (Crucible.RegMap args) =
  do writeLogM ("Establishing preconditions..." :: Text)
     args' <-
       generateM
         (Proxy :: Proxy arch)
         (Ctx.size (context ^. argumentStorageTypes))
         (\idx idx' Refl ->
            do let constraints = Set.toList (getCompose (argConstraints preconds Ctx.! idx))
               unless (null constraints) $
                 writeLogM ("Modifying argument #" <> Text.pack (show (Ctx.indexVal idx)))
               constrainOneArgument context sym constraints idx (args Ctx.! idx'))
     return (Crucible.RegMap args')

setupExecution ::
  ( Crucible.IsSymInterface sym
  , LLVMMem.HasLLVMAnn sym
  , ArchOk arch
  , HasLog Text f
  , MonadIO f
  ) =>
  sym ->
  Context m arch argTypes ->
  Constraints m arch argTypes ->
  f (Either (SetupError m arch argTypes)
            ( SetupResult m arch sym argTypes
            , Crucible.RegMap sym (MapToCrucibleType arch argTypes)
            ))
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
