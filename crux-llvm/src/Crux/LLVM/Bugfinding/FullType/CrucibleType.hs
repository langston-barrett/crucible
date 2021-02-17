{-
Module           : Crux.LLVM.Bugfinding.FullType.CrucibleType
Description      : Interop between 'FullType' and 'CrucibleTypes.CrucibleType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Crux.LLVM.Bugfinding.FullType.CrucibleType
  ( toCrucibleType

  -- * Assignments
  , SomeAssign(..)
  , SomeIndex(..)
  , assignmentToFullType
  , translateIndex
  , generateM
  ) where

import           Data.Functor.Const (Const(Const, getConst))
import           Data.Proxy (Proxy(Proxy))
import           Control.Monad.State (runStateT)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some), viewSome)

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.FullType.Type
import           Crux.LLVM.Bugfinding.FullType.MemType (toFullTypeM)
import           Crux.LLVM.Bugfinding.FullType.ModuleTypes (ModuleTypes, makeModuleTypes)

-- | c.f. @llvmTypeToRepr@
toCrucibleType ::
  ArchOk arch =>
  proxy arch ->
  FullTypeRepr m ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType arch ft)
toCrucibleType proxy =
  \case
    FTIntRepr natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTArrayRepr _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType proxy fullTypeRepr)
    FTStructRepr _ typeReprs ->
      case assignmentToCrucibleType proxy typeReprs of
        SomeAssign' ctReprs Refl -> CrucibleTypes.StructRepr ctReprs

data SomeAssign arch crucibleTypes
  = forall m fullTypes.
    SomeAssign
      { saFullTypes :: Ctx.Assignment (FullTypeRepr m) fullTypes
      , saModuleTypes :: ModuleTypes m
      , saProof :: MapToCrucibleType arch fullTypes :~: crucibleTypes
      }

assignmentToFullType ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Either L.Ident (SomeAssign arch crucibleTypes)
assignmentToFullType proxy crucibleTypes memTypes =
  case makeModuleTypes ?lc of
    Some moduleTypes ->
      do (Some fullTypes, moduleTypes') <-
           runStateT
            (Ctx.generateSomeM
              (Ctx.sizeInt (Ctx.size crucibleTypes))
              (\idx ->
                case Ctx.intIndex idx (Ctx.size crucibleTypes) of
                  Nothing -> panic "Impossible" ["Mismatched context size"]
                  Just (Some idx') ->
                    do Some fullTypeRepr <-
                         toFullTypeM (getConst (memTypes Ctx.! idx'))
                       pure $ Some fullTypeRepr))
            moduleTypes
         case testCompatibilityAssign proxy fullTypes crucibleTypes of
           Just Refl -> Right (SomeAssign fullTypes moduleTypes' Refl)
           Nothing -> panic "Impossible" []

data SomeAssign' arch m fullTypes
  = forall crucibleTypes.
    SomeAssign'
      { saCrucibleTypes :: Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes
      , saProof' :: MapToCrucibleType arch fullTypes :~: crucibleTypes
      }

assignmentToCrucibleType ::
  ArchOk arch =>
  proxy arch ->
  Ctx.Assignment (FullTypeRepr m) fts ->
  SomeAssign' arch m fts
assignmentToCrucibleType proxy fullTypes =
  let someCrucibleTypes =
        Ctx.generateSome
          (Ctx.sizeInt (Ctx.size fullTypes))
          (\idx ->
              case Ctx.intIndex idx (Ctx.size fullTypes) of
                Nothing ->
                  panic
                    "assignmentToCrucibleType"
                    ["Impossible: Index was from the same context!"]
                Just (Some idx') -> Some (toCrucibleType proxy (fullTypes Ctx.! idx')))
  in case someCrucibleTypes of
       Some crucibleTypes ->
        case testCompatibilityAssign proxy fullTypes crucibleTypes of
          Just Refl -> SomeAssign' crucibleTypes Refl
          Nothing ->
            panic
              "assignmentToCrucibleType"
              ["Impossible: Types match by construction!"]

testCompatibility ::
  forall proxy arch m ft tp.
  ArchOk arch =>
  proxy arch ->
  FullTypeRepr m ft ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (ToCrucibleType arch ft :~: tp)
testCompatibility proxy fullTypeRepr = testEquality (toCrucibleType proxy fullTypeRepr)

testCompatibilityAssign ::
  ArchOk arch =>
  proxy arch ->
  Ctx.Assignment (FullTypeRepr m) ctx1 ->
  Ctx.Assignment CrucibleTypes.TypeRepr ctx2 ->
  Maybe (MapToCrucibleType arch ctx1 :~: ctx2)
testCompatibilityAssign proxy ftAssign ctAssign =
  -- TODO(lb): This is like a zip + fold?
  case (Ctx.viewAssign ftAssign, Ctx.viewAssign ctAssign) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Just Refl
    (Ctx.AssignExtend ftRest ftHead, Ctx.AssignExtend ctRest ctHead) ->
      case (testCompatibility proxy ftHead ctHead, testCompatibilityAssign proxy ftRest ctRest) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    _ -> Nothing

-- data FullTypeFromCrucible arch m tp =
--   forall ft. FullTypeFromCrucible (ToCrucibleType arch ft :~: tp) (FullTypeRepr m ft)

-- assignmentToFullType' ::
--   forall proxy arch crucibleTypes.
--   ( ?lc :: TypeContext
--   , ArchOk arch
--   ) =>
--   proxy arch ->
--   Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
--   Ctx.Assignment (Const MemType) crucibleTypes ->
--   Maybe (Ctx.Assignment (FullTypeFromCrucible m arch) crucibleTypes)
-- assignmentToFullType' proxy crucibleTypes memTypes =
--   Ctx.generateM
--     (Ctx.size crucibleTypes)
--     (\idx ->
--        do Some fullTypeRepr <-
--             toFullType proxy (getConst (memTypes Ctx.! idx))
--           Refl <- testEquality (crucibleTypes Ctx.! idx) (toCrucibleType proxy fullTypeRepr)
--           Just (FullTypeFromCrucible Refl fullTypeRepr))

data SomeIndex arch ft crucibleTypes
  = forall tp. SomeIndex (Ctx.Index crucibleTypes tp) (ToCrucibleType arch ft :~: tp)

translateSize ::
  proxy arch ->
  Ctx.Size fullTypes ->
  Ctx.Size (MapToCrucibleType arch fullTypes)
translateSize proxy sz =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> Ctx.zeroSize
    Ctx.IncSize sz' -> Ctx.incSize (translateSize proxy sz')

translateIndex ::
  proxy arch ->
  Ctx.Size fullTypes ->
  Ctx.Index fullTypes ft ->
  SomeIndex arch ft (MapToCrucibleType arch fullTypes)
translateIndex proxy sz idx =
  case (Ctx.viewSize sz, Ctx.viewIndex sz idx) of
    (Ctx.IncSize _, Ctx.IndexViewLast sz') ->
      SomeIndex (Ctx.lastIndex (Ctx.incSize (translateSize proxy sz'))) Refl
    (Ctx.IncSize sz', Ctx.IndexViewInit idx') ->
      case translateIndex proxy sz' idx' of
        SomeIndex idx'' Refl -> SomeIndex (Ctx.skipIndex idx'') Refl
    (Ctx.ZeroSize, _) ->
      panic
        "translateIndex"
        ["Impossible: Can't index into empty/zero-size context."]

generateM ::
  Applicative m =>
  proxy arch ->
  Ctx.Size fullTypes ->
  (forall ft tp.
   Ctx.Index fullTypes ft ->
   Ctx.Index (MapToCrucibleType arch fullTypes) tp ->
   (ToCrucibleType arch ft :~: tp) ->
   m (f tp)) ->
  m (Ctx.Assignment f (MapToCrucibleType arch fullTypes))
generateM proxy sz f =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> pure Ctx.empty
    Ctx.IncSize sz' ->
      Ctx.extend
      <$> generateM
            proxy
            sz'
            (\idx idx' Refl -> f (Ctx.skipIndex idx) (Ctx.skipIndex idx') Refl)
      <*>
        case translateIndex proxy sz (Ctx.lastIndex sz) of
          SomeIndex idx' Refl -> f (Ctx.lastIndex sz) idx' Refl
