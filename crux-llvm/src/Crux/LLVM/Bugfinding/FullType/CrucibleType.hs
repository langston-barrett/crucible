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
  , toPartType
  , toFullType

  -- * Assignments
  , SomeAssign(..)
  , SomeIndex(..)
  , assignmentToFullType
  , assignmentToFullType'
  , translateIndex
  , generateM
  ) where

import           Data.Functor.Const (Const(Const, getConst))
import qualified Data.Vector as Vec

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.FullType.Type

-- | c.f. @llvmTypeToRepr@
toCrucibleType ::
  ArchOk arch =>
  FullTypeRepr arch ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType ft)
toCrucibleType =
  \case
    FTIntRepr natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTArrayRepr _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType fullTypeRepr)
    FTStructRepr _ typeReprs _ -> CrucibleTypes.StructRepr typeReprs

toPartType ::
  forall proxy arch.
  ArchOk arch =>
  proxy arch ->
  MemType ->
  Maybe (Some (PartTypeRepr arch))
toPartType proxy =
  \case
    PtrType (MemType memType) ->
      do Some pointedTo <- toPartType proxy memType
         Just (Some (PTPtrRepr pointedTo))
    PtrType (Alias ident) -> Just (Some (PTAliasRepr (Const ident)))
    mt@(PtrType _) -> unimplemented "toFullType" ("Translating " ++ show mt)
    IntType n ->
      case mkNatRepr n of
        Some w | Just LeqProof <- isPosNat w -> Just (Some (PTIntRepr w))
        _ -> panic "toPartType" ["Invalid integer width " ++ show n]
    StructType structInfo ->
      do let structInfoFields = MemType.siFields structInfo
         Some fields <-
           Ctx.generateSomeM
             (length structInfoFields)
             (\idx -> toPartType proxy (MemType.fiType (structInfoFields Vec.! idx))
               :: Maybe (Some (PartTypeRepr arch)))
         Just (Some (PTStructRepr structInfo fields))
    _ -> unimplemented "toFullType" "Translating this type"

-- NOTE(lb): I *believe* that it's impossible to translate a MemType+TypeRepr
-- directly into a FullType and prove that the FullType corresponds to the
-- CrucibleType, because in the struct case you'd need to construct a Ctx out of
-- an Assignment with existentially quantified types. However, the following
-- function just uses testEquality on the TypeRepr from toCrucibleType.

toFullType ::
  forall proxy arch tp.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  MemType ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (Some (FullTypeRepr arch))
toFullType proxy memType typeRepr =
  case CrucibleTypes.asBaseType typeRepr of
    CrucibleTypes.AsBaseType _baseTypeRepr -> unimplemented "toFullType" "Base types"
    CrucibleTypes.NotBaseType ->
      case typeRepr of
        LLVMMem.LLVMPointerRepr w ->
          case (memType, testEquality ?ptrWidth w) of
            (PtrType _symType, Just Refl) ->
              do Some contained <- toPartType proxy memType
                 Just (Some (FTPtrRepr contained))
            (IntType _w, _) ->
              -- TODO assert about _w
              Just (Some (FTIntRepr w))
            _ -> badCombo
        CrucibleTypes.VectorRepr containedTypeRepr ->
          case memType of
            VecType n memType' ->
              do Some contained <-
                   toFullType proxy memType' containedTypeRepr
                 Some natRepr <- pure $ mkNatRepr n
                 Just (Some (FTArrayRepr natRepr contained))
            _ -> badCombo
        CrucibleTypes.StructRepr
          (fieldTypes :: Ctx.Assignment CrucibleTypes.TypeRepr fields) ->
          unimplemented "toFullType" "Struct types"
        _ -> unimplemented "toFullType" (show typeRepr)
  where
    badCombo :: forall a. a
    badCombo =
      panic "Bad MemType/CrucibleType combo" [ "MemType: " ++ show memType
                                             , "Crucible type:" ++ show typeRepr
                                             ]

testCompatibility ::
  forall arch ft tp.
  ArchOk arch =>
  FullTypeRepr arch (ft :: FullType arch) ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (ToCrucibleType ft :~: tp)
testCompatibility fullTypeRepr = testEquality (toCrucibleType fullTypeRepr)

----------------------------------------------------------------------
-- Assignments
--

data FullTypeFromCrucible arch tp =
  forall ft. FullTypeFromCrucible (ToCrucibleType ft :~: tp) (FullTypeRepr arch ft)

assignmentToFullType' ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Maybe (Ctx.Assignment (FullTypeFromCrucible arch) crucibleTypes)
assignmentToFullType' proxy crucibleTypes memTypes =
  Ctx.generateM
    (Ctx.size crucibleTypes)
    (\idx ->
       do let typeRepr = crucibleTypes Ctx.! idx
          Some fullTypeRepr <-
            toFullType proxy (getConst (memTypes Ctx.! idx)) typeRepr
          Refl <- testEquality typeRepr (toCrucibleType fullTypeRepr)
          Just (FullTypeFromCrucible Refl fullTypeRepr))

data SomeAssign arch crucibleTypes
  = forall fullTypes.
    SomeAssign
      { saFullTypes :: Ctx.Assignment (FullTypeRepr arch) fullTypes
      , saProof :: MapToCrucibleType fullTypes :~: crucibleTypes
      }

assignmentToFullType ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Maybe (SomeAssign arch crucibleTypes)
assignmentToFullType proxy crucibleTypes memTypes =
  do Some fullTypes <-
       Ctx.generateSomeM
         (Ctx.sizeInt (Ctx.size crucibleTypes))
         (\idx ->
           do Some idx' <- Ctx.intIndex idx (Ctx.size crucibleTypes)
              let typeRepr = crucibleTypes Ctx.! idx'
              Some fullTypeRepr <-
                toFullType proxy (getConst (memTypes Ctx.! idx')) typeRepr
              Just (Some fullTypeRepr))
     Refl <- testCompatibilityAssign fullTypes crucibleTypes
     Just (SomeAssign fullTypes Refl)

data SomeIndex ft crucibleTypes
  = forall tp. SomeIndex (Ctx.Index crucibleTypes tp) (ToCrucibleType ft :~: tp)

translateSize :: Ctx.Size fullTypes -> Ctx.Size (MapToCrucibleType fullTypes)
translateSize sz =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> Ctx.zeroSize
    Ctx.IncSize sz' -> Ctx.incSize (translateSize sz')

translateIndex ::
  Ctx.Size fullTypes -> Ctx.Index fullTypes ft -> SomeIndex ft (MapToCrucibleType fullTypes)
translateIndex sz idx =
  case (Ctx.viewSize sz, Ctx.viewIndex sz idx) of
    (Ctx.IncSize _, Ctx.IndexViewLast sz') ->
      SomeIndex (Ctx.lastIndex (Ctx.incSize (translateSize sz'))) Refl
    (Ctx.IncSize sz', Ctx.IndexViewInit idx') ->
      case translateIndex sz' idx' of
        SomeIndex idx'' Refl -> SomeIndex (Ctx.skipIndex idx'') Refl
    (Ctx.ZeroSize, _) ->
      panic
        "translateIndex"
        ["Impossible: Can't index into empty/zero-size context."]

generateM ::
  Applicative m =>
  Ctx.Size fullTypes ->
  (forall ft tp.
   Ctx.Index fullTypes ft ->
   Ctx.Index (MapToCrucibleType fullTypes) tp ->
   (ToCrucibleType ft :~: tp) ->
   m (f tp)) ->
  m (Ctx.Assignment f (MapToCrucibleType fullTypes))
generateM sz f =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> pure Ctx.empty
    Ctx.IncSize sz' ->
      Ctx.extend
      <$> generateM
            sz'
            (\idx idx' Refl -> f (Ctx.skipIndex idx) (Ctx.skipIndex idx') Refl)
      <*>
        case translateIndex sz (Ctx.lastIndex sz) of
          SomeIndex idx' Refl -> f (Ctx.lastIndex sz) idx' Refl

testCompatibilityAssign ::
  ArchOk arch =>
  Ctx.Assignment (FullTypeRepr arch) ctx1 ->
  Ctx.Assignment CrucibleTypes.TypeRepr ctx2 ->
  Maybe (MapToCrucibleType ctx1 :~: ctx2)
testCompatibilityAssign ftAssign ctAssign =
  -- TODO(lb): This is like a zip + fold?
  case (Ctx.viewAssign ftAssign, Ctx.viewAssign ctAssign) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Just Refl
    (Ctx.AssignExtend ftRest ftHead, Ctx.AssignExtend ctRest ctHead) ->
      case (testCompatibility ftHead ctHead, testCompatibilityAssign ftRest ctRest) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    _ -> Nothing
