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
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Vector as Vec

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.FullType.Type

----------------------------------------------------------------------
-- Conversions (toFullType and its callees)
--

-- | c.f. @llvmTypeToRepr@
toCrucibleType ::
  ArchOk arch =>
  FullTypeRepr 'Full arch ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType ft)
toCrucibleType =
  \case
    FTIntRepr _ natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr _ _ _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTArrayRepr _ _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType fullTypeRepr)
    FTFullStructRepr _ _ typeReprs ->
      case assignmentToCrucibleType typeReprs of
        SomeAssign' ctReprs Refl -> CrucibleTypes.StructRepr ctReprs

-- | c.f. @llvmTypeToRepr@
toCrucibleType' ::
  forall arch full ft.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  FullTypeRepr full arch ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType ft)
toCrucibleType' =
  \case
    FTIntRepr _ natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr _ _ _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTArrayRepr _ _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType' fullTypeRepr)
    FTFullStructRepr _ _ typeReprs ->
      case anyAssignmentToCrucibleType toCrucibleType' typeReprs of
        SomeAssign' ctReprs Refl -> CrucibleTypes.StructRepr ctReprs
    FTPartStructRepr _ typeReprs ->
      case anyAssignmentToCrucibleType toCrucibleType' typeReprs of
        SomeAssign' ctReprs Refl -> CrucibleTypes.StructRepr ctReprs
    FTAliasRepr (Const ident) -> undefined -- TODO
      -- TODO: Maybe handle this?
      -- case asMemType (Alias ident) of
      --   Left err -> panic "toCrucibleType'" ["bad alias"]
      --   Right memType ->
      --     case toPartType (Proxy :: Proxy arch) memType of
      --       Just (Some partType) -> toCrucibleType' partType
      --       Nothing -> panic "toCrucibleType'" ["bad mem type"]

-- TODO: Make this total?
toPartType ::
  forall proxy arch.
  ArchOk arch =>
  proxy arch ->
  MemType ->
  Maybe (Some (FullTypeRepr 'Part arch))
toPartType proxy =
  \case
    PtrType (MemType memType) ->
      do Some pointedTo <- toPartType proxy memType
         Just (Some (FTPtrRepr PartRepr PartRepr pointedTo))
    PtrType (Alias ident) -> Just (Some (FTAliasRepr (Const ident)))
    mt@(PtrType _) -> unimplemented "toFullType" ("Translating " ++ show mt)
    IntType n ->
      case mkNatRepr n of
        Some w | Just LeqProof <- isPosNat w -> Just (Some (FTIntRepr PartRepr w))
        _ -> panic "toPartType" ["Invalid integer width " ++ show n]
    StructType structInfo ->
      do let structInfoFields = MemType.siFields structInfo
         Some fields <-
           Ctx.generateSomeM
             (length structInfoFields)
             (\idx -> toPartType proxy (MemType.fiType (structInfoFields Vec.! idx))
               :: Maybe (Some (FullTypeRepr 'Part arch)))
         Just (Some (FTPartStructRepr structInfo fields))
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
  Maybe (Some (FullTypeRepr 'Full arch))
toFullType proxy memType typeRepr =
  case CrucibleTypes.asBaseType typeRepr of
    CrucibleTypes.AsBaseType _baseTypeRepr ->
      unimplemented "toFullType" "Base types"
    CrucibleTypes.NotBaseType ->
      case typeRepr of
        LLVMMem.LLVMPointerRepr w ->
          case (memType, testEquality ?ptrWidth w) of
            (PtrType _symType, Just Refl) ->
              do Some contained <- toPartType proxy memType
                 Just (Some (FTPtrRepr PartRepr FullRepr contained))
            (IntType _w, _) ->
              -- TODO assert about _w
              Just (Some (FTIntRepr FullRepr w))
            _ -> badCombo
        CrucibleTypes.VectorRepr containedTypeRepr ->
          case memType of
            VecType n memType' ->
              do Some contained <-
                   toFullType proxy memType' containedTypeRepr
                 Some natRepr <- pure $ mkNatRepr n
                 Just (Some (FTArrayRepr FullRepr natRepr contained))
            _ -> badCombo
        CrucibleTypes.StructRepr
          (fieldTypes :: Ctx.Assignment CrucibleTypes.TypeRepr fields) ->
          case memType of
            StructType structInfo ->
              do SomeAssign fullFieldTypes Refl <-
                   assignmentToFullType proxy fieldTypes $
                     Ctx.generate
                       (Ctx.size fieldTypes)
                       (\idx -> Const (MemType.fiType (MemType.siFields structInfo Vec.! Ctx.indexVal idx)))
                 Just (Some (FTFullStructRepr FullRepr structInfo fullFieldTypes))
            _ -> badCombo
        _ -> unimplemented "toFullType" (show typeRepr)
  where
    badCombo :: forall a. a
    badCombo =
      panic "Bad MemType/CrucibleType combo" [ "MemType: " ++ show memType
                                             , "Crucible type:" ++ show typeRepr
                                             ]

data SomeAssign arch crucibleTypes
  = forall fullTypes.
    SomeAssign
      { saFullTypes :: Ctx.Assignment (FullTypeRepr 'Full arch) fullTypes
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

data SomeAssign' arch fullTypes
  = forall crucibleTypes.
    SomeAssign'
      { saCrucibleTypes :: Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes
      , saProof' :: MapToCrucibleType fullTypes :~: crucibleTypes
      }

assignmentToCrucibleType ::
  ArchOk arch =>
  Ctx.Assignment (FullTypeRepr 'Full arch) fts ->
  SomeAssign' arch fts
assignmentToCrucibleType fullTypes =
  let someCrucibleTypes =
        Ctx.generateSome
          (Ctx.sizeInt (Ctx.size fullTypes))
          (\idx ->
              case Ctx.intIndex idx (Ctx.size fullTypes) of
                Nothing ->
                  panic
                    "assignmentToCrucibleType"
                    ["Impossible: Index was from the same context!"]
                Just (Some idx') -> Some (toCrucibleType (fullTypes Ctx.! idx')))
  in case someCrucibleTypes of
       Some crucibleTypes ->
        case testCompatibilityAssign fullTypes crucibleTypes of
          Just Refl -> SomeAssign' crucibleTypes Refl
          Nothing ->
            panic
              "assignmentToCrucibleType"
              ["Impossible: Types match by construction!"]

anyAssignmentToCrucibleType ::
  ArchOk arch =>
  (forall ft. FullTypeRepr full arch ft -> CrucibleTypes.TypeRepr (ToCrucibleType ft)) ->
  Ctx.Assignment (FullTypeRepr full arch) fts ->
  SomeAssign' arch fts
anyAssignmentToCrucibleType convert fullTypes =
  let someCrucibleTypes =
        Ctx.generateSome
          (Ctx.sizeInt (Ctx.size fullTypes))
          (\idx ->
              case Ctx.intIndex idx (Ctx.size fullTypes) of
                Nothing ->
                  panic
                    "assignmentToCrucibleType"
                    ["Impossible: Index was from the same context!"]
                Just (Some idx') -> Some (convert (fullTypes Ctx.! idx')))
  in case someCrucibleTypes of
       Some crucibleTypes ->
        case testCompatibilityAnyAssign convert fullTypes crucibleTypes of
          Just Refl -> SomeAssign' crucibleTypes Refl
          Nothing ->
            panic
              "assignmentToCrucibleType"
              ["Impossible: Types match by construction!"]

testCompatibility ::
  ArchOk arch =>
  (forall ft. FullTypeRepr full arch ft -> CrucibleTypes.TypeRepr (ToCrucibleType ft)) ->
  FullTypeRepr full arch (ft :: FullType arch) ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (ToCrucibleType ft :~: tp)
testCompatibility convert fullTypeRepr = testEquality (convert fullTypeRepr)

testCompatibilityAssign ::
  ArchOk arch =>
  Ctx.Assignment (FullTypeRepr 'Full arch) ctx1 ->
  Ctx.Assignment CrucibleTypes.TypeRepr ctx2 ->
  Maybe (MapToCrucibleType ctx1 :~: ctx2)
testCompatibilityAssign = testCompatibilityAnyAssign toCrucibleType

testCompatibilityAnyAssign ::
  ArchOk arch =>
  (forall ft. FullTypeRepr full arch ft -> CrucibleTypes.TypeRepr (ToCrucibleType ft)) ->
  Ctx.Assignment (FullTypeRepr full arch) ctx1 ->
  Ctx.Assignment CrucibleTypes.TypeRepr ctx2 ->
  Maybe (MapToCrucibleType ctx1 :~: ctx2)
testCompatibilityAnyAssign convert ftAssign ctAssign =
  case (Ctx.viewAssign ftAssign, Ctx.viewAssign ctAssign) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Just Refl
    (Ctx.AssignExtend ftRest ftHead, Ctx.AssignExtend ctRest ctHead) ->
      case (testCompatibility convert ftHead ctHead, testCompatibilityAnyAssign convert ftRest ctRest) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    _ -> Nothing

----------------------------------------------------------------------
-- Assignments
--

data FullTypeFromCrucible full arch tp =
  forall ft. FullTypeFromCrucible (ToCrucibleType ft :~: tp) (FullTypeRepr full arch ft)

assignmentToFullType' ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Maybe (Ctx.Assignment (FullTypeFromCrucible 'Full arch) crucibleTypes)
assignmentToFullType' proxy crucibleTypes memTypes =
  Ctx.generateM
    (Ctx.size crucibleTypes)
    (\idx ->
       do let typeRepr = crucibleTypes Ctx.! idx
          Some fullTypeRepr <-
            toFullType proxy (getConst (memTypes Ctx.! idx)) typeRepr
          Refl <- testEquality typeRepr (toCrucibleType fullTypeRepr)
          Just (FullTypeFromCrucible Refl fullTypeRepr))

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
