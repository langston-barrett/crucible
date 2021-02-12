-- Like MemType, but not mutually recursive
-- Like CrucibleType, but has types of pointers
-- Contains definitions of aliases

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

module Crux.LLVM.Bugfinding.FullType where

import           GHC.TypeLits (Nat)
import           Data.Functor.Const (Const(getConst))
import           Data.Functor.Compose (Compose(Compose))
import           Data.Traversable (for)
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Text as Text
import qualified Data.Vector as Vec

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.TraversableFC (fmapFC)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.SymbolRepr
import           Data.Parameterized.Some (Some(Some), viewSome)
import           Data.Parameterized.Vector (Vector)

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)


-- | Type level only
--
-- Like a 'CrucibleTypes.CrucibleType', but contains type information through
-- pointer references.
--
-- Alternatively, like a 'MemType' that can be linked to a
-- 'CrucibleTypes.CrucibleType' by type-level information.
data FullType arch where
  FTInt :: Nat -> FullType arch
  FTFloat :: FullType arch
  FTPtr :: FullType arch -> FullType arch
  FTArray :: Nat -> FullType arch -> FullType arch
  FTStruct :: Ctx.Ctx (FullType arch) -> FullType arch

type family MapToCrucibleType (ctx :: Ctx (FullType arch)) :: Ctx CrucibleTypes.CrucibleType where
  MapToCrucibleType 'Ctx.EmptyCtx   = Ctx.EmptyCtx
  MapToCrucibleType (xs 'Ctx.::> x) = MapToCrucibleType xs Ctx.::> ToCrucibleType x

type family ToCrucibleType (ft :: FullType arch) :: CrucibleTypes.CrucibleType where
  ToCrucibleType (FTInt n) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType n)
  ToCrucibleType (FTPtr _ft :: FullType arch) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType (FTArray _n ft) =
    CrucibleTypes.VectorType (ToCrucibleType ft)
  ToCrucibleType (FTStruct ctx) =
    CrucibleTypes.StructType (MapToCrucibleType ctx)

-- | A 'FullTypeRepr' has enough information to recover a
-- 'CrucibleTypes.CrucibleType'.
data FullTypeRepr arch (ft :: FullType arch) where
  FTIntRepr :: (1 <= w) => NatRepr w -> FullTypeRepr arch ('FTInt w)
  FTPtrRepr :: PartTypeRepr arch ft -> FullTypeRepr arch ('FTPtr ft)
  FTArrayRepr :: NatRepr n -> FullTypeRepr arch ft -> FullTypeRepr arch ('FTArray n ft)
  FTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment CrucibleTypes.TypeRepr (MapToCrucibleType fields) ->
    Ctx.Assignment (FullTypeRepr arch) fields ->
    FullTypeRepr arch ('FTStruct fields)

-- | A 'PartTypeRepr' doesn't have enough information to recover a
-- 'CrucibleTypes.CrucibleType', and so must appear under a pointer in a
-- 'FullTypeRepr'.
data PartTypeRepr arch (ft :: FullType arch) where
  -- PTFullTypeRepr :: FullTypeRepr ft -> PartTypeRepr ft
  -- TODO(?) duplication
  PTIntRepr :: (1 <= w) => NatRepr w -> PartTypeRepr arch ('FTInt w)
  PTPtrRepr :: PartTypeRepr arch ft -> PartTypeRepr arch ('FTPtr ft)
  PTArrayRepr :: NatRepr n -> PartTypeRepr arch ft -> PartTypeRepr arch ('FTArray n ft)
  PTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment (PartTypeRepr arch) fields ->
    PartTypeRepr arch ('FTStruct fields)
  PTAliasRepr :: L.Ident -> PartTypeRepr arch ft

data FullTypeFromCrucible arch tp =
  forall ft. FullTypeFromCrucible (ToCrucibleType ft :~: tp) (FullTypeRepr arch ft)

assignmentToFullType ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Maybe (Ctx.Assignment (FullTypeFromCrucible arch) crucibleTypes)
assignmentToFullType proxy crucibleTypes memTypes =
  Ctx.generateM
    (Ctx.size crucibleTypes)
    (\idx ->
       do let typeRepr = crucibleTypes Ctx.! idx
          Some fullTypeRepr <-
            toFullType proxy (getConst (memTypes Ctx.! idx)) typeRepr
          Refl <- testEquality typeRepr (toCrucibleType fullTypeRepr)
          Just (FullTypeFromCrucible Refl fullTypeRepr))

data CrucibleFromFullType ft =
  CrucibleFromFullType (CrucibleTypes.TypeRepr (ToCrucibleType ft))

-- | c.f. @llvmTypeToRepr@
toCrucibleType ::
  ArchOk arch =>
  FullTypeRepr arch ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType ft)
toCrucibleType =
  \case
    FTIntRepr natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTArrayRepr natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType fullTypeRepr)
    FTStructRepr _ typeReprs _ -> CrucibleTypes.StructRepr typeReprs

-- NOTE(lb): I *believe* that it's impossible to translate a MemType+TypeRepr
-- directly into a FullType and prove that the FullType corresponds to the
-- CrucibleType, because in the struct case you'd need to construct a Ctx out of
-- an Assignment with existentially quantified types. However, you can just use
-- the testEquality instance on the

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
    PtrType (Alias ident) -> Just (Some (PTAliasRepr ident))
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
    CrucibleTypes.AsBaseType baseTypeRepr -> unimplemented "toFullType" "Base types"
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

data IntConstraint = IntConstraint

data ValueSpec (ty :: FullType arch) where
  VSMinimal :: ValueSpec ty
  VSInt :: [IntConstraint] -> ValueSpec ('FTInt n)
  VSAnyPtr :: ValueSpec ('FTPtr ty)
  VSAllocPtr :: ValueSpec ('FTPtr ty)
  VSInitializedPtr :: ValueSpec ty -> ValueSpec ('FTPtr ty)
  VSStruct ::
    Ctx.Assignment ValueSpec fields ->
    ValueSpec ('FTStruct fields)
  VSArray :: Vector n (ValueSpec ty) -> ValueSpec ('FTArray n ty)

data Cursor (ty :: FullType arch) where
  Here :: Cursor ty
  Dereference :: Cursor ty -> Cursor ('FTPtr ty)
  Index :: (i <= n) => NatRepr i -> Cursor ty -> Cursor ('FTArray n ty)
  Field :: Ctx.Index fields ty -> Cursor ty -> Cursor ('FTStruct fields)

-- | LLVM types supported by symbolic simulator.
-- data SymType
--   = MemType MemType
--   | Alias L.Ident
--   | FunType FunDecl
--   | VoidType
--     -- | A type that LLVM does not know the structure of such as
--     -- a struct that is declared, but not defined.
--   | OpaqueType
--     -- | A type not supported by the symbolic simulator.
--   | UnsupportedType L.Type
--   deriving (Eq)

-- toFullType :: CrucibleTypes.CrucibleType -> MemType -> Maybe (Some (FullType arch))
      -- TODO How do we match up contexts of fields?
      -- do fieldList <-
      --      for
      --        (fmap MemType.fiType (MemType.siFields structInfo))
      --        (\fieldType ->
      --           do Some field <- toFullType fieldType
      --              Just (Some field))
      --    Just (Some (FTStruct (listToCtx fieldList))) -- TODO (?)
  -- ToCrucibleType FTFloat = CrucibleTypes.FloatType -- TODO floatinfo?

-- data Cursor
--   = Here
--   | Dereference Cursor
--   | Index !Word64 Cursor
--   | Field !Word64 Cursor
--   deriving Eq
