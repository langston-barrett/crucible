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

import           GHC.TypeLits as GHC
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
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.Vector (Vector)

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Overrides (ArchOk)


-- | Type level only
--
-- Like a 'CrucibleTypes.CrucibleType', but contains type information through
-- pointer references. This requires handling recursive types.
--
-- Alternatively, like a 'MemType' that's linked to a
-- 'CrucibleTypes.CrucibleType' by type-level information.
data FullType arch (names :: Ctx GHC.Symbol) where
  FTAlias :: Symbol -> FullType arch names -> FullType arch names
  FTRec :: FullType arch (names Ctx.::> symb)
  FTWeak :: FullType arch (names Ctx.::> symb)
  FTInt :: Nat -> FullType arch names
  FTFloat :: FullType arch names
  FTPtr :: FullType arch names -> FullType arch names
  FTArray :: Nat -> FullType arch names -> FullType arch names
  FTStruct :: Ctx.Ctx (FullType arch names) -> FullType arch names

-- | Map a type family or parameterized type over a 'Ctx'.
type family MapToCrucibleType (ctx :: Ctx (FullType arch names)) :: Ctx CrucibleTypes.CrucibleType where
  MapToCrucibleType 'Ctx.EmptyCtx   = Ctx.EmptyCtx
  MapToCrucibleType (xs 'Ctx.::> x) = MapToCrucibleType xs Ctx.::> ToCrucibleType x

type family ToCrucibleType (ft :: FullType arch names) :: CrucibleTypes.CrucibleType where
  ToCrucibleType (FTInt n) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType n)
  ToCrucibleType (FTPtr _ft :: FullType arch names) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType (FTArray _n ft) =
    CrucibleTypes.VectorType (ToCrucibleType ft)
  ToCrucibleType (FTStruct ctx) =
    CrucibleTypes.StructType (MapToCrucibleType ctx)

data SomeFullType arch tp where
  SomeFullType :: FullTypeRepr (ft :: FullType arch names) -> ToCrucibleType ft :~: tp -> SomeFullType arch tp

data SomeFullTypeRepr arch where
  SomeFullTypeRepr :: FullTypeRepr (ft :: FullType arch names) -> SomeFullTypeRepr arch

data FullTypeRepr (ft :: FullType arch names) where
  FTIntRepr :: NatRepr w -> FullTypeRepr ('FTInt w)
  FTPtrRepr :: FullTypeRepr ft -> FullTypeRepr ('FTPtr ft)
  FTArrayRepr :: NatRepr n -> FullTypeRepr ft -> FullTypeRepr ('FTArray n ft)
  FTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment FullTypeRepr fields ->
    FullTypeRepr ('FTStruct fields)
  FTRecRepr :: SymbolRepr symb -> FullTypeRepr ('FTRec :: FullType arch (names Ctx.::> symb))

toFullType :: ArchOk arch => proxy arch -> MemType -> Maybe (SomeFullTypeRepr arch)
toFullType proxy =
  \case
    PtrType (MemType memType) ->
      do SomeFullTypeRepr pointedTo <- toFullType proxy memType
         Just (SomeFullTypeRepr (FTPtrRepr pointedTo))
    PtrType (Alias (L.Ident ident)) ->
      case someSymbol (Text.pack ident) of
        Some (symRepr :: SymbolRepr symb) ->
          Just (SomeFullTypeRepr (FTRecRepr symRepr))
    PtrType _ -> Nothing -- TODO

-- liftRefl ::
--   Ctx.Assignment (f a :~:) ctx ->
--   Ctx.Assignment f ctx' ->
-- liftRefl = _

-- Ctx.Assignment (SomeFullType arch) fields
-- Ctx.Assignment FullTypeRepr (Map ToCrucibleType fields')

toFullType' ::
  forall proxy arch tp.
  ( ?lc :: TypeContext
  , ArchOk arch
  ) =>
  proxy arch ->
  MemType ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (SomeFullType arch tp)
toFullType' proxy memType typeRepr =
  case CrucibleTypes.asBaseType typeRepr of
    CrucibleTypes.AsBaseType baseTypeRepr -> error "unim"
    CrucibleTypes.NotBaseType ->
      case typeRepr of
        LLVMMem.LLVMPointerRepr w ->
          case (memType, testEquality ?ptrWidth w) of
            (PtrType symType, Just Refl) ->
              -- TODO aliases?
              case asMemType symType of
                Left _ -> Nothing
                Right memType ->
                  do SomeFullTypeRepr contained <- toFullType proxy memType
                     Just (SomeFullType (FTPtrRepr contained) Refl)
            (IntType _w, _) ->
              -- TODO assert about _w
              Just (SomeFullType (FTIntRepr w) Refl)
            _ -> error "bad memtype combo"
        CrucibleTypes.VectorRepr containedTypeRepr ->
          case memType of
            VecType n memType' ->
              do SomeFullType contained Refl <-
                   toFullType' proxy memType' containedTypeRepr
                 Some natRepr <- pure $ mkNatRepr n
                 Just (SomeFullType (FTArrayRepr natRepr contained) Refl)
            _ -> error "bad memtype combo"
        CrucibleTypes.StructRepr
          (fieldTypes :: Ctx.Assignment CrucibleTypes.TypeRepr fields) ->
          case memType of
            StructType structInfo ->
              do assign :: Ctx.Assignment (SomeFullType arch) fields <-
                   Ctx.generateM  -- in Maybe
                    (Ctx.size fieldTypes)
                    (\idx ->
                      toFullType'
                        proxy
                        -- TODO(lb) unsafe indexing here
                        (MemType.fiType $ MemType.siFields structInfo Vec.! Ctx.indexVal idx)
                        (fieldTypes Ctx.! idx))
                 Just (SomeFullType (FTStructRepr structInfo _) Refl)
            _ -> error "bad memtype combo"
        _ -> undefined

data IntConstraint = IntConstraint

data ValueSpec (names :: Ctx GHC.Symbol) (ty :: FullType arch names) where
  VSMinimal :: ValueSpec names ty
  VSInt :: [IntConstraint] -> ValueSpec names ('FTInt n)
  VSAnyPtr :: ValueSpec names ('FTPtr ty)
  VSAllocPtr :: ValueSpec names ('FTPtr ty)
  VSInitializedPtr :: ValueSpec names ty -> ValueSpec names ('FTPtr ty)
  VSStruct ::
    Ctx.Assignment (ValueSpec names) fields ->
    ValueSpec names ('FTStruct fields)
  VSArray :: Vector n (ValueSpec names ty) -> ValueSpec names ('FTArray n ty)

data Cursor (names :: Ctx GHC.Symbol) (ty :: FullType arch names) where
  Here :: Cursor names ty
  Dereference :: Cursor names ty -> Cursor names ('FTPtr ty)
  Index :: (i <= n) => NatRepr i -> Cursor names ty -> Cursor names ('FTArray n ty)
  Field ::
    Ctx.Index fields ty ->
    Cursor names ty ->
    Cursor names ('FTStruct fields)

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
