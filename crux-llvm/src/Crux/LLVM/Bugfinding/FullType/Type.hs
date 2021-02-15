{-
Module           : Crux.LLVM.Bugfinding.FullType.Type
Description      : 'FullType' is like a 'CrucibleTypes.CrucibleType' and a 'MemType'
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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Crux.LLVM.Bugfinding.FullType.Type
  ( type FullType(..)
  , FullTypeRepr(..)
  , PartTypeRepr(..)
  , MapToCrucibleType
  , ToCrucibleType
  , MapToBaseType
  , ToBaseType
  ) where

import           GHC.TypeLits (Nat)
import           Data.Functor.Const (Const(Const))
import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.Classes (OrdF(compareF), OrderingF(LTF, GTF, EQF))
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import qualified Data.Parameterized.TH.GADT as U

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemType as MemType

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
  ToCrucibleType ('FTInt n) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType n)
  ToCrucibleType ('FTPtr _ft :: FullType arch) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType ('FTArray _n ft) =
    CrucibleTypes.VectorType (ToCrucibleType ft)
  ToCrucibleType ('FTStruct ctx) =
    CrucibleTypes.StructType (MapToCrucibleType ctx)

type family MapToBaseType (ctx :: Ctx (FullType arch)) :: Ctx CrucibleTypes.BaseType where
  MapToBaseType 'Ctx.EmptyCtx   = Ctx.EmptyCtx
  MapToBaseType (xs 'Ctx.::> x) = MapToBaseType xs Ctx.::> ToBaseType x

-- | The type of annotated What4 values that correspond to each 'FullType'
type family ToBaseType (ft :: FullType arch) :: CrucibleTypes.BaseType where
  ToBaseType ('FTInt n) = CrucibleTypes.BaseBVType n
  ToBaseType ('FTPtr _ft :: FullType arch) = CrucibleTypes.BaseBVType (ArchWidth arch)
  ToBaseType ('FTStruct ctx) = CrucibleTypes.BaseStructType (MapToBaseType ctx)
  -- TODO(lb): BaseArrayType for Vector? It's not a BaseType in Crucible

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
  -- The Const is so that we can get type variables in scope in the TestEquality
  -- instance, see below.
  PTAliasRepr :: Const L.Ident ft -> PartTypeRepr arch ft

-- data IntConstraint = IntConstraint

-- -- Describe the structure of values and constraints on them
-- data ValueSpec (ty :: FullType arch) where
--   VSMinimal :: ValueSpec ty
--   VSInt :: [IntConstraint] -> ValueSpec ('FTInt n)
--   VSAnyPtr :: ValueSpec ('FTPtr ty) -- TODO just VSMinimal
--   VSAllocatedPtr :: ValueSpec ('FTPtr ty)
--   VSInitializedPtr :: ValueSpec ty -> ValueSpec ('FTPtr ty)
--   VSStruct ::
--     Ctx.Assignment ValueSpec fields ->
--     ValueSpec ('FTStruct fields)
--   VSArray :: Vector n (ValueSpec ty) -> ValueSpec ('FTArray n ty)

-- -- Should a Cursor say what type it points *to*?
-- data Cursor (ty :: FullType arch) where
--   Here :: Cursor ty
--   Dereference :: Cursor ty -> Cursor ('FTPtr ty)
--   Index :: (i <= n) => NatRepr i -> Cursor ty -> Cursor ('FTArray n ty)
--   Field :: Ctx.Index fields ty -> Cursor ty -> Cursor ('FTStruct fields)

-- addConstraint :: Constraint ty -> Cursor ty -> ValueSpec ty -> ValueSpec ty
-- addConstraint _ _ = _

-- gen :: Assignment ValueSpec argTypes -> (Mem, RegMap)
-- gen _ _ = _

-- setup ::
--   Mem ->
--   Assignment ValueSpec fts ->
--   ( RegMap (Map ToCrucibleType fts)
--   , MemImpl sym
--   , Map (Annotation sym) (Some Selector)
--   )

-- minimal :: FullTypeRepr ft -> RegValue (ToCrucibleType ft)
-- minimal :: FullTypeRepr ft -> ValueSpec ft

-- classify ::
--   Map (Annotation sym) ->
--   BadBehavior ->
--   [exists ft. (Selector ft, Constraint ft)]

-- modify ::
--   [exists ft. (Selector ft, Constraint ft)] ->
--   Map Symbol (Some ValueSpec) ->
--   Assignment ValueSpec fts ->
--   ( Map Symbol (Some ValueSpec)
--   , Assignment ValueSpec fts
--   )


-- expand :: Assignment ValueSpec fts -> Assignment ValueSpec fts
-- choose :: [Some Selector] -> Some Selector
-- expandable :: ValueSpec ft -> [Some Cursor]


$(return [])

instance TestEquality (FullTypeRepr arch) where
  testEquality =
    $(U.structuralTypeEquality [t|FullTypeRepr|]
      [ ( U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|PartTypeRepr|]) U.AnyType) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|FullTypeRepr|]) U.AnyType) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
        , [|testEquality|]
        )
      ]
    )

-- TODO(lb): We just assume (via unsafeCoerce) that types with the same L.Ident
-- are the same. Only valid when one L.Module is in use.
instance TestEquality (PartTypeRepr arch) where
  testEquality =
    $(U.structuralTypeEquality [t|PartTypeRepr|]
      [ ( U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|PartTypeRepr|]) U.AnyType) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
        , [|testEquality|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|])) U.AnyType
        , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                if ident1 == ident2 then (Just (unsafeCoerce Refl :: ft1 :~: ft2)) else Nothing |]
        )
      ]
    )

instance OrdF (FullTypeRepr arch) where
  compareF =
    $(U.structuralTypeOrd [t|FullTypeRepr|]
      [ ( U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|PartTypeRepr|]) U.AnyType) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|FullTypeRepr|]) U.AnyType) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
        , [|compareF|]
        )
      ]
    )

-- | See note on 'TestEquality' instance.
instance OrdF (PartTypeRepr arch) where
  compareF =
    $(U.structuralTypeOrd [t|PartTypeRepr|]
      [ ( U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|PartTypeRepr|]) U.AnyType) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
        , [|compareF|]
        )
      , ( U.TypeApp (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|])) U.AnyType
        , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                case compare ident1 ident2 of
                  LT -> unsafeCoerce LTF :: OrderingF ft1 ft2
                  GT -> unsafeCoerce GTF :: OrderingF ft1 ft2
                  EQ -> unsafeCoerce EQF :: OrderingF ft1 ft2
          |]
        )
      ]
    )
