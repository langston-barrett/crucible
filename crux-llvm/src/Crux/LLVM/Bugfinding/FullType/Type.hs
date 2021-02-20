{-
Module           : Crux.LLVM.Bugfinding.FullType.Type
Description      : 'FullType' is like a 'CrucibleTypes.CrucibleType' and a 'MemType.MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

A 'FullType' is like a 'CrucibleTypes.CrucibleType', but contains type
information through pointer references. Alternatively, it\'s like a
'MemType.MemType' that can be linked to a 'CrucibleTypes.CrucibleType' by
type-level information.

By using this machinery, we head off several sources of partiality/errors:

* By passing a 'FullType' instead of a 'MemType.MemType' and a
  'CrucibleTypes.CrucibleType', you can no longer pass incompatible/out-of-sync
  inputs.
* When building a @RegValue@, using 'FullType' can help prevent ill-typed
  pointers.
* There are a few sources of partiality in the 'MemType.MemType' to
  'CrucibleTypes.TypeRepr' translation that can be avoided, specifically
  ill-sized integer values.
* 'FullType' distinguishes between pointers and pointer-widths integers.

TODO: Split into Internal module, don't export PartTypeRepr constructors from
this module, see @asFullType@

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
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

-- These come from TH-generated code
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-inaccessible-code #-}

module Crux.LLVM.Bugfinding.FullType.Type
  ( type FullType(..)
  , FullTypeRepr(..)
  , PartTypeRepr(..)
  , MapToCrucibleType
  , ToCrucibleType
  , MapToBaseType
  , ToBaseType
  , isPtrRepr
  , IsPtrRepr(..)
  ) where

import           GHC.TypeLits (Nat)
import           Data.Kind (Type)
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
data FullType (m :: Type) where
  FTInt :: Nat -> FullType m
  FTFloat :: FullType m
  FTPtr :: FullType m -> FullType m
  FTArray :: Nat -> FullType m -> FullType m
  FTStruct :: Ctx.Ctx (FullType m) -> FullType m

type family MapToCrucibleType arch (ctx :: Ctx (FullType m)) :: Ctx CrucibleTypes.CrucibleType where
  MapToCrucibleType arch 'Ctx.EmptyCtx   = Ctx.EmptyCtx
  MapToCrucibleType arch (xs 'Ctx.::> x) = MapToCrucibleType arch xs Ctx.::> ToCrucibleType arch x

type family ToCrucibleType arch (ft :: FullType m) :: CrucibleTypes.CrucibleType where
  ToCrucibleType arch ('FTInt n) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType n)
  ToCrucibleType arch ('FTPtr _ft) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType arch ('FTArray _n ft) =
    CrucibleTypes.VectorType (ToCrucibleType arch ft)
  ToCrucibleType arch ('FTStruct ctx) =
    CrucibleTypes.StructType (MapToCrucibleType arch ctx)

type family MapToBaseType arch (ctx :: Ctx (FullType m)) :: Ctx CrucibleTypes.BaseType where
  MapToBaseType arch 'Ctx.EmptyCtx   = Ctx.EmptyCtx
  MapToBaseType arch (xs 'Ctx.::> x) = MapToBaseType arch xs Ctx.::> ToBaseType arch x

-- | The type of annotated What4 values that correspond to each 'FullType'
type family ToBaseType arch (ft :: FullType m) :: CrucibleTypes.BaseType where
  ToBaseType arch ('FTInt n) = CrucibleTypes.BaseBVType n
  ToBaseType arch ('FTPtr _ft) = CrucibleTypes.BaseNatType
  ToBaseType arch ('FTStruct ctx) = CrucibleTypes.BaseStructType (MapToBaseType arch ctx)
  -- TODO(lb): BaseArrayType for Vector? It's not a BaseType in Crucible

data FullTypeRepr m (ft :: FullType m) where
  FTIntRepr ::
    (1 <= w) =>
    NatRepr w ->
    FullTypeRepr m ('FTInt w)
  FTPtrRepr ::
    PartTypeRepr m ft ->
    FullTypeRepr m ('FTPtr ft)
  FTArrayRepr ::
    NatRepr n ->
    FullTypeRepr m ft ->
    FullTypeRepr m ('FTArray n ft)
  FTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment (FullTypeRepr m) fields ->
    FullTypeRepr m ('FTStruct fields)

-- | This functions similarly to 'MemType.SymType'
data PartTypeRepr m (ft :: FullType m) where
  PTFullRepr :: FullTypeRepr m ft -> PartTypeRepr m ft
  -- The Const is so that we can get type variables in scope in the TestEquality
  -- instance, see below.
  PTAliasRepr :: Const L.Ident ft -> PartTypeRepr m ft


data IsPtrRepr m ft = forall ft'. IsPtrRepr (ft :~: 'FTPtr ft')

isPtrRepr :: forall m ft. FullTypeRepr m ft -> Maybe (IsPtrRepr m ft)
isPtrRepr =
  \case
    FTPtrRepr _ -> Just (IsPtrRepr Refl)
    _ -> Nothing

-- data IntConstraint = IntConstraint

-- -- Describe the structure of values and constraints on them
-- data ValueSpec (ty :: FullType) where
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
-- data Cursor (ty :: FullType) where
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

-- | We assume (via unsafeCoerce) that types with the same L.Ident are the same.
-- This is validated by the existential used in @makeModuleTypes@.
instance TestEquality (PartTypeRepr m) where
  testEquality =
    $(U.structuralTypeEquality [t|PartTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|]))
            , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                    if ident1 == ident2 then (Just (unsafeCoerce Refl :: ft1 :~: ft2)) else Nothing |]
            )
          ]))

instance TestEquality (FullTypeRepr m) where
  testEquality =
    $(U.structuralTypeEquality [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|PartTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          ]))

-- | See note on 'TestEquality' instance.
instance OrdF (PartTypeRepr m) where
  compareF =
    $(U.structuralTypeOrd [t|PartTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|]))
            , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                    case compare ident1 ident2 of
                      LT -> unsafeCoerce LTF :: OrderingF ft1 ft2
                      GT -> unsafeCoerce GTF :: OrderingF ft1 ft2
                      EQ -> unsafeCoerce EQF :: OrderingF ft1 ft2
              |]
            )
          ]))


instance OrdF (FullTypeRepr m) where
  compareF =
    $(U.structuralTypeOrd [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|PartTypeRepr|]))
            , [|compareF|]
            )
          ]))
