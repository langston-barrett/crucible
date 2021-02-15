{-
Module           : Crux.LLVM.Bugfinding.FullType.Type
Description      : 'FullType' is like a 'CrucibleTypes.CrucibleType' and a 'MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
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
  , type Full(..)
  , FullTypeRepr(..)
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

data Full
  = Full
  | Part

-- | A 'FullTypeRepr' has enough information to recover a
-- 'CrucibleTypes.CrucibleType'.
--
-- The parameter @full@ indicates whether this type is under a 'FTPtrRepr'. If
-- @full@ is @True@, then the type doesn't have enough information to recover a
-- 'CrucibleTypes.CrucibleType'.
data FullTypeRepr (full :: Full) arch (ft :: FullType arch) where
  FTIntRepr :: (1 <= w) => NatRepr w -> FullTypeRepr full arch ('FTInt w)
  FTPtrRepr :: FullTypeRepr 'Part arch ft -> FullTypeRepr full arch ('FTPtr ft)
  FTArrayRepr :: NatRepr n -> FullTypeRepr full arch ft -> FullTypeRepr full arch ('FTArray n ft)
  FTFullStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment CrucibleTypes.TypeRepr (MapToCrucibleType fields) ->
    Ctx.Assignment (FullTypeRepr full arch) fields ->
    FullTypeRepr full arch ('FTStruct fields)
  FTPartStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment (FullTypeRepr 'Part arch) fields ->
    FullTypeRepr 'Part arch ('FTStruct fields)
  -- The Const is so that we can get type variables in scope in the TestEquality
  -- instance, see below.
  FTAliasRepr :: Const L.Ident ft -> FullTypeRepr 'Part arch ft

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

-- TODO(lb): We just assume (via unsafeCoerce) that types with the same L.Ident
-- are the same. Only valid when one L.Module is in use.
instance TestEquality (FullTypeRepr 'Full arch) where
  testEquality =
    $(U.structuralTypeEquality [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|]))
            , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                    if ident1 == ident2 then (Just (unsafeCoerce Refl :: ft1 :~: ft2)) else Nothing |]
            )
          ]))

-- | See note on 'TestEquality' instance.
instance OrdF (FullTypeRepr 'Full arch) where
  compareF =
    $(U.structuralTypeOrd [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
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

instance TestEquality (FullTypeRepr 'Part arch) where
  testEquality =
    $(U.structuralTypeEquality [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|]))
            , [| \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                    if ident1 == ident2 then (Just (unsafeCoerce Refl :: ft1 :~: ft2)) else Nothing |]
            )
          ]))

instance OrdF (FullTypeRepr 'Part arch) where
  compareF =
    $(U.structuralTypeOrd [t|FullTypeRepr|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
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
