{-
Module       : Crux.LLVM.Bugfinding.Constraints
Description  : Descriptions of function preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Crux.LLVM.Bugfinding.Constraints
  ( Constraint(..)
  , ppConstraint
  , RelationalConstraint(..)
  , Selector(..)
  , ValueConstraint(..)
  , SomeValueConstraint(..)
  , Constraints(..)
  , emptyConstraints
  , isEmpty
  , oneArgumentConstraint

  -- * Pretty-printing
  , ppValueConstraint
  , ppConstraints
  ) where

import           Control.Lens (set)
import           Data.Functor.Const
import           Data.Functor.Compose (Compose(Compose))
import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (isJust)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF(ixF), OrdF(compareF, leqF), OrderingF(LTF, GTF, EQF))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (allFC, toListFC)

import           Lang.Crucible.LLVM.DataLayout (fromAlignment, Alignment)

import           Crux.LLVM.Bugfinding.Cursor
import           Crux.LLVM.Bugfinding.FullType.Type (FullType(..), FullTypeRepr)

data Constraint m (atTy :: FullType m) where
  Allocated :: Constraint m ('FTPtr ft)
  -- ^ This pointer is not null
  Initialized :: Constraint m ('FTPtr ft)
  -- ^ This pointer points to initialized memory
  Aligned :: Alignment -> Constraint m ('FTPtr ft)
  -- ^ This pointer has at least this alignment
  SizeAtLeast :: !Int -> Constraint m ('FTPtr ft)
  -- ^ The allocation backing this pointer has at least this size

data SomeConstraint m
  = forall ft. SomeConstraint (Constraint m ft)

-- | Ignores type indices
instance Eq (SomeConstraint m) where
  SomeConstraint c1 == SomeConstraint c2 =
    case (c1, c2) of
      (Allocated, Allocated) -> True
      (Initialized, Initialized) -> True
      (Aligned align, Aligned align') -> align == align'
      (SizeAtLeast n, SizeAtLeast n') -> n == n'
      _ -> False

-- | Ignores type indices
instance Ord (SomeConstraint m) where
  compare (SomeConstraint c1) (SomeConstraint c2) =
    case (c1, c2) of
      (Allocated, Allocated) -> EQ
      (Allocated, _) -> LT
      (Initialized, Initialized) -> EQ
      (Initialized, _) -> LT
      (Aligned align, Aligned align') -> compare align align'
      (Aligned _, _) -> LT
      (SizeAtLeast i, SizeAtLeast i') -> compare i i'
      (SizeAtLeast _, _) -> GT

data ValueConstraint m inTy atTy
  = ValueConstraint
      { inTypeRepr :: FullTypeRepr m inTy
      , constraintCursor :: Cursor m inTy atTy
      , constraintBody :: Constraint m atTy
      }

data SomeValueConstraint m inTy
  = forall atTy. SomeValueConstraint (ValueConstraint m inTy atTy)

instance Eq (SomeValueConstraint m inTy) where
  SomeValueConstraint (ValueConstraint inTyRep1 cursor1 body1) ==
    SomeValueConstraint (ValueConstraint inTyRep2 cursor2 body2) =
    SomeConstraint body1 == SomeConstraint body2 &&
    isJust (testEquality cursor1 cursor2) &&
    isJust (testEquality inTyRep1 inTyRep2)

instance Ord (SomeValueConstraint m inTy) where
  SomeValueConstraint (ValueConstraint inTyRep1 cursor1 body1) <=
    SomeValueConstraint (ValueConstraint inTyRep2 cursor2 body2) =
    (SomeConstraint body1 <= SomeConstraint body2)
    && leqF cursor1 cursor2
    && leqF inTyRep1 inTyRep2

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint m arch argTypes
  = forall inTy inTy' ft ft'.
    SizeOfAllocation
      (Selector m argTypes inTy ('FTInt ft))
      (Selector m argTypes inTy' ('FTPtr ft'))
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second

instance Eq (RelationalConstraint m arch argTypes) where
  rc1 == rc2 = error "TODO eq relationalconstraint"

instance Ord (RelationalConstraint m arch argTypes) where
  rc1 <= rc2 = error "TODO ord relationalconstraint"

data Constraints m arch argTypes
  = Constraints
      { argConstraints :: Ctx.Assignment (Compose Set (SomeValueConstraint m)) argTypes
      , globalConstraints :: Map L.Symbol (Set (Some (SomeValueConstraint m)))
      , relationalConstraints :: Set (RelationalConstraint m arch argTypes)
      }

instance Eq (Constraints m arch argTypes) where
  cs1 == cs2 =
    and [ allFC
            getConst
            (Ctx.zipWith
               (\(Compose s1) (Compose s2) -> Const (s1 == s2))
               (argConstraints cs1)
               (argConstraints cs2))
        , globalConstraints cs1 == globalConstraints cs2
        , relationalConstraints cs1 == relationalConstraints cs2
        ]

-- | Union
--
-- TODO: Merge identical constraints?
instance Semigroup (Constraints m arch types) where
  cs1 <> cs2 =
    Constraints
      { argConstraints =
          Ctx.zipWith
            (\(Compose s1) (Compose s2) -> Compose (s1 <> s2))
            (argConstraints cs1)
            (argConstraints cs2)
      , globalConstraints = globalConstraints cs1 <> globalConstraints cs2
      , relationalConstraints = relationalConstraints cs1 <> relationalConstraints cs2
      }

emptyConstraints :: Ctx.Size argTypes -> Constraints m arch argTypes
emptyConstraints sz =
  Constraints
    { argConstraints = Ctx.generate sz (\_index -> Compose Set.empty)
    , globalConstraints = Map.empty
    , relationalConstraints = Set.empty
    }

isEmpty :: Constraints m arch argTypes -> Bool
isEmpty cs@(Constraints argCs _ _) = emptyConstraints (Ctx.size argCs) == cs

ppConstraint :: Constraint m ft -> Doc Void
ppConstraint =
  \case
    Allocated ->
      PP.pretty "is allocated"
    Initialized ->
      PP.pretty "is initialized"
    Aligned alignment ->
      PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    SizeAtLeast size ->
      PP.pretty "has size at least " <> PP.viaShow size

ppValueConstraint' :: String -> ValueConstraint m inTy atTy -> Doc Void
ppValueConstraint' top (ValueConstraint _ty cursor body) =
  ppCursor top cursor <> PP.pretty ": " <> ppConstraint body

ppValueConstraint :: ValueConstraint m inTy atTy -> Doc Void
ppValueConstraint = ppValueConstraint' "<top>"

ppConstraints :: Constraints m arch argTypes -> Doc Void
ppConstraints (Constraints argCs globCs _relCs) =
  let ppArgC idx (Compose constraints) =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Argument #" <> PP.viaShow (Ctx.indexVal idx)
                   -- TODO: Use argument names
                   : map (\(SomeValueConstraint vc) -> ppValueConstraint vc)
                         (Set.toList constraints)
                   ))
      ppGlobC (L.Symbol sym) constraints =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Global " <> PP.pretty sym
                   : map (\(Some (SomeValueConstraint vc)) -> ppValueConstraint vc)
                         (Set.toList constraints)
                   ))
  in PP.vsep $ toListWithIndex ppArgC argCs ++ map (uncurry ppGlobC) (Map.toList globCs)
  where
    toListWithIndex :: (forall tp. Ctx.Index ctx tp -> f tp -> a)
                    -> Ctx.Assignment f ctx
                    -> [a]
    toListWithIndex f assign =
      toListFC getConst $
        Ctx.generate (Ctx.size assign) (\idx -> Const (f idx (assign Ctx.! idx)))


oneArgumentConstraint ::
  Ctx.Size argTypes ->
  Ctx.Index argTypes inTy ->
  Set (SomeValueConstraint m inTy) ->
  Constraints m arch argTypes
oneArgumentConstraint sz idx constraints =
  let empty = emptyConstraints sz
  in empty
       { argConstraints =
           set (ixF idx) (Compose constraints) (argConstraints empty)
       }

-- TODO split modules
$(return [])

instance TestEquality (ValueConstraint m inTy) where
  testEquality =
    $(U.structuralTypeEquality [t|ValueConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Constraint|]))
            , [|\cs1 cs2 ->
                  if SomeConstraint cs1 == SomeConstraint cs2
                  then Just Refl
                  else Nothing |]
            )
          ]))

instance OrdF (ValueConstraint m inTy) where
  compareF =
    $(U.structuralTypeOrd [t|ValueConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [
            ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Constraint|]))
            , [| \cs1 cs2 ->
                   case compare (SomeConstraint cs1) (SomeConstraint cs2) of
                     LT -> LTF
                     GT -> GTF
                     EQ -> EQF |]
            )
          ]))

instance TestEquality (SomeValueConstraint m) where
  testEquality
    (SomeValueConstraint vc1@(ValueConstraint inTy _ _))
    (SomeValueConstraint vc2@(ValueConstraint inTy' _ _)) =
    case testEquality inTy inTy' of
      Just Refl ->
        if isJust (testEquality vc1 vc2)
        then Just Refl
        else Nothing
      Nothing -> Nothing
