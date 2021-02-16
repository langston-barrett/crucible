{-
Module       : Crux.LLVM.Bugfinding.Setup.Annotation
Description  : TODO
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Crux.LLVM.Bugfinding.Setup.Annotation
  ( Annotation
  , symAnnotation
  , makeAnnotation
  ) where

import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))

import           Data.Parameterized.Classes (OrdF(compareF))
import qualified Data.Parameterized.TH.GADT as U

import qualified What4.Interface as What4

import           Crux.LLVM.Bugfinding.FullType (FullTypeRepr, FullRepr, ToBaseType, toFullRepr)

data Annotation arch sym ft =
  forall full.
  Annotation
    { symAnnotation :: What4.SymAnnotation sym (ToBaseType ft)
    , annfullRepr :: FullRepr full
    , annFullTypeRepr :: FullTypeRepr full arch ft
    }

makeAnnotation ::
  FullTypeRepr full arch ft ->
  What4.SymAnnotation sym (ToBaseType ft) ->
  Annotation arch sym ft
makeAnnotation ftRepr ann = Annotation ann (toFullRepr ftRepr) ftRepr

$(return [])

instance TestEquality (What4.SymAnnotation sym) => TestEquality (Annotation arch sym) where
  testEquality =
    $(U.structuralTypeEquality [t|Annotation|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|testEquality|]
            )
          , ( appAny (U.ConType [t|FullRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|What4.SymAnnotation|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (What4.SymAnnotation sym) => OrdF (Annotation arch sym) where
  compareF =
    $(U.structuralTypeOrd [t|Annotation|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (appAny (U.ConType [t|FullTypeRepr|])))
            , [|compareF|]
            )
          , ( appAny (U.ConType [t|FullRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|What4.SymAnnotation|]))
            , [|compareF|]
            )
          ]))
