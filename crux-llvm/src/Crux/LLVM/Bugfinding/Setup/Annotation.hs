{-
Module       : Crux.LLVM.Bugfinding.Setup.Annotation
Description  : TODO
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
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

import           Data.Type.Equality (TestEquality(testEquality))

import           Data.Parameterized.Classes (OrdF(compareF))
import qualified Data.Parameterized.TH.GADT as U

import qualified What4.Interface as What4

import           Crux.LLVM.Bugfinding.FullType (FullType(FTPtr), FullTypeRepr, ToBaseType)

data Annotation m arch sym ft =
  Annotation
    { symAnnotation :: What4.SymAnnotation sym (ToBaseType arch ('FTPtr ft))
    , _annFullTypeRepr :: FullTypeRepr m ('FTPtr ft)
    }

makeAnnotation ::
  FullTypeRepr m ('FTPtr ft) ->
  What4.SymAnnotation sym (ToBaseType arch ('FTPtr ft)) ->
  Annotation m arch sym ft
makeAnnotation ftRepr ann = Annotation ann ftRepr

$(return [])

instance TestEquality (What4.SymAnnotation sym) => TestEquality (Annotation m arch sym) where
  testEquality =
    $(U.structuralTypeEquality [t|Annotation|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|What4.SymAnnotation|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (What4.SymAnnotation sym) => OrdF (Annotation m arch sym) where
  compareF =
    $(U.structuralTypeOrd [t|Annotation|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|What4.SymAnnotation|]))
            , [|compareF|]
            )
          ]))
