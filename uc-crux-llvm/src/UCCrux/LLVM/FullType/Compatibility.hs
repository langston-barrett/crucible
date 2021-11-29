{-
Module           : UCCrux.LLVM.FullType.Compatibility
Description      : Type compatibility
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.FullType.Compatibility
  ( CompatTypes(..),
  )
where

{- ORMOLU_DISABLE -}
import           Data.Type.Equality (TestEquality(testEquality))

import           Data.Parameterized.Classes (OrdF(compareF))
import qualified Data.Parameterized.TH.GADT as U

import           UCCrux.LLVM.FullType.Type (FullType(FTInt, FTPtr), FullTypeRepr)
{- ORMOLU_ENABLE -}

data CompatTypes m (ft1 :: FullType m) (ft2 :: FullType m) where
  -- Base case

  CompatRefl :: FullTypeRepr m ft -> CompatTypes m ft ft

  -- Boring recursive cases

  CompatPtr ::
    CompatTypes m ft1 ft2 ->
    CompatTypes m ('FTPtr ft1) ('FTPtr ft2)

  -- Interesting cases

  -- | Any pointer is compatible with a @void*@ or @char*@
  CompatBytes ::
    FullTypeRepr m ft ->
    CompatTypes m ('FTPtr ('FTInt 8)) ('FTPtr ft)

$(return [])

instance TestEquality (CompatTypes m ft1) where
  testEquality =
    $( U.structuralTypeEquality
         [t|CompatTypes|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|CompatTypes|]))),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (CompatTypes m ft1) where
  compareF =
    $( U.structuralTypeOrd
         [t|CompatTypes|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|CompatTypes|]))),
                   [|compareF|]
                 )
               ]
         )
     )
