{-
Module           : UCCrux.LLVM.FullType.Maps
Description      : Total parameterized maps
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.FullType.Maps
  (
  )
where

import           Control.Lens.Indexed (ifoldr)
import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))

import           Data.Parameterized.Classes (OrdF(compareF), fromOrdering)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair (Pair(Pair))
import qualified Data.Parameterized.TH.GADT as U

import           UCCrux.LLVM.Module (DeclSymbol, DeclMap)
import           UCCrux.LLVM.FullType.Type (FuncSigRepr, FullTypeRepr)

-- | Invariant: Has one entry per declaration in the module @m@.
data TypedDeclSymbol m fs =
  TypedDeclSymbol
    { typedDeclSymbol :: DeclSymbol m
    , typedDeclRepr :: FuncSigRepr m fs
    }

newtype TypedDeclMap m f = TypedDeclMap
  {getTypedDeclMap :: MapF (TypedDeclSymbol m) f}

mkDeclMapF ::
  (DeclSymbol m -> a -> Pair (FuncSigRepr m) f) ->
  DeclMap m a -> 
  TypedDeclMap m f
mkDeclMapF f =
  ifoldr
    (\symb val typedMap ->
       case f symb val of
         Pair rep v -> typedInsert (TypedDeclSymbol symb rep) v typedMap)
    (TypedDeclMap MapF.empty)
  where
    typedInsert k v typedMap =
          TypedDeclMap (MapF.insert k v (getTypedDeclMap typedMap))

-- ------------------------------------------------------------------------------
-- Instances

$(return [])

instance TestEquality (TypedDeclSymbol m) where
  testEquality =
    $( U.structuralTypeEquality
         [t|TypedDeclSymbol|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FuncSigRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (U.ConType [t|DeclSymbol|]),
                   [|\s1 s2 -> if s1 == s2 then Just Refl else Nothing|]
                 )
               ]
         )
     )

instance OrdF (TypedDeclSymbol m) where
  compareF =
    $( U.structuralTypeOrd
         [t|TypedDeclSymbol|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FuncSigRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (U.ConType [t|DeclSymbol|]),
                   [|\s1 s2 -> fromOrdering (compare s1 s2)|]
                 )
               ]
         )
     )
