{-
Module       : Crux.LLVM.Bugfinding.Constraints
Description  : Descriptions of function preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

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
import           Data.Functor.Compose (Compose(Compose, getCompose))
import           Data.Type.Equality (TestEquality(testEquality))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (isJust)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF(ixF), OrdF(compareF, leqF))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (allFC, toListFC)

import           Lang.Crucible.LLVM.DataLayout (fromAlignment, Alignment)

import           Crux.LLVM.Bugfinding.Cursor

-- | A constraint on a single value
data Constraint
  = Allocated
  -- ^ This pointer is not null
  | Initialized
  -- ^ This pointer points to initialized memory
  | Aligned Alignment
  -- ^ This pointer has at least this alignment
  | SizeAtLeast !Int
  -- ^ The allocation backing this pointer has at least this size
  deriving (Eq, Ord)

data ValueConstraint m ft
  = ValueConstraint
      { constraintBody :: Constraint
      , constraintCursor :: Cursor m ft
      -- TODO un-some
      }

instance Eq (ValueConstraint m ft) where
  ValueConstraint body1 cursor1 == ValueConstraint body2 cursor2 =
    body1 == body1 && isJust (testEquality cursor1 cursor2)

instance Ord (ValueConstraint m ft) where
  ValueConstraint body1 cursor1 <= ValueConstraint body2 cursor2 =
    body1 <= body1 && leqF cursor1 cursor2

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint m arch argTypes ft
  = SizeOfAllocation (Selector m argTypes ft) (Selector m argTypes ft)
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second

data Constraints m arch argTypes
  = Constraints
      { argConstraints :: Ctx.Assignment (Compose Set (ValueConstraint m)) argTypes
      , globalConstraints :: Map L.Symbol (Set (Some (ValueConstraint m)))
      , relationalConstraints :: Set (Some (RelationalConstraint m arch argTypes))
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

ppConstraint :: Constraint -> Doc Void
ppConstraint =
  \case
    Allocated -> PP.pretty "is allocated"
    Initialized -> PP.pretty "is initialized"
    Aligned alignment -> PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    SizeAtLeast size -> PP.pretty "has size at least " <> PP.viaShow size

ppValueConstraint' :: String -> ValueConstraint m ft -> Doc Void
ppValueConstraint' top (ValueConstraint body cursor) =
  ppCursor top cursor <> PP.pretty ": " <> ppConstraint body

ppValueConstraint :: ValueConstraint m ft -> Doc Void
ppValueConstraint = ppValueConstraint' "<top>"

ppConstraints :: Constraints m arch argTypes -> Doc Void
ppConstraints (Constraints argCs globCs _relCs) =
  let ppArgC idx (Compose constraints) =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Argument #" <> PP.viaShow (Ctx.indexVal idx)
                   -- TODO: Use argument names
                   : map ppValueConstraint (Set.toList constraints)
                   ))
      -- ppGlobC (L.Symbol sym) constraints =
      --   PP.nest
      --     2
      --     (PP.vsep ( PP.pretty "Global " <> PP.pretty sym
      --              : map ppValueConstraint (Set.toList constraints)
      --              ))
  -- TODO: print relCs, globCs
  in PP.vsep $ toListWithIndex ppArgC argCs -- ++ map (uncurry ppGlobC) (Map.toList globCs)
  where
    toListWithIndex :: (forall tp. Ctx.Index ctx tp -> f tp -> a)
                    -> Ctx.Assignment f ctx
                    -> [a]
    toListWithIndex f assign =
      toListFC getConst $
        Ctx.generate (Ctx.size assign) (\idx -> Const (f idx (assign Ctx.! idx)))


oneArgumentConstraint ::
  Ctx.Size argTypes ->
  Ctx.Index argTypes ft ->
  Set (ValueConstraint m ft) ->
  Constraints m arch argTypes
oneArgumentConstraint sz idx constraints =
  let empty = emptyConstraints sz
  in empty
       { argConstraints =
           set (ixF idx) (Compose constraints) (argConstraints empty)
       }

-- TODO split modules
$(return [])

instance TestEquality (ValueConstraint m) where
  testEquality =
    $(U.structuralTypeEquality [t|ValueConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (ValueConstraint m) where
  compareF =
    $(U.structuralTypeOrd [t|ValueConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [
            ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))

instance TestEquality (RelationalConstraint m arch argTypes) where
  testEquality =
    $(U.structuralTypeEquality [t|RelationalConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Selector|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (RelationalConstraint m arch argTypes) where
  compareF =
    $(U.structuralTypeOrd [t|RelationalConstraint|]
      (let appAny con = U.TypeApp con U.AnyType
       in [
            ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|compareF|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Selector|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))
