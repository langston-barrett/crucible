{-
Module       : Crux.LLVM.Bugfinding.Constraints
Description  : Descriptions of function preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

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
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF(ixF))

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

data ValueConstraint
  = ValueConstraint
      { constraintBody :: Constraint
      , constraintCursor :: Cursor
      }
  deriving (Eq, Ord)

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint m arch argTypes
  = SizeOfAllocation (Selector m argTypes) (Selector m argTypes)
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second
  deriving (Eq, Ord)

data Constraints m arch argTypes
  = Constraints
      { argConstraints :: Ctx.Assignment (Const (Set ValueConstraint)) argTypes
      , globalConstraints :: Map L.Symbol (Set ValueConstraint)
      , relationalConstraints :: Set (RelationalConstraint m arch argTypes)
      }

instance Eq (Constraints m arch argTypes) where
  cs1 == cs2 =
    and [ toListFC getConst (argConstraints cs1) == toListFC getConst (argConstraints cs2)
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
            (\e1 e2 -> Const (getConst e1 <> getConst e2))
            (argConstraints cs1)
            (argConstraints cs2)
      , globalConstraints = globalConstraints cs1 <> globalConstraints cs2
      , relationalConstraints = relationalConstraints cs1 <> relationalConstraints cs2
      }

emptyConstraints :: Ctx.Size argTypes -> Constraints m arch argTypes
emptyConstraints sz =
  Constraints
    { argConstraints = Ctx.generate sz (\_index -> Const Set.empty)
    , globalConstraints = Map.empty
    , relationalConstraints = Set.empty
    }

isEmpty :: Constraints m arch argTypes -> Bool
isEmpty (Constraints argCs globCs relCs) =
  and [ allFC ((== Set.empty) . getConst) argCs
      , globCs == Map.empty
      , relCs == Set.empty
      ]

ppConstraint :: Constraint -> Doc Void
ppConstraint =
  \case
    Allocated -> PP.pretty "is allocated"
    Initialized -> PP.pretty "is initialized"
    Aligned alignment -> PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    SizeAtLeast size -> PP.pretty "has size at least " <> PP.viaShow size

ppValueConstraint' :: String -> ValueConstraint -> Doc Void
ppValueConstraint' top (ValueConstraint body cursor) =
  ppCursor top cursor <> PP.pretty ": " <> ppConstraint body

ppValueConstraint :: ValueConstraint -> Doc Void
ppValueConstraint = ppValueConstraint' "<top>"

ppConstraints :: Constraints m arch argTypes -> Doc Void
ppConstraints (Constraints argCs globCs _relCs) =
  let ppArgC idx (Const constraints) =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Argument #" <> PP.viaShow (Ctx.indexVal idx)
                   -- TODO: Use argument names
                   : map ppValueConstraint (Set.toList constraints)
                   ))
      ppGlobC (L.Symbol sym) constraints =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Global " <> PP.pretty sym
                   : map ppValueConstraint (Set.toList constraints)
                   ))
  -- TODO: print relCs
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
  Ctx.Index argTypes ft ->
  Set ValueConstraint ->
  Constraints m arch argTypes
oneArgumentConstraint sz idx constraints =
  let empty = emptyConstraints sz
  in empty
       { argConstraints =
           set (ixF idx) (Const constraints) (argConstraints empty)
       }
