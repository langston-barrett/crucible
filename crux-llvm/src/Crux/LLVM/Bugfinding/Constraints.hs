{-
Module       : Crux.LLVM.Bugfinding.Constraints
Description  : Descriptions of function preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE PolyKinds #-}

module Crux.LLVM.Bugfinding.Constraints
  ( Constraint(..)
  , RelationalConstraint(..)
  , Selector(..)
  , ValueConstraint(..)
  , Constraints(..)
  , emptyConstraints
  , oneArgumentConstraint
  ) where

import           Control.Lens (set)
import           Data.Functor.Const
import           Data.Map (Map)
import qualified Data.Map as Map

import           Data.Parameterized.Classes (IxedF(ixF))

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import           Crux.LLVM.Bugfinding.Cursor

-- | A constraint on a single value
data Constraint
  = NotNull
  -- ^ This pointer is not null
  | SizeAtLeast !Int
  -- ^ The allocation backing this pointer has at least this size

data ValueConstraint
  = ValueConstraint
      { constraintBody :: Constraint
      , constraintCursor :: Cursor
      }

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint argTypes
  = SizeOfAllocation (Selector argTypes) (Selector argTypes)
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second

data Constraints argTypes
  = Constraints
      { argConstraints :: Ctx.Assignment (Const [ValueConstraint]) argTypes
      , globalConstraints :: Map L.Symbol ValueConstraint
      , relationalConstraints :: [RelationalConstraint argTypes]
      }

emptyConstraints :: Ctx.Size argTypes -> Constraints argTypes
emptyConstraints sz =
  Constraints
    { argConstraints = Ctx.generate sz (\_index -> Const [])
    , globalConstraints = Map.empty
    , relationalConstraints = []
    }

oneArgumentConstraint ::
  Ctx.Size argTypes ->
  Ctx.Index argTypes tp ->
  [ValueConstraint] ->
  Constraints argTypes
oneArgumentConstraint sz idx constraints =
  let empty = emptyConstraints sz
  in empty
       { argConstraints =
           set (ixF idx) (Const constraints) (argConstraints empty)
       }

-- | Union
instance Semigroup (Constraints types) where
  cs1 <> cs2 = error "Unimplemented"  -- TODO(lb)
