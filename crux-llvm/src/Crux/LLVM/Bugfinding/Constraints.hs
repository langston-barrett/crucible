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
  ( Selector(..)
  , ValueConstraint(..)
  , Constraints(..)
  , emptyConstraints
  ) where

import           Data.Functor.Const
import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Types as CrucibleTypes

import           Crux.LLVM.Bugfinding.Cursor

-- | A constraint on a single value
data ConstraintBody
  = NotNull
  -- ^ This pointer is not null
  | SizeAtLeast !Int
  -- ^ The allocation backing this pointer has at least this size

data ValueConstraint
  = ValueConstraint
      { constraintBody :: ConstraintBody
      , constraintCursor :: Cursor
      }

data Selector
  = SelectArgument !Int Cursor
  | SelectGlobal !L.Symbol Cursor

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint
  = SizeOfAllocation Selector Selector
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second

data Constraints types
  = Constraints
      { argConstraints :: Ctx.Assignment (Const [ValueConstraint]) types
      , globalConstraints :: Map L.Symbol ValueConstraint
      , relationalConstraints :: [RelationalConstraint]
      }

emptyConstraints :: Ctx.Size types -> Constraints types
emptyConstraints sz =
  Constraints
    { argConstraints = Ctx.generate sz (\index -> Const [])
    , globalConstraints = Map.empty
    , relationalConstraints = []
    }

-- | Union
instance Semigroup (Constraints types) where
  cs1 <> cs2 = error "Unimplemented"
