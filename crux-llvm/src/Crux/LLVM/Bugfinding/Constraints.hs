{-
Module       : Crux.LLVM.Bugfinding.Constraints
Description  : Descriptions of function preconditions.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module Crux.LLVM.Bugfinding.Constraints
  ( Selector(..)
  , ValueConstraint(..)
  , Constraint(..)
  , subsumes
  , conflict
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
  | SelectGlobal L.Symbol Cursor

-- | A (possibly) \"relational\" constraint across several values.
data Constraint
  = ConstraintOnValue ConstraintBody Selector
  | SizeOfAllocation Selector Selector
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second

-- | Does the first precondition make the second one redundant?
subsumes :: Constraint -> Constraint -> Bool
subsumes _ _ = False

-- | Are these preconditions mutually exclusive?
conflict :: Constraint -> Constraint -> Bool
conflict _ _ = False

mapToContext ::
  Monoid a =>
  Ctx.Assignment f items ->
  Map Int a ->
  Ctx.Assignment (Const a) items
mapToContext assign mp =
  Ctx.generate
    (Ctx.size assign)
    (\index -> Const (Map.findWithDefault mempty (Ctx.indexVal index) mp))

-- | Turn a relational constraint into value constraints
compileOne ::
  Constraint ->
  CrucibleTypes.CtxRepr types  {-^ Argument Crucible types -} ->
  (Map L.Symbol [ValueConstraint], Map Int [ValueConstraint])
compileOne constraint argTypes =
  case constraint of
    ConstraintOnValue body selector -> _
    SizeOfAllocation selector selector -> _

-- | Turn relational constraints into value constraints
compile ::
  [Constraint] ->
  CrucibleTypes.CtxRepr types  {-^ Argument Crucible types -} ->
  (Map L.Symbol [ValueConstraint], Ctx.Assignment (Const [ValueConstraint]) types)
compile constraints argTypes =
  foldr _ (Map.empty, _) constraints
