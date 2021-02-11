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
  deriving Eq

data ValueConstraint
  = ValueConstraint
      { constraintBody :: Constraint
      , constraintCursor :: Cursor
      }
  deriving Eq

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint argTypes
  = SizeOfAllocation (Selector argTypes) (Selector argTypes)
  -- ^ The first argument (a bitvector) is equal to the size of the allocation
  -- pointed to by the second
  deriving Eq

data Constraints argTypes
  = Constraints
      { argConstraints :: Ctx.Assignment (Const [ValueConstraint]) argTypes
      , globalConstraints :: Map L.Symbol [ValueConstraint]
      , relationalConstraints :: [RelationalConstraint argTypes]
      }

emptyConstraints :: Ctx.Size argTypes -> Constraints argTypes
emptyConstraints sz =
  Constraints
    { argConstraints = Ctx.generate sz (\_index -> Const [])
    , globalConstraints = Map.empty
    , relationalConstraints = []
    }

isEmpty :: Constraints argTypes -> Bool
isEmpty (Constraints argCs globCs relCs) =
  and [ allFC ((== []) . getConst) argCs
      , globCs == Map.empty
      , relCs == []
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

ppConstraints :: Constraints argTypes -> Doc Void
ppConstraints (Constraints argCs _globCs _relCs) =
  let ppArgC idx (Const constraints) =
        PP.nest
          2
          (PP.vsep ( PP.pretty "Argument #" <> PP.viaShow (Ctx.indexVal idx)
                   -- TODO: Use argument names
                   : map ppValueConstraint constraints
                   ))
      -- ppGlobC symb constraint = PP.pretty "Constraint on global " <> _
  -- TODO: print globCs, relCs
  in PP.vsep $ toListWithIndex ppArgC argCs
  where
    toListWithIndex :: (forall tp. Ctx.Index ctx tp -> f tp -> a)
                    -> Ctx.Assignment f ctx
                    -> [a]
    toListWithIndex f assign =
      toListFC getConst $
        Ctx.generate (Ctx.size assign) (\idx -> Const (f idx (assign Ctx.! idx)))


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
