{-
Module       : UCCrux.LLVM.Run.Simulate.Imprecision
Description  : Tracking sources of imprecision
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

See also "UCCrux.LLVM.Run.Simulate.Unsoundness".
-}
{-# LANGUAGE DeriveFunctor #-}

module UCCrux.LLVM.Run.Simulate.Imprecision
  ( Imprecision (..),
    Withimprecision (..),
    ppImprecision,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Set (Set)
import qualified Data.Set as Set

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName(getSkipOverrideName))
{- ORMOLU_ENABLE -}

-- | Track sources of imprecision
data Withimprecision a = WithImprecision
  { imprecision :: Imprecision,
    possiblyImpreciseValue :: a
  }
  deriving (Eq, Functor, Ord, Show)

-- | 'Imprecision' are over-approximations of the set of all possible runtime
-- behaviors of the program.
data Imprecision = Imprecision
  { impreciseSkipOverridesUsed :: Set SkipOverrideName
  }
  deriving (Eq, Ord, Show)

ppImprecision :: Imprecision -> Doc ann
ppImprecision u =
  PP.nest 2 $
    PP.vcat $
      ( PP.pretty
          "Execution of the following functions was skipped:" :
        bullets
          (map getSkipOverrideName (Set.toList (impreciseSkipOverridesUsed u)))
      )
  where
    bullets = map ((PP.pretty "-" PP.<+>) . PP.pretty)

instance Semigroup Imprecision where
  u1 <> u2 =
    Imprecision
      { impreciseSkipOverridesUsed =
          impreciseSkipOverridesUsed u1 <> impreciseSkipOverridesUsed u2
      }

instance Monoid Imprecision where
  mempty =
    Imprecision
      { impreciseSkipOverridesUsed = Set.empty
      }
