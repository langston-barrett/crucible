{-
Module       : UCCrux.LLVM.Run.Simulate.Actions
Description  : Actions to perform before or after simulation
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Run.Simulate.Actions
  ( MakeArguments(..),
    bindIO,
    PreSimulation(..),
    liftPre,
    PostSimulation(..),
    liftIOPost,
    PrePost(..),
    ForAllSymInterface(..),
    ForAllSymInterface1(..),
    ForAllSymInterface2(..),
    SimActions(..),
    SomeSimActions(..),
    andThen,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Data.Profunctor (Profunctor(lmap, rmap))

import qualified What4.Expr.Builder as What4
import qualified What4.LabeledPred as What4
import qualified What4.Interface as What4

import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible
import           Lang.Crucible.Simulator.RegMap (RegMap)
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.MemModel (MemImpl, HasLLVMAnn, LLVMAnnMap, MemOptions)
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.Intrinsics (IntrinsicsOptions)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
{- ORMOLU_ENABLE -}


newtype MakeArguments argTypes sym a
  = MakeArguments
      { runMakeArguments ::
          sym ->
          IO ( RegMap sym argTypes
             , MemImpl sym
             , a
             )
      }
  deriving (Functor)

bindIO ::
  MakeArguments argTypes sym a ->
  (a -> IO b) ->
  MakeArguments argTypes sym b
bindIO (MakeArguments f) g =
  MakeArguments (\sym -> f sym >>= \(r, m, a) -> (r, m,) <$> g a)

-- TODO profunctor
newtype PreSimulation p sym b a
  = PreSimulation
      { runPreSimulation ::
          (?lc :: TypeContext) =>
          (?intrinsicsOpts :: IntrinsicsOptions) =>
          (?memOpts :: MemOptions) =>
          sym ->
          b ->
          Crucible.OverrideSim
            p
            sym
            LLVM
            (Crucible.RegEntry sym CrucibleTypes.UnitType)
            CrucibleTypes.EmptyCtx
            CrucibleTypes.UnitType
            a
      }
  deriving (Functor)

liftPre ::
  Crucible.OverrideSim
    p
    sym
    LLVM
    (Crucible.RegEntry sym CrucibleTypes.UnitType)
    CrucibleTypes.EmptyCtx
    CrucibleTypes.UnitType
    a ->
  PreSimulation p sym b a
liftPre comp = PreSimulation (\_ _ -> comp)

-- | Combination of the reader and 'Crucible.OverrideSim' applicatives
instance Applicative (PreSimulation p sym b) where
  pure a = PreSimulation (\_ _ -> return a)
  (PreSimulation f) <*> (PreSimulation g) =
    PreSimulation (\sym b -> f sym b <*> g sym b)

-- | Combination of the reader and 'Crucible.OverrideSim' monads
instance Monad (PreSimulation p sym b) where
  (PreSimulation g) >>= f =
    PreSimulation (\sym b ->
                     do x <- g sym b
                        let PreSimulation h = f x
                        h sym b)

instance Profunctor (PreSimulation p sym) where
  lmap f (PreSimulation g) = PreSimulation (\sym a -> g sym (f a))
  rmap = fmap

-- TODO profunctor
newtype PostSimulation sym b a
  = PostSimulation
      { runPostSimulation ::
          sym ->
          b ->
          LLVMAnnMap sym ->
          What4.LabeledPred (What4.Pred sym) Crucible.SimError ->
          IO a
      }
  deriving (Functor)

instance Profunctor (PostSimulation sym) where
  lmap f (PostSimulation g) = PostSimulation (\sym a -> g sym (f a))
  rmap = fmap

-- | Combination of the reader and IO applicatives
instance Applicative (PostSimulation sym b) where
  pure a = PostSimulation (\_ _ _ _ -> return a)
  (PostSimulation f) <*> (PostSimulation g) =
    PostSimulation (\sym b ann p -> f sym b ann p <*> g sym b ann p)

-- | Combination of the reader and IO monads
instance Monad (PostSimulation sym b) where
  (PostSimulation g) >>= f =
    PostSimulation (\sym b ann p ->
                     do x <- g sym b ann p
                        let PostSimulation h = f x
                        h sym b ann p)

liftIOPost :: IO a -> PostSimulation sym b a
liftIOPost comp = PostSimulation (\_ _ _ _ -> comp)

data PrePost sym b a =
  PrePost
    { -- | Additional setup actions (e.g. registering overrides)
      pre :: forall personality. PreSimulation (personality sym) sym b a,
      -- | What to do after simulation ends
      post :: PostSimulation sym b a
    }
  deriving (Functor)

data SimActions argTypes sym b =
  SimActions
    { -- | Setup arguments and memory
      makeArguments :: MakeArguments argTypes sym b,
      prePost :: PrePost sym b ()
    }

-- TODO
-- executePre ::
--   SimActions a argTypes sym ->
--   sym ->
--   Crucible.OverrideSim
--     (personality sym)
--     sym
--     LLVM
--     (Crucible.RegEntry sym CrucibleTypes.UnitType)
--     CrucibleTypes.EmptyCtx
--     CrucibleTypes.UnitType
--     ()
-- executePre = _

data SomeSimActions argTypes sym =
  forall b. SomeSimActions (SimActions argTypes sym b)

newtype ForAllSymInterface f =
  ForAllSymInterface
    { withSymInterface ::
        forall sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f sym
    }

newtype ForAllSymInterface1 f a =
  ForAllSymInterface1
    { withSymInterface1 ::
        forall sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f sym a
    }

newtype ForAllSymInterface2 f b a =
  ForAllSymInterface2
    { withSymInterface2 ::
        forall sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f sym b a
    }

andThen ::
  ForAllSymInterface1 (SimActions argTypes) b ->
  ForAllSymInterface2 PrePost b () ->
  ForAllSymInterface1 (SimActions argTypes) b
andThen as pp =
  ForAllSymInterface1 $
    case (as, pp) of
      (ForAllSymInterface1 actions, ForAllSymInterface2 (PrePost pre' post')) ->
        actions
          { prePost =
              let PrePost pre'' post'' = prePost actions
              in PrePost
                   { pre = pre'' >> pre',
                     post = post'' >> post'
                   }
          }
