{-
Module       : UCCrux.LLVM.Run.Simulate.Actions
Description  : Actions to perform before or after simulation
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

This interface is complex, but is intended to allow API consumers to do things
like set up different overrides for different runs of the symbolic simulator,
and to pass data between the steps that set up simulation and the steps that
analyze the outcome of simulation.
-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Run.Simulate.Actions
  ( MakeArguments(..),
    bindIO,
    PreSimulation(..),
    liftPre,
    lmapIOPre,
    PostSimulation(..),
    lmapIOPost,
    PrePost(..),
    ForAllSymInterface(..),
    ForAllSymInterface1(..),
    ForAllSymInterface2(..),
    SimActions(..),
    SomeSimActions(..),
    mapSomeSimActions,
    andThen,
    andThen_,
    shim,
    shimIO,
    addDataIO,
    andThenWithIORef,
    andThenWithIORefs,
    addPost,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Monad.IO.Class (MonadIO(liftIO))
import           Control.Monad.Reader (MonadReader(ask, local))
import           Data.IORef (IORef)
import qualified Data.IORef as IORef
import           Data.Profunctor (Profunctor(lmap, rmap))

import qualified What4.Expr.Builder as What4
import qualified What4.LabeledPred as What4
import qualified What4.Interface as What4
import           What4.InterpretedFloatingPoint (IsInterpretedFloatExprBuilder)

import           Lang.Crucible.Backend (IsSymInterface, IsBoolSolver)
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

-- | Set up the arguments and memory state for execution. Additionally, create
-- any data or references that need to be shared between subsequent steps (type
-- parameter @b@).
newtype MakeArguments argTypes sym b
  = MakeArguments
      { runMakeArguments ::
          sym ->
          IO ( RegMap sym argTypes
             , MemImpl sym
             , b
             )
      }
  deriving (Functor)

bindIO ::
  MakeArguments argTypes sym b ->
  (b -> IO c) ->
  MakeArguments argTypes sym c
bindIO (MakeArguments f) g =
  MakeArguments (\sym -> f sym >>= \(r, m, b) -> (r, m,) <$> g b)

-- | Perform actions such as registering overrides or modifying memory just
-- before executing the CFG.
--
-- Has access to data from @MakeArguments@ (type parameter @b@).
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

lmapIOPre ::
  (c -> IO b) ->
  PreSimulation p sym b a ->
  PreSimulation p sym c a
lmapIOPre f (PreSimulation g) = PreSimulation (\sym c -> g sym =<< liftIO (f c))

-- | Perform actions in Crux's \"error continuation\".
--
-- Has access to data from @MakeArguments@ (type parameter @b@).
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

instance MonadIO (PostSimulation sym b) where
  liftIO comp = PostSimulation (\_ _ _ _ -> comp)

instance MonadReader b (PostSimulation sym b) where
  ask = PostSimulation $ \_sym b _bb _gl -> return b
  local fb (PostSimulation comp) =
    PostSimulation $ \sym b bb gl -> comp sym (fb b) bb gl

lmapIOPost ::
  (c -> IO b) ->
  PostSimulation sym b a ->
  PostSimulation sym c a
lmapIOPost f (PostSimulation g) =
  PostSimulation (\sym c bb gl ->
                    do b <- liftIO (f c)
                       g sym b bb gl)

data PrePost p sym b a =
  PrePost
    { -- | Additional setup actions (e.g. registering overrides)
      pre :: PreSimulation p sym b (),
      -- | What to do after simulation ends
      post :: PostSimulation sym b a
    }
  deriving (Functor)

instance Profunctor (PrePost p sym) where
  lmap f (PrePost pr po) = PrePost (lmap f pr) (lmap f po)
  rmap f (PrePost pr po) = PrePost pr (rmap f po)

-- | Actions to execute to set up symbolic execution and interpret any errors.
--
-- See comments on 'MakeArguments', 'PreSimulation', and 'PostSimulation'.
data SimActions argTypes p sym b a =
  SimActions
    { makeArguments :: MakeArguments argTypes sym b,
      prePost :: PrePost p sym b a
    }
  deriving (Functor)

-- | Somewhat awkward ordering of type variables to work with
-- 'ForAllSymInterface'.
data SomeSimActions argTypes a p sym =
  forall b. SomeSimActions (SimActions argTypes p sym b a)

mapSomeSimActions ::
  (forall b. SimActions argTypes p sym b a -> SimActions argTypes p sym b c) ->
  SomeSimActions argTypes a p sym ->
  SomeSimActions argTypes c p sym
mapSomeSimActions f (SomeSimActions actions) =
  SomeSimActions (f actions)

-- NOTE(lb): It's a wart that the below types need the sym ~ ExprBuilder
-- constraint, made necessary by the use of 'asApp' in UCCrux.LLVM.Classify.
-- We should look into whether the necessary functionality could be more
-- elegantly exposed from crucible-llvm+What4.

newtype ForAllSymInterface f =
  ForAllSymInterface
    { withSymInterface ::
        forall personality sym t s x.
        IsBoolSolver sym =>
        IsInterpretedFloatExprBuilder sym =>
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f (personality sym) sym
    }

newtype ForAllSymInterface1 f a =
  ForAllSymInterface1
    { withSymInterface1 ::
        forall personality sym t s x.
        IsBoolSolver sym =>
        IsInterpretedFloatExprBuilder sym =>
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f (personality sym) sym a
    }

-- | The essence of the 'SimActions' API: combine multiple actions to be
-- executed before and after symbolic execution.
andThen ::
  (a -> c -> d) ->
  SimActions argTypes p sym b a ->
  PrePost p sym b c ->
  SimActions argTypes p sym b d
andThen f actions (PrePost pre' post') =
  actions
    { prePost =
        let PrePost pre'' post'' = prePost actions
        in PrePost
             { pre = pre'' >> pre',
               post = f <$> post'' <*> post'

             }
    }

andThen_ ::
  SimActions argTypes p sym b a ->
  PrePost p sym b () ->
  SimActions argTypes p sym b a
andThen_ = andThen const

-- | Pipe-fitting.
shim ::
  (b -> c) ->
  (c -> b) ->
  SimActions argTypes p sym b a ->
  SimActions argTypes p sym c a
shim forwards backwards actions =
  actions
    { makeArguments = forwards <$> makeArguments actions,
      prePost = lmap backwards (prePost actions)
    }

shimIO ::
  (b -> IO c) ->
  (c -> IO b) ->
  SimActions argTypes p sym b a ->
  SimActions argTypes p sym c a
shimIO forwards backwards actions =
  actions
    { makeArguments =
        makeArguments actions `bindIO` forwards,
      prePost = PrePost { pre = lmapIOPre backwards (pre (prePost actions)),
                          post = lmapIOPost backwards (post (prePost actions))
                        }
    }

addDataIO ::
  (b -> IO c) ->
  SimActions argTypes p sym b a ->
  SimActions argTypes p sym (b, c) a
addDataIO f = shimIO (\b -> (b,) <$> f b) (return . fst)

-- | Add an 'IORef'.
andThenWithIORef ::
  d ->
  SimActions argTypes p sym b a ->
  PrePost p sym (IORef d) c ->
  SimActions argTypes p sym (b, IORef d) (a, c)
andThenWithIORef d actions prPo =
  andThen
    (,)
    (addDataIO (const (IORef.newIORef d)) actions)
    (lmap snd prPo)

-- | Add two 'IORef'.
andThenWithIORefs ::
  d ->
  e ->
  SimActions argTypes p sym b a ->
  PrePost p sym (IORef d, IORef e) c ->
  SimActions argTypes p sym (b, (IORef d, IORef e)) (a, c)
andThenWithIORefs d e actions prPo =
  andThen
    (,)
    (addDataIO (const ((,) <$> IORef.newIORef d <*> IORef.newIORef e)) actions)
    (lmap snd prPo)

-- | Tack on another task to execute when interpreting errors.
addPost ::
  (a -> c -> d) ->
  SimActions argTypes p sym b a ->
  PostSimulation sym b c ->
  SimActions argTypes p sym b d
addPost f actions po =
  andThen f actions (PrePost { pre = return (), post = po })
