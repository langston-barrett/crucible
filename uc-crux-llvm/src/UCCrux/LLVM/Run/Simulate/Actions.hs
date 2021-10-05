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
    lmapIOPre,
    PostSimulation(..),
    liftIOPost,
    lmapIOPost,
    PrePost(..),
    ForAllSymInterface(..),
    ForAllSymInterface1(..),
    ForAllSymInterface2(..),
    SimActions(..),
    SomeSimActions(..),
    andThen,
    shim,
    shimIO,
    addDataIO,
    passViaIORef,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef)
import qualified Data.IORef as IORef
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

lmapIOPre ::
  (c -> IO b) ->
  PreSimulation p sym b a ->
  PreSimulation p sym c a
lmapIOPre f (PreSimulation g) = PreSimulation (\sym c -> g sym =<< liftIO (f c))

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
      pre :: PreSimulation p sym b a,
      -- | What to do after simulation ends
      post :: PostSimulation sym b a
    }
  deriving (Functor)

instance Profunctor (PrePost p sym) where
  lmap f (PrePost pr po) = PrePost (lmap f pr) (lmap f po)
  rmap f (PrePost pr po) = PrePost (rmap f pr) (rmap f po)

data SimActions argTypes p sym b =
  SimActions
    { -- | Setup arguments and memory
      makeArguments :: MakeArguments argTypes sym b,
      prePost :: PrePost p sym b ()
    }

-- TODO
-- executePre ::
--   SimActions a argTypes sym ->
--   sym ->
--   Crucible.OverrideSim
--     (p sym)
--     sym
--     LLVM
--     (Crucible.RegEntry sym CrucibleTypes.UnitType)
--     CrucibleTypes.EmptyCtx
--     CrucibleTypes.UnitType
--     ()
-- executePre = _

data SomeSimActions argTypes p sym =
  forall b. SomeSimActions (SimActions argTypes p sym b)

-- NOTE(lb): It's a wart that the below types need the sym ~ ExprBuilder
-- constraint, made necessary by the use of 'asApp' in UCCrux.LLVM.Classify.
-- We should look into whether the necessary functionality could be more
-- elegantly exposed from crucible-llvm+What4.

newtype ForAllSymInterface f =
  ForAllSymInterface
    { withSymInterface ::
        forall personality sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f (personality sym) sym
    }

newtype ForAllSymInterface1 f a =
  ForAllSymInterface1
    { withSymInterface1 ::
        forall personality sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f (personality sym) sym a
    }

newtype ForAllSymInterface2 f b a =
  ForAllSymInterface2
    { withSymInterface2 ::
        forall personality sym t s x.
        (sym ~ What4.ExprBuilder t s x) =>
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f (personality sym) sym b a
    }

andThen ::
  SimActions argTypes p sym b ->
  PrePost p sym b () ->
  SimActions argTypes p sym b
andThen actions (PrePost pre' post') =
  actions
    { prePost =
        let PrePost pre'' post'' = prePost actions
        in PrePost
             { pre = pre'' >> pre',
               post = post'' >> post'
             }
    }

shim ::
  (b -> c) ->
  (c -> b) ->
  SimActions argTypes p sym b ->
  SimActions argTypes p sym c
shim forwards backwards actions =
  actions
    { makeArguments = forwards <$> makeArguments actions,
      prePost = lmap backwards (prePost actions)
    }

shimIO ::
  (b -> IO c) ->
  (c -> IO b) ->
  SimActions argTypes p sym b ->
  SimActions argTypes p sym c
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
  SimActions argTypes p sym b ->
  SimActions argTypes p sym (b, c)
addDataIO f = shimIO (\b -> (b,) <$> f b) (return . fst)

-- | Create a fresh IORef in the 'MakeArguments', fill it in the
-- 'PreSimulation', and consume it in the 'PostSimulation'.
passViaIORef ::
  c ->
  MakeArguments argTypes sym b ->
  PreSimulation p sym b c ->
  (c -> PostSimulation sym b ()) ->
  SimActions argTypes p sym (b, IORef c)
passViaIORef c0 makeArgs (PreSimulation pr) po =
  SimActions
    { makeArguments =
        makeArgs `bindIO` \b -> (b,) <$> IORef.newIORef c0,
      prePost =
        PrePost { pre =
                    PreSimulation $
                      \sym (b, ref) ->
                        (liftIO . IORef.writeIORef ref) =<< pr sym b,
                  post =
                    PostSimulation $
                      \sym (b, ref) bb gl ->
                        do c <- liftIO (IORef.readIORef ref)
                           case po c of
                             PostSimulation f ->
                               f sym b bb gl
                }
    }
