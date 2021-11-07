{-
Module       : UCCrux.LLVM.Run.Simulate.Uncertainty
Description  : Sources of uncertainty that occur during simulation
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module UCCrux.LLVM.Run.Simulate.Uncertainty
  ( Uncertainty(..),
    partitionUncertainty,
    ppUncertainty,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Exception (displayException)

import           Data.Text (Text)
import qualified Data.Text as Text

import           Panic (Panic)

import           Lang.Crucible.Simulator (SimError)

import           UCCrux.LLVM.Classify.Types (Located(Located))
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented)
{- ORMOLU_ENABLE -}

-- | Sources of uncertainty that occur during simulation
--
-- In the ideal world, this would just have the timeout and bounds constructors.
data Uncertainty
  = -- | Simulation, input generation, or classification encountered
    -- unimplemented functionality
    UUnimplemented (Panic Unimplemented)
  | -- | This @Pred@ was not annotated. These should likely should be fixed in
    -- Crucible-LLVM.
    UMissingAnnotation SimError
  | -- | Simulation timed out
    UTimeout !Text
  | -- | Hit loops/recursion bounds
    UExhaustedBounds !Text
  deriving (Show)

partitionUncertainty ::
  [Located Uncertainty] -> ([Located SimError], [Located ()], [Located (Panic Unimplemented)], [Located Text], [Located Text])
partitionUncertainty = go [] [] [] [] []
  where
    go ms fs ns ts ex =
      \case
        [] -> (ms, fs, ns, ts, ex)
        (Located loc (UMissingAnnotation err) : rest) ->
          let (ms', fs', ns', ts', ex') = go ms fs ns ts ex rest
           in (Located loc err : ms', fs', ns', ts', ex')
        (Located loc (UUnimplemented unin) : rest) ->
          let (ms', fs', ns', ts', ex') = go ms fs ns ts ex rest
           in (ms', fs', Located loc unin : ns', ts', ex')
        (Located loc (UTimeout fun) : rest) ->
          let (ms', fs', ns', ts', ex') = go ms fs ns ts ex rest
           in (ms', fs', ns', Located loc fun : ts', ex')
        (Located loc (UExhaustedBounds msg) : rest) ->
          let (ms', fs', ns', ts', ex') = go ms fs ns ts ex rest
           in (ms', fs', ns', ts', Located loc msg : ex')

ppUncertainty :: Uncertainty -> Text
ppUncertainty =
  \case
    UMissingAnnotation err ->
      "(Internal issue) Missing annotation for error:\n" <> Text.pack (show err)
    UUnimplemented pan -> Text.pack (displayException pan)
    UTimeout fun -> Text.pack "Simulation timed out while executing " <> fun
    UExhaustedBounds msg ->
      Text.pack "Hit bounds on loops/recursion: " <> msg
