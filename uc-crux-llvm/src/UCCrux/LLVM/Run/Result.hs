{-
Module       : UCCrux.LLVM.Run.Result
Description  : The result
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
-- Needed for GHC 8.6
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Run.Result
  ( BugfindingResult (..),
    SomeBugfindingResult (..),
    SomeBugfindingResult' (..),
    FunctionSummary (..),
    FunctionSummaryTag (..),
    functionSummaryTag,
    ppFunctionSummaryTag,
    makeFunctionSummary,
    ppFunctionSummary,
    printFunctionSummary,
  )
where

{- ORMOLU_DISABLE -}
import           Data.List.NonEmpty (NonEmpty((:|)), toList)
import           Data.Sequence (Seq)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Context (Assignment)

import           UCCrux.LLVM.Classify.Types (Located(..), ppLocated, TruePositive, ppTruePositive, Diagnosis, Unclassified, ppUnclassified)
import           UCCrux.LLVM.Constraints (isEmpty, ppConstraints, Constraints(..))
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr)
import           UCCrux.LLVM.Run.Simulate (UCCruxSimulationResult)
import           UCCrux.LLVM.Run.Simulate.Uncertainty (Uncertainty(..))
import           UCCrux.LLVM.Run.Simulate.Imprecision (Imprecision, ppImprecision)
import           UCCrux.LLVM.Run.Simulate.Unsoundness (Unsoundness, ppUnsoundness)
{- ORMOLU_ENABLE -}

data FunctionSummaryTag
  = TagUnclear
  | TagLikelyBugs
  | TagSafeWithPreconditions
  | TagLikelySafe
  deriving (Bounded, Enum, Eq, Ord)

functionSummaryTag :: FunctionSummary m argTypes -> FunctionSummaryTag
functionSummaryTag =
  \case
    Unclear {} -> TagUnclear
    LikelyBugs {} -> TagLikelyBugs
    SafeWithPreconditions {} -> TagSafeWithPreconditions
    LikelySafe {} -> TagLikelySafe

ppFunctionSummaryTag :: FunctionSummaryTag -> Text
ppFunctionSummaryTag =
  \case
    TagUnclear -> "Unclear result, couldn't tell if errors are feasible"
    TagLikelyBugs -> "Found likely bugs"
    TagSafeWithPreconditions -> "Function is safe if deduced preconditions are met"
    TagLikelySafe -> "Function is always safe"

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
--
-- TODO: It would be great to have more provenance information for the
-- 'Constraints'. What bug does a given constraint help avoid? On what line?
data FunctionSummary m (argTypes :: Ctx (FullType m))
  = Unclear (NonEmpty (Located Unclassified))
  | LikelyBugs Imprecision (NonEmpty (Located TruePositive))
  | SafeWithPreconditions Unsoundness (Constraints m argTypes)
  | LikelySafe Unsoundness

-- | The result of running the bugfinding/contract inference main loop. Contains
-- both the final, summary result ('BugfindingResult'), as well as the sequence
-- of simulation results that led to it ('UCCruxSimulationResult'), which is
-- consumed in particular during crash-equivalence checking.
data SomeBugfindingResult m arch
  = forall argTypes.
    SomeBugfindingResult
      (Assignment (FullTypeRepr m) argTypes)
      (BugfindingResult m arch argTypes)
      (Seq (UCCruxSimulationResult m arch argTypes))

data SomeBugfindingResult'
  = forall m arch. SomeBugfindingResult' (SomeBugfindingResult m arch)

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data BugfindingResult m arch (argTypes :: Ctx (FullType m)) = BugfindingResult
  { uncertainResults :: [Located Uncertainty],
    deducedPreconditions :: [Diagnosis],
    summary :: FunctionSummary m argTypes
  }

ppFunctionSummary :: FunctionSummary m argTypes -> Doc Void
ppFunctionSummary fs =
  PP.pretty (ppFunctionSummaryTag (functionSummaryTag fs))
    <> case fs of
      Unclear unclass ->
        PP.pretty $
          ":\n"
            <> Text.intercalate
              "\n----------\n"
              (let ppU = PP.renderStrict . (PP.layoutPretty PP.defaultLayoutOptions) . ppUnclassified
               in toList (fmap (ppLocated ppU) unclass))
      LikelyBugs imprecision bugs ->
        PP.pretty
          (":\n" :: Text)
          <> PP.pretty
               (Text.intercalate
                 "\n----------\n"
                 (toList (fmap (ppLocated ppTruePositive) bugs)))
          <> ppImprecision' imprecision
      SafeWithPreconditions u preconditions ->
        PP.pretty
          (":\n" :: Text)
          <> ppConstraints preconditions
               <> ppUnsoundness' u
      LikelySafe u -> "." <> ppUnsoundness' u
  where
    ppUnsoundness' u =
      if mempty == u
        then mempty
        else
          PP.pretty
            ( Text.unwords
                [ "\nIn addition to any assumptions listed above, the",
                  "following sources of unsoundness may invalidate this",
                  "safety claim:\n"
                ]
            )
            <> ppUnsoundness u

    ppImprecision' i =
      if mempty == i
        then mempty
        else
          PP.pretty
            ( Text.unwords
                [ "\nIn addition to any assumptions listed above, the",
                  "following sources of imprecision may invalidate this",
                  "claim:\n"
                ]
            )
            <> ppImprecision i

printFunctionSummary :: FunctionSummary m argTypes -> Text
printFunctionSummary fs =
  PP.renderStrict (PP.layoutPretty PP.defaultLayoutOptions (ppFunctionSummary fs))

-- NOTE(lb): Unsoundness is only reported if a safety claim is being made, and
-- imprecision is only reported if an unsafety claim is being made.
makeFunctionSummary ::
  Constraints m argTypes ->
  [Located TruePositive] ->
  [Located Unclassified] ->
  Unsoundness ->
  Imprecision ->
  FunctionSummary m argTypes
makeFunctionSummary preconditions truePositives unclass unsoundness imprecision =
  case (isEmpty preconditions, truePositives, unclass) of
    (True, [], []) -> LikelySafe unsoundness
    (False, [], _) -> SafeWithPreconditions unsoundness preconditions
    (_, t : ts, _) -> LikelyBugs imprecision (t :| ts)
    (_, _, u : us) -> Unclear (u :| us)
