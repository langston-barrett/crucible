{-
Module       : Crux.LLVM.Bugfinding.Result
Description  : The result
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Crux.LLVM.Bugfinding.Result
  ( BugfindingResult(..)
  , SomeBugfindingResult(..)
  , FunctionSummary(..)
  , makeFunctionSummary
  , printFunctionSummary
  ) where

import           Data.List.NonEmpty (NonEmpty((:|)), toList)
import           Data.Text (Text)
import qualified Data.Text as Text

import Crux.LLVM.Bugfinding.Classify (TruePositive, ppTruePositive, Uncertainty, ppUncertainty)
import Crux.LLVM.Bugfinding.Constraints (isEmpty, ppConstraints, Constraints(..))

data FunctionSummary m arch argTypes
  = Unclear (NonEmpty Uncertainty)
  | FoundBugs (NonEmpty TruePositive)
  | SafeWithPreconditions Bool (Constraints m arch argTypes)
  | SafeUpToBounds
  | AlwaysSafe

data SomeBugfindingResult =
  forall m arch argTypes. SomeBugfindingResult (BugfindingResult m arch argTypes)

data BugfindingResult m arch argTypes
  = BugfindingResult
      { uncertainResults :: [Uncertainty]
      , summary :: FunctionSummary m arch argTypes
      }

printFunctionSummary :: FunctionSummary m arch argTypes -> Text
printFunctionSummary =
  \case
    Unclear uncertainties ->
      "Unclear result, either false or true positives:\n"
      <> Text.intercalate "----------\n" (toList (fmap ppUncertainty uncertainties))
    FoundBugs bugs ->
      "There might be bugs in this function:\n"
      <> Text.intercalate "----------\n" (toList (fmap ppTruePositive bugs))
    SafeWithPreconditions b preconditions ->
      "This function is safe assuming the following preconditions are met:\n"
      <> if b then "The loop/recursion bound is not exceeded, and:\n" else ""
      <> Text.pack (show (ppConstraints preconditions))
    AlwaysSafe -> "This function is always safe."
    SafeUpToBounds -> "This function is safe up to the specified bounds on loops/recursion."

makeFunctionSummary ::
  Constraints m arch argTypes ->
  [Uncertainty] ->
  [TruePositive] ->
  Bool {-^ Did we hit the bounds? -} ->
  FunctionSummary m arch argTypes
makeFunctionSummary preconditions uncertainties truePositives bounds =
  case (isEmpty preconditions, uncertainties, truePositives, bounds) of
    (True, [], [], False) -> AlwaysSafe
    (True, [], [], True) -> SafeUpToBounds
    (False, [], [], b) -> SafeWithPreconditions b preconditions
    (_, [], t:ts, _) -> FoundBugs (t :| ts)
    (_, u:us, _, _) -> Unclear (u :| us)
