{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Bugfinding (tests) where

import           Control.Exception (SomeException, try, displayException)
import qualified Data.Text as Text
import           System.FilePath ((</>))
import           System.IO (IOMode(WriteMode), withFile)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           Data.Parameterized.NatRepr (NatRepr, knownNat)
import qualified Data.Parameterized.Context as Ctx

import qualified Crux
import           CruxLLVMMain (processLLVMOptions)
import           Crux.LLVM.Compile (genBitCode)
import           Crux.LLVM.Config (LLVMOptions(entryPoint), llvmCruxConfig)

-- Code being tested
import           Crux.LLVM.Bugfinding (translateAndLoop)
import qualified Crux.LLVM.Bugfinding.Result as Result
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (assertUnimplemented)
import           Crux.LLVM.Bugfinding.Cursor (Cursor(..))
import           Crux.LLVM.Bugfinding.Classify (partitionUncertainty)
import           Crux.LLVM.Bugfinding.FullType (FullType(..), FullTypeRepr(..))


-- Just test that a few things typecheck as expected

exampleHere :: Cursor m ('FTInt 64) ('FTInt 64)
exampleHere = Here (FTIntRepr knownNat)

_exampleArray :: Cursor m ('FTArray 8 ('FTInt 64)) ('FTInt 64)
_exampleArray = Index (knownNat :: NatRepr 7) knownNat exampleHere

_exampleStruct ::
  Cursor m
    ('FTStruct ('Ctx.EmptyCtx Ctx.::> 'FTInt 32 Ctx.::> 'FTInt 64))
    ('FTInt 64)
_exampleStruct =
  Field
    (Ctx.extend (Ctx.extend Ctx.empty (FTIntRepr knownNat)) (FTIntRepr knownNat))
    (Ctx.lastIndex Ctx.knownSize)
    exampleHere

testDir :: FilePath
testDir = "tests/bugfinding"

findBugs :: FilePath -> String -> IO Result.SomeBugfindingResult
findBugs file fn =
  do withFile (testDir </> file <> ".output") WriteMode $ \h ->
       do let outCfg = Crux.OutputConfig False h h True
          (cruxOpts, llvmOpts) <-
            Crux.loadOptions outCfg "crux-llvm" "0.1" llvmCruxConfig $ \(initCrux, initLlvm) ->
              do (cruxOpts, llvmOpts) <-
                   processLLVMOptions ( initCrux { Crux.inputFiles = [testDir </> file]
                                                 , Crux.loopBound = Just 8
                                                 , Crux.recursionBound = Just 8
                                                 }
                                      , initLlvm { entryPoint = fn }
                                      )


                 try (genBitCode cruxOpts llvmOpts) >>=
                   \case
                     Left (exc :: SomeException) ->
                       putStrLn ("Trouble when running Clang:" ++ displayException exc)
                     Right () -> pure ()

                 pure (cruxOpts, llvmOpts)
          putStrLn (unwords [ "Reproduce with:\n"
                            , "cabal v2-run exe:crux-llvm -- "
                            , "--bugfinding"
                            , "--entry-point"
                            , fn
                            , testDir </> file
                            ])
          let ?outputConfig = outCfg
          translateAndLoop cruxOpts llvmOpts

hasBugs :: FilePath -> String -> TT.TestTree
hasBugs file fn =
  TH.testCase (fn <> " has bugs") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       [] TH.@=? map show missingAnn
       [] TH.@=? map show failedAssert
       case Result.summary result of
         Result.FoundBugs bugs -> pure ()
         _ -> TH.assertFailure (unwords ["Expected", fn, "to have bugs"])

isSafe :: FilePath -> String -> TT.TestTree
isSafe file fn =
  TH.testCase (fn <> " is safe") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       [] TH.@=? map show missingAnn
       [] TH.@=? map show failedAssert
       case Result.summary result of
         Result.AlwaysSafe -> pure ()
         _ -> TH.assertFailure
                (unwords ["Expected", fn, "to be safe but the result was"
                         , Text.unpack (Result.printFunctionSummary (Result.summary result))
                         ])

isSafeToBounds :: FilePath -> String -> TT.TestTree
isSafeToBounds file fn =
  TH.testCase (fn <> " is safe") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       [] TH.@=? map show missingAnn
       [] TH.@=? map show failedAssert
       case Result.summary result of
         Result.SafeUpToBounds -> pure ()
         _ -> TH.assertFailure
                (unwords ["Expected", fn, "to be safe up to recursion/loop bounds"
                         , "but the result was"
                         , Text.unpack (Result.printFunctionSummary (Result.summary result))
                         ])

isSafeWithPreconditions :: FilePath -> String -> Bool -> TT.TestTree
isSafeWithPreconditions file fn resourceExhausted =
  TH.testCase (fn <> " is safe") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       [] TH.@=? map show missingAnn
       [] TH.@=? map show failedAssert
       case Result.summary result of
         Result.SafeWithPreconditions didExhaust _preconditions ->
           resourceExhausted TH.@=? didExhaust
         _ -> TH.assertFailure
                (unwords ["Expected", fn, "to be safe with preconditions"
                         , "but the result was"
                         , Text.unpack (Result.printFunctionSummary (Result.summary result))
                         ])

isUnannotated :: FilePath -> String -> TT.TestTree
isUnannotated file fn =
  TH.testCase (fn <> " is unannotated") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       [] TH.@=? map show failedAssert
       0 < length missingAnn TH.@?
           (unwords ["Expected", fn, "to be unannotated"
                    , "but the result was"
                    , Text.unpack (Result.printFunctionSummary (Result.summary result))
                    ])

hasFailedAssert :: FilePath -> String -> TT.TestTree
hasFailedAssert file fn =
  TH.testCase (fn <> " has a symbolically failing assert") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show unclass
       0 < length failedAssert TH.@?
           (unwords ["Expected", fn, "to have failing assertions"
                    , "but the result was"
                    , Text.unpack (Result.printFunctionSummary (Result.summary result))
                    ])

isUnclassified :: FilePath -> String -> TT.TestTree
isUnclassified file fn =
  TH.testCase (fn <> " is unclassified") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show missingAnn
       [] TH.@=? map show failedAssert
       0 < length unclass TH.@?
           (unwords ["Expected", fn, "to be unclassified"
                    , "but the result was"
                    , Text.unpack (Result.printFunctionSummary (Result.summary result))
                    ])

hasMissingAnn :: FilePath -> String -> TT.TestTree
hasMissingAnn file fn =
  TH.testCase (fn <> " has a mssing annotation") $
    do Result.SomeBugfindingResult result <- findBugs file fn
       let (unclass, missingAnn, failedAssert) =
             partitionUncertainty (Result.uncertainResults result)
       [] TH.@=? map show failedAssert
       [] TH.@=? map show unclass
       0 < length missingAnn TH.@?
           (unwords ["Expected", fn, "to have a missing annotation"
                    , "but the result was"
                    , Text.unpack (Result.printFunctionSummary (Result.summary result))
                    ])

isUnimplemented :: FilePath -> String -> TT.TestTree
isUnimplemented file fn =
  TH.testCase (fn <> " exercises unimplemented functionality") $
    assertUnimplemented (findBugs file fn) >>=
      \case
        Left msg ->
          TH.assertFailure
            (unwords ["Expected", fn, "to be unimplemented"
                     , "but the result was"
                     , msg
                     ])
        Right _ -> pure ()

tests :: TT.TestTree
tests =
  TT.testGroup "bugfinding"
    [ hasBugs "assert_false.c" "assert_false"
    , hasBugs "assert_arg_eq.c" "assert_arg_eq" -- goal: hasFailedAssert
    , isSafe "add1.c" "add1"
    , isSafe "branch.c" "branch"
    , isSafe "compare_to_null.c" "compare_to_null"
    , isSafe "print.c" "print"
    , isSafe "read_global.c" "read_global"
    , isSafe "write_global.c" "write_global"
    , isSafeToBounds "factorial.c" "factorial"
    , isSafeToBounds "loop_arg_bound.c" "loop_arg_bound"
    , isSafeToBounds "loop_constant_big_bound_arg_start.c" "loop_constant_big_bound_arg_start"
    , isSafeToBounds "loop_constant_bound_arg_start.c" "loop_constant_bound_arg_start" -- TODO: Why not just isSafe?
    , isSafeWithPreconditions "deref_arg.c" "deref_arg" False
    , isSafeWithPreconditions "deref_struct_field.c" "deref_struct_field" False
    , isSafeWithPreconditions "writes_to_arg.c" "writes_to_arg" False
    , isSafeWithPreconditions "writes_to_arg_conditional.c" "writes_to_arg_conditional" False
    , isSafeWithPreconditions "writes_to_arg_conditional_ptr.c" "writes_to_arg_conditional_ptr" False
    , isSafeWithPreconditions "writes_to_arg_field.c" "writes_to_arg_field" False
    , isSafeWithPreconditions "writes_to_arg_ptr.c" "writes_to_arg_ptr" False
    , isUnclassified "do_exit.c" "do_exit"  -- goal: isSafe
    , isUnclassified "do_fork.c" "do_fork"
    , isUnclassified "do_getchar.c" "do_getchar"  -- goal: isSafe
    , isUnclassified "do_recv.c" "do_recv"
    , isUnclassified "linked_list_sum.c" "linked_list_sum" -- goal: isSafeWP(True)
    , isUnclassified "mutually_recursive_linked_list_sum.c" "mutually_recursive_linked_list_sum" -- goal: isSafeWP(True)
    , isUnclassified "oob_read_heap.c" "oob_read_heap"  -- goal: notSafe
    , isUnclassified "oob_read_stack.c" "oob_read_stack"  -- goal: notSafe
    , isUnclassified "ptr_as_array.c" "ptr_as_array"  -- goal: isSafe
    , isUnclassified "sized_array_arg.c" "sized_array_arg"  -- goal: isSafe
    , isUnclassified "uninitialized_stack.c" "uninitialized_stack"  -- goal: notSafe
    , isUnimplemented "add1_double.c" "add1_double"  -- goal: ???
    , isUnimplemented "add1_float.c" "add1_float"  -- goal: ???
    , isUnimplemented "call_function_pointer.c" "call_function_pointer"  -- goal: ???
    , isUnimplemented "nested_structs.c" "nested_structs"

    -- TODO: Fix upstream?
    -- "error: in do_memcpy_const_size\nError during memory load"
    , isUnannotated "do_memcpy_const_size.c" "do_memcpy_const_size"  -- goal: isSafeWP

    -- TODO: https://github.com/GaloisInc/crucible/issues/651
    -- , isSafeWithPreconditions "do_strlen.c" "do_strlen" False


    -- TODO: Panics on redundant constraints
    -- , isUnclassified "do_memcpy.c" "do_memcpy"  -- goal: isSafeWP
    -- , isUnclassified "do_memset.c" "do_memset"  -- goal: isSafeWP

    -- TODO: Not sure if Crux can do C++?
    -- , isSafe "cxxbasic.cpp" "cxxbasic"
    ]
