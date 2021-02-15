{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Bugfinding (tests) where

import           Control.Exception (SomeException, try, displayException)
import qualified Data.Text as Text
import           System.FilePath ((</>))
import           System.IO (IOMode(WriteMode), withFile)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import qualified Crux
import           CruxLLVMMain (processLLVMOptions)
import           Crux.LLVM.Compile (genBitCode)
import           Crux.LLVM.Config (LLVMOptions(entryPoint), llvmCruxConfig)

-- Code being tested
import           Crux.LLVM.Bugfinding
  (SomeBugfindingResult(..), BugfindingResult(..), FunctionSummary(..), translateAndLoop, printFunctionSummary)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (assertUnimplemented)

testDir :: FilePath
testDir = "tests/bugfinding"

findBugs :: FilePath -> String -> IO (SomeBugfindingResult)
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

isSafe :: FilePath -> String -> TT.TestTree
isSafe file fn =
  TH.testCase (fn <> " is safe") $
    do SomeBugfindingResult result <- findBugs file fn
       0 TH.@=? length (unclassifiedErrors result)
       case summary result of
         AlwaysSafe -> pure ()
         _ -> TH.assertFailure (unwords ["Expected", fn, "to be safe"])

isSafeWithPreconditions :: FilePath -> String -> TT.TestTree
isSafeWithPreconditions file fn =
  TH.testCase (fn <> " is safe") $
    do SomeBugfindingResult result <- findBugs file fn
       0 TH.@=? length (unclassifiedErrors result)
       case summary result of
         SafeWithPreconditions _preconditions -> pure ()
         _ -> TH.assertFailure
                (unwords ["Expected", fn, "to be safe with preconditions"
                         , "but the result was"
                         , Text.unpack (printFunctionSummary (summary result))
                         ])

isUnclassified :: FilePath -> String -> TT.TestTree
isUnclassified file fn =
  TH.testCase (fn <> " is unclassified") $
    do SomeBugfindingResult result <- findBugs file fn
       0 < length (unclassifiedErrors result) TH.@?
           (unwords ["Expected", fn, "to be unclassified"
                    , "but the result was"
                    , Text.unpack (printFunctionSummary (summary result))
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
    [ isSafe "add1.c" "add1"
    , isSafe "branch.c" "branch"
    , isSafe "compare_to_null.c" "compare_to_null"
    , isSafe "factorial.c" "factorial"  -- TODO only up to the recursion bound?
    , isSafe "loop_arg_bound.c" "loop_arg_bound"
    , isSafe "loop_constant_bound_arg_start.c" "loop_constant_bound_arg_start"
    , isSafe "print.c" "print"
    , isSafe "assert_arg_eq.c" "assert_arg_eq" -- TODO: Compile with asserts!
    , isSafe "assert_false.c" "assert_false" -- TODO: Compile with asserts!
    , isSafe "read_global.c" "read_global"
    , isSafe "write_global.c" "write_global"
    , isSafeWithPreconditions "deref_arg.c" "deref_arg"
    , isSafeWithPreconditions "deref_struct_field.c" "deref_struct_field"
    , isSafeWithPreconditions "do_strlen.c" "do_strlen"  -- TODO: Why is this safe??
    , isSafeWithPreconditions "writes_to_arg.c" "writes_to_arg"
    , isSafeWithPreconditions "writes_to_arg_conditional.c" "writes_to_arg_conditional"
    , isSafeWithPreconditions "writes_to_arg_conditional_ptr.c" "writes_to_arg_conditional_ptr"
    , isUnclassified "do_exit.c" "do_exit"  -- goal: isSafe
    , isUnclassified "do_fork.c" "do_fork"
    , isUnclassified "do_getchar.c" "do_getchar"  -- goal: isSafe
    , isUnclassified "do_memcpy.c" "do_memcpy"  -- goal: isSafeWP
    , isUnclassified "do_memset.c" "do_memset"  -- goal: isSafeWP
    , isUnclassified "do_recv.c" "do_recv"
    , isUnclassified "linked_list_sum.c" "linked_list_sum"  -- goal: isSafe
    , isUnclassified "nested_structs.c" "nested_structs"
    , isUnclassified "oob_read_heap.c" "oob_read_heap"  -- goal: notSafe
    , isUnclassified "oob_read_stack.c" "oob_read_stack"  -- goal: notSafe
    , isUnclassified "ptr_as_array.c" "ptr_as_array"  -- goal: isSafe
    , isUnclassified "sized_array_arg.c" "sized_array_arg"  -- goal: isSafe
    , isUnclassified "uninitialized_stack.c" "uninitialized_stack"  -- goal: notSafe
    , isUnclassified "writes_to_arg_ptr.c" "writes_to_arg_ptr"  -- goal: isSafeWP
    , isUnimplemented "add1_double.c" "add1_double"  -- goal: ???
    , isUnimplemented "add1_float.c" "add1_float"  -- goal: ???
    , isUnimplemented "call_function_pointer.c" "call_function_pointer"  -- goal: ???

    -- TODO: Not sure if Crux can do C++?
    -- , isSafe "cxxbasic.cpp" "cxxbasic"
    ]
