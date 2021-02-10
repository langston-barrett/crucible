{-# Language OverloadedStrings #-}

module Bugfinding (tests) where

import System.FilePath ((</>))
import System.IO (IOMode(WriteMode), withFile)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           Data.Parameterized.Some (Some(Some))

import qualified Crux
import           CruxLLVMMain (processLLVMOptions)
import           Crux.LLVM.Compile (genBitCode)
import           Crux.LLVM.Config (LLVMOptions(entryPoint), llvmCruxConfig)

-- Code being tested
import           Crux.LLVM.Bugfinding (BugfindingResult(..), translateAndLoop)

testDir :: FilePath
testDir = "tests/bugfinding"

findBugs :: FilePath -> String -> IO (Some BugfindingResult)
findBugs file fn =
  do withFile (testDir </> "output") WriteMode $ \h ->
       do let outCfg = Crux.OutputConfig False h h True
          Crux.loadOptions outCfg "crux-llvm" "0.1" llvmCruxConfig $ \(initCrux, initLlvm) ->
            do (cruxOpts, llvmOpts) <-
                 processLLVMOptions ( initCrux { Crux.inputFiles = [testDir </> file]
                                               , Crux.loopBound = Just 8
                                               }
                                    , initLlvm { entryPoint = fn }
                                    )
               genBitCode cruxOpts llvmOpts
               putStrLn (unwords [ "Reproduce with:\n"
                                 , "cabal v2-run exe:crux-llvm -- "
                                 , "--bugfinding"
                                 , "--entry-point"
                                 , fn
                                 , testDir </> file
                                 ])
               translateAndLoop cruxOpts llvmOpts

isSafe :: FilePath -> String -> TT.TestTree
isSafe file fn =
  TH.testCase (fn <> " is safe") $
    do Some result <- findBugs file fn
       case result of
         AlwaysSafe -> pure ()
         _ -> TH.assertFailure (unwords ["Expected", fn, "to be safe"])

isSafeWithPreconditions :: FilePath -> String -> TT.TestTree
isSafeWithPreconditions file fn =
  TH.testCase (fn <> " is safe") $
    do Some result <- findBugs file fn
       case result of
         SafeWithPreconditions _preconditions -> pure ()
         _ -> TH.assertFailure (unwords ["Expected", fn, "to be safe with preconditions"])

tests :: TT.TestTree
tests =
  TT.testGroup "bugfinding"
    [ isSafe "add1.c" "add1"
    , isSafe "branch.c" "branch"
    , isSafe "compare_to_null.c" "compare_to_null"
    , isSafe "loop_arg_bound.c" "loop_arg_bound"
    , isSafe "loop_constant_bound_arg_start.c" "loop_constant_bound_arg_start"
    , isSafe "print.c" "print"
    , isSafe "read_global.c" "read_global"
    , isSafe "write_global.c" "write_global"
    , isSafeWithPreconditions "deref_arg.c" "deref_arg"
    , isSafeWithPreconditions "deref_struct_field.c" "deref_struct_field"
    , isSafeWithPreconditions "writes_to_arg.c" "writes_to_arg"
    , isSafeWithPreconditions "writes_to_arg_conditional.c" "writes_to_arg_conditional"
    , isSafeWithPreconditions "writes_to_arg_conditional_ptr.c" "writes_to_arg_conditional_ptr"
    -- TODO: Unimplemented
    -- , isSafeWithPreconditions "do_memcpy.c" "do_memcpy"
    -- , isSafeWithPreconditions "do_memset.c" "do_memset"
    -- , isSafeWithPreconditions "ptr_as_array.c" "ptr_as_array"
    -- , isSafeWithPreconditions "writes_to_arg_ptr.c" "writes_to_arg_ptr"
    -- , notSafe "uninitialized_stack.c" "uninitialized_stack"
    -- , notSafe "oob_read_heap.c" "oob_read_heap"
    -- , notSafe "oob_read_stack.c" "oob_read_stack"
    ]
