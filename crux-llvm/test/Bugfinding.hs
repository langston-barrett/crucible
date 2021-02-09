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
                 processLLVMOptions ( initCrux { Crux.inputFiles = [testDir </> file] }
                                    , initLlvm { entryPoint = fn }
                                    )
               genBitCode cruxOpts llvmOpts
               putStrLn (unwords [ "Reproduce with"
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

tests :: TT.TestTree
tests =
  TT.testGroup "bugfinding"
    [ TH.testCase "writes_to_arg is safe with preconditions" $
        do Some result <- findBugs "writes_to_arg.c" "writes_to_arg"
           case result of
             SafeWithPreconditions _preconditions -> pure ()
             _ -> TH.assertFailure "blah"
    , isSafe "add1.c" "add1"
    , isSafe "print.c" "print"
    ]
