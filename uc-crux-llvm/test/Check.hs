{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

module Check (checkOverrideTests) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import qualified Data.Text as Text

import           What4.Interface (Pred)

import qualified Lang.Crucible.CFG.Core as Crucible

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           Lang.Crucible.LLVM.Translation (llvmPtrWidth, transContext)

import           UCCrux.LLVM.Context.Function (makeFunctionContext, ppFunctionContextError)
import           UCCrux.LLVM.Context.Module (CFGWithTypes(..), defnTypes, moduleTranslation, findFun, withModulePtrWidth)
import           UCCrux.LLVM.Module (FuncSymbol(FuncDefnSymbol))
import           UCCrux.LLVM.Newtypes.FunctionName (functionNameFromString)
import qualified UCCrux.LLVM.Overrides.Check as Check
import qualified UCCrux.LLVM.Run.EntryPoints as EntryPoints
import           UCCrux.LLVM.Run.Loop (bugfindingLoop, loopOnFunction)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Simulate (noSetupAction)

-- Tests
import qualified Utils
{- ORMOLU_ENABLE -}

checkOverrideTests :: TT.TestTree
checkOverrideTests =
  TT.testGroup
    "check overrides"
    [ TH.testCase
        "disjunctive generalization"
        (Utils.withOptions
          Nothing
          "check_disjunctive_generalization.c"
          (\appCtx modCtx halloc cruxOpts llOpts ->
             do [f] <-
                  EntryPoints.getEntryPoints <$>
                    EntryPoints.makeEntryPointsOrThrow
                      (modCtx ^. defnTypes)
                      [functionNameFromString "f"]

                withModulePtrWidth
                  modCtx
                  ( do
                      CFGWithTypes cfg argFTys _retTy _varArgs <-
                        pure (findFun modCtx (FuncDefnSymbol f))

                      ref <- IORef.newIORef Map.empty

                      case makeFunctionContext modCtx f argFTys (Crucible.cfgArgTypes cfg) of
                        Left err ->
                          error (Text.unpack (ppFunctionContextError err))
                        Right funCtx ->
                          do -- Run main loop on f, to deduce the precondition
                             -- that y should be nonnull
                             (result, _) <-
                               bugfindingLoop
                                 appCtx
                                 modCtx
                                 funCtx
                                 noSetupAction
                                 cfg
                                 cruxOpts
                                 llOpts
                                 halloc

                             -- Construct override that checks that y is nonnull
                             let maybeOv =
                                   Check.checkOverrideFromResult
                                     modCtx
                                     ref
                                     argFTys
                                     cfg
                                     (FuncDefnSymbol f)
                                     result

                             -- Run main loop on g, but with additional check
                             -- override

                             -- Confirm that the resulting map is nonempty
                             -- Confirm that the predicate is
                             return ()
                  )
                _
          )
        )

    ]
