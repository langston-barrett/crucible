{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures -fno-warn-incomplete-uni-patterns #-}

module Clobber (clobberTests) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Data.Functor.Compose (Compose(Compose))
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import qualified Data.Set as Set

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (knownNat)

import qualified Lang.Crucible.CFG.Core as Crucible

import           Lang.Crucible.LLVM.Translation (transContext, llvmTypeCtx)

import qualified Crux.LLVM.Config as CruxLLVM

import           UCCrux.LLVM.Constraints (ConstrainedShape(..), emptyConstraints)
import           UCCrux.LLVM.Context.Module (CFGWithTypes(..), defnTypes, findFun, withModulePtrWidth, moduleTranslation, declTypes)
import           UCCrux.LLVM.Context.Function (makeFunctionContext, ppFunctionContextError)
import qualified UCCrux.LLVM.Cursor as Cursor
import qualified UCCrux.LLVM.FullType.Type as FT
import           UCCrux.LLVM.Module (FuncSymbol(FuncDefnSymbol, FuncDeclSymbol), makeDeclSymbol)
import           UCCrux.LLVM.Newtypes.FunctionName (functionNameFromString)
import qualified UCCrux.LLVM.Run.EntryPoints as EntryPoints
import qualified UCCrux.LLVM.Run.Simulate as Sim
import qualified UCCrux.LLVM.Overrides.Skip as Skip
import qualified UCCrux.LLVM.Shape as Shape

-- Tests
import qualified Utils
{- ORMOLU_ENABLE -}

clobberTests :: TT.TestTree
clobberTests =
  TT.testGroup
    "clobbering"
    [ TH.testCase
        "clobbers_arg.c"
        ( Utils.withOptions
            Nothing
            "clobbers_arg.c"
            (\appCtx modCtx halloc cruxOpts llOpts ->
               do [caller] <-
                    EntryPoints.getEntryPoints <$>
                      EntryPoints.makeEntryPointsOrThrow
                        (modCtx ^. defnTypes)
                        [functionNameFromString "calls_clobbers_arg"]
                  let Just callee =
                        makeDeclSymbol
                          (L.Symbol "clobbers_arg")
                          (modCtx ^. declTypes)
                  () <-
                    withModulePtrWidth modCtx $
                      do CFGWithTypes cfg argFTys _retTy _varArgs <-
                           pure (findFun modCtx (FuncDefnSymbol caller))
                         funCtx <-
                           case makeFunctionContext modCtx caller argFTys (Crucible.cfgArgTypes cfg) of
                             Left err ->
                               error (Text.unpack (ppFunctionContextError err))
                             Right funCtx -> return funCtx
                         let ?memOpts = CruxLLVM.memOpts llOpts
                         let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
                         let
                           -- This type signature is necessary for some
                           -- reason...
                           msg = "Test failure: 'clobbers_arg'"
                           i32p = FT.FTPtrRepr (FT.toPartType (FT.FTIntRepr (knownNat @32)))
                           specs =
                             Skip.ClobberSpecs
                               { Skip.sometimesClobber = Map.empty
                               , Skip.alwaysClobber =
                                   [ Skip.SomeClobberSpec $
                                       Skip.ClobberSpec
                                         { Skip.clobberSelector =
                                           Skip.ClobberSelectArgument
                                             (Ctx.baseIndex)
                                             (Cursor.Here i32p)
                                         , Skip.clobberType = i32p
                                         , Skip.clobberShape =
                                             ConstrainedShape
                                               (Shape.ShapeInt (Compose []))
                                         }
                                   ]
                               }

                           callbacks :: Sim.SimulatorCallbacks m _ _ _
                           callbacks =
                             Sim.SimulatorCallbacks $
                               do nameRef <- IORef.newIORef Set.empty
                                  annRef <- IORef.newIORef Map.empty
                                  return $
                                    Sim.SimulatorHooks
                                      { Sim.createOverrideHooks =
                                          [ Sim.SymCreateOverrideFn $
                                              \sym ->
                                                return $
                                                  fromMaybe (error msg) $
                                                    Skip.createSkipOverride
                                                      modCtx
                                                      sym
                                                      nameRef
                                                      annRef
                                                      specs
                                                      Nothing
                                                      (FuncDeclSymbol callee)
                                          ]
                                      , Sim.resultHook =
                                        \_sym _mem _args _cruxResult _ucCruxResult ->
                                          do calls <- IORef.readIORef nameRef
                                             TH.assertEqual
                                               "The override for 'clobbers_arg' was exec'd"
                                               1
                                               (length calls)
                                             return ()
                                      }
                         Sim.runSimulatorWithCallbacks
                           appCtx
                           modCtx
                           funCtx
                           halloc
                           (emptyConstraints argFTys)
                           cfg
                           cruxOpts
                           llOpts
                           callbacks
                        -- TODO(lb): confirm that the result indicates safety
                  return ()
            )
        )
    ]
