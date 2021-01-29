-- TODO(lb) trim
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Bugfinding (bugfindingLoop) where

import System.Exit
  ( ExitCode )

import Data.Foldable (for_, toList)
import Data.Type.Equality ((:~:)(Refl), testEquality)
import Data.Proxy (Proxy(..))
import Data.Void (Void)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.String (fromString)
import qualified Data.Map.Strict as Map
import Data.IORef
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)

import System.FilePath( (</>) )
import System.IO (stdout)

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.TraversableFC (foldlMFC)
import qualified Data.Parameterized.Context as Ctx hiding (Assignment)

import Prettyprinter
import Prettyprinter.Render.Text
import Lumberjack as LJ

-- what4
import qualified What4.Interface as What4

-- crucible
import Lang.Crucible.CFG.Core(AnyCFG(..), CFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator
  ( emptyRegMap
  , RegMap(..)
  , fnBindingsFromList, runOverrideSim, callCFG
  , initSimContext, profilingMetrics
  , ExecState( InitialState )
  , SimState, defaultAbortHandler, printHandle
  , ppSimError
  )
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes
import Lang.Crucible.Simulator.ExecutionTree ( stateGlobals )
import Lang.Crucible.Simulator.GlobalState ( lookupGlobal )


-- crucible-llvm
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn )
import Lang.Crucible.LLVM.Globals
        ( initializeAllMemory, populateAllGlobals )
import Lang.Crucible.LLVM.MemModel
        ( MemImpl, withPtrWidth, memAllocCount, memWriteCount
        , MemOptions(..), HasLLVMAnn, LLVMAnnMap
        , explainCex, CexExplanation(..)
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap
        , LLVMContext, llvmMemVar, ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, register_llvm_overrides)

import Lang.Crucible.LLVM.Errors( ppBB )
import Lang.Crucible.LLVM.Extension( ArchWidth, LLVM )
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux
import qualified Crux

import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common

 -- local
import Crux.LLVM.Config
import Crux.LLVM.Compile
import Crux.LLVM.Overrides
import Crux.LLVM.Simulate (parseLLVM, setupSimCtxt, registerFunctions)

-- newtype IOLog a = IOLog { getIOLog :: IO a }
--   deriving (Applicative, Functor, Monad, MonadIO)

class MonadIO m => HasIOLog m

instance HasIOLog IO

instance HasIOLog m => LJ.HasLog Text m where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

findFun ::
  (ArchOk arch, Logs) =>
  String -> ModuleCFGMap arch -> IO (AnyCFG (LLVM arch))
findFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, anyCfg) -> pure anyCfg
    Nothing -> throwCError (MissingFun nm)

generateArg ::
  forall proxy sym arch tp.
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch ->
  sym ->
  Int ->
  CrucibleTypes.TypeRepr tp ->
  IO (Crucible.RegValue sym tp)
generateArg _proxy sym depth typeRepr =
  let unimplemented = error ("Unimplemented: " ++ show typeRepr) -- TODO(lb)
  in
    case CrucibleTypes.asBaseType typeRepr of
      CrucibleTypes.AsBaseType baseTypeRepr ->
        -- TODO(lb): Is this the right behavior?
        -- TODO(lb): Do I need more fresh symbols?
        What4.freshConstant
          sym
          (What4.safeSymbol "whatever")
          baseTypeRepr
      CrucibleTypes.NotBaseType ->
        case typeRepr of
          CrucibleTypes.UnitRepr -> return ()
          CrucibleTypes.AnyRepr ->
            -- TODO(lb): Should be made more complex
            return $ Crucible.AnyValue CrucibleTypes.UnitRepr ()

          -- TODO this doesn't match:
          -- IntrinsicRepr LLVM_pointer [BVRepr 32]
          LLVMMem.PtrRepr -> LLVMMem.mkNullPointer sym ?ptrWidth
          CrucibleTypes.IntrinsicRepr
            symbolRepr
            (Ctx.Empty Ctx.:> (CrucibleTypes.asBaseType ->
                                 CrucibleTypes.AsBaseType
                                   bvRepr@(CrucibleTypes.BaseBVRepr _width))) ->
              case testEquality symbolRepr (CrucibleTypes.knownSymbol :: CrucibleTypes.SymbolRepr "LLVM_pointer") of
                Nothing -> unimplemented
                Just Refl -> do
                  bv <- What4.freshConstant sym (What4.safeSymbol "whatever") bvRepr
                  LLVMMem.llvmPointer_bv sym bv

          -- BoolRepr :: TypeRepr BoolType
          -- NatRepr  :: TypeRepr NatType
          -- IntegerRepr :: TypeRepr IntegerType
          -- RealValRepr :: TypeRepr RealValType
          -- ComplexRealRepr :: TypeRepr ComplexRealType
          -- BVRepr :: (1 <= n) => !(NatRepr n) -> TypeRepr (BVType n)
          -- RecursiveRepr :: IsRecursiveType nm
          --               => SymbolRepr nm
          --               -> CtxRepr ctx
          --               -> TypeRepr (RecursiveType nm ctx)
          -- FloatRepr :: !(FloatInfoRepr flt) -> TypeRepr (FloatType flt)

          -- -- | This is a float with user-definable mantissa and exponent that
          -- -- maps directly to the what4 base type.
          -- IEEEFloatRepr :: !(FloatPrecisionRepr ps) -> TypeRepr (IEEEFloatType ps)

          -- CharRepr :: TypeRepr CharType
          -- StringRepr :: StringInfoRepr si -> TypeRepr (StringType si)
          -- FunctionHandleRepr :: !(CtxRepr ctx)
          --                    -> !(TypeRepr ret)
          --                    -> TypeRepr (FunctionHandleType ctx ret)

          -- MaybeRepr   :: !(TypeRepr tp) -> TypeRepr (MaybeType   tp)
          -- VectorRepr  :: !(TypeRepr tp) -> TypeRepr (VectorType  tp)
          -- StructRepr  :: !(CtxRepr ctx) -> TypeRepr (StructType  ctx)
          -- VariantRepr :: !(CtxRepr ctx) -> TypeRepr (VariantType ctx)
          -- ReferenceRepr :: TypeRepr a -> TypeRepr (ReferenceType a)

          -- WordMapRepr :: (1 <= n)
          --             => !(NatRepr n)
          --             -> !(BaseTypeRepr tp)
          --             -> TypeRepr (WordMapType n tp)

          -- StringMapRepr :: !(TypeRepr tp) -> TypeRepr (StringMapType tp)

          -- SymbolicArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx::>tp))
          --                   -> !(BaseTypeRepr t)
          --                   -> TypeRepr (SymbolicArrayType (idx::>tp) t)

          -- -- A reference to a symbolic struct.
          -- SymbolicStructRepr :: Ctx.signment BaseTypeRepr ctx
          --                    -> TypeRepr (SymbolicStructType ctx)
          _ -> unimplemented -- TODO(lb)

-- TODO(lb): Per-argument depth
doGen ::
  (Crucible.IsSymInterface sym, ArchOk arch) =>
  proxy arch -> sym -> Int -> CrucibleTypes.CtxRepr init -> IO (RegMap sym init)
doGen proxy sym depth types =
  case Ctx.viewAssign types of
    Ctx.AssignEmpty -> pure emptyRegMap
    Ctx.AssignExtend rest typeRepr ->
      Crucible.assignReg
        typeRepr
        <$> (generateArg proxy sym depth typeRepr)
        <*> (doGen proxy sym depth rest)

showRegEntry ::
  forall proxy arch sym ty.
  (Crucible.IsSymInterface sym, ArchOk arch, Logs) =>
  proxy arch ->
  What4.IsSymExprBuilder sym =>
  Crucible.RegEntry sym ty ->
  Text
showRegEntry proxy regEntry =
  case CrucibleTypes.asBaseType (Crucible.regType regEntry) of
    CrucibleTypes.AsBaseType _baseTyRepr ->
      Text.pack (show (What4.printSymExpr (Crucible.regValue regEntry)))
    CrucibleTypes.NotBaseType ->
      case Crucible.regType regEntry of
        CrucibleTypes.UnitRepr -> "()"
        -- TODO(lb): More cases!
        -- LLVMMem.PtrRepr -> Text.pack (show (Crucible.regValue regEntry))
        -- CrucibleTypes.IntrinsicRepr
        --   symbolRepr
        --   (Ctx.Empty Ctx.:> (CrucibleTypes.asBaseType ->
        --                         CrucibleTypes.AsBaseType
        --                           bvRepr@(CrucibleTypes.BaseBVRepr _width))) ->
        --   undefined
        _ -> "unimplemented"

-- | Construct minimal arguments for a function based on the types.
generateMinimalArgs ::
  forall arch sym blocks init ret.
  (Crucible.IsSymInterface sym, ArchOk arch, Logs) =>
  sym ->
  Text ->
  CFG (LLVM arch) blocks init ret ->
  IO (RegMap sym init)
generateMinimalArgs sym entrypoint cfg = do
 writeLogM ("Generating arguments for " <> entrypoint)
 args <- doGen (Proxy :: Proxy arch) sym 0 (cfgArgTypes cfg)
 foldlMFC
   (\n arg ->
      do writeLogM (Text.unwords [ "Argument"
                                 , Text.pack (show n)
                                 , "of"
                                 , entrypoint <> ":"
                                 , Text.pack (show (Crucible.regType arg))
                                 -- TODO(lb): Pretty print?
                                 -- , showRegEntry arg
                                 ])
         return (n + 1))
   (0 :: Int)
   (regMap args)

 return args

-- TODO(lb): Deduplicate with simulateLLVM
simulateLLVM :: CruxOptions -> LLVMOptions -> Crux.SimulatorCallback
simulateLLVM cruxOpts llvmOpts = Crux.SimulatorCallback $ \sym _maybeOnline ->
  do llvm_mod   <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
     halloc     <- newHandleAllocator
     let ?laxArith = laxArithmetic llvmOpts
     let ?optLoopMerge = loopMerge llvmOpts
     Some trans <- translateModule halloc llvm_mod
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
         do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ptrW]
            bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
            let ?lc = llvmCtxt^.llvmTypeCtx
            -- shrug... some weird interaction between do notation and implicit parameters here...
            -- not sure why I have to let/in this expression...
            let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb) in
              do let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt)
                                { printHandle = view outputHandle ?outputConfig }
                 mem <- populateAllGlobals sym (globalInitMap trans)
                           =<< initializeAllMemory sym llvmCtxt llvm_mod

                 let globSt = llvmGlobals llvmCtxt mem

                 let initSt = InitialState simctx globSt defaultAbortHandler CrucibleTypes.UnitRepr $
                          runOverrideSim CrucibleTypes.UnitRepr $
                            do -- TODO(lb): Do this lazily
                               registerFunctions llvm_mod trans
                               let entry = entryPoint llvmOpts
                               AnyCFG cfg <- liftIO $ findFun entry (cfgMap trans)
                               args <- liftIO $ generateMinimalArgs sym (Text.pack entry) cfg
                               callCFG cfg args >> return ()

                 -- arbitrary, we should probabl make this limit configurable
                 let detailLimit = 10

                 -- TODO(lb): Needed?
                 let explainFailure evalFn gl =
                       do bb <- readIORef bbMapRef
                          ex <- explainCex sym bb evalFn >>= \f -> f (gl ^. Crucible.labeledPred)
                          let details = case ex of
                                NoExplanation -> mempty
                                DisjOfFailures xs ->
                                  case map ppBB xs of
                                    []  -> mempty
                                    [x] -> indent 2 x
                                    xs' | length xs' <= detailLimit
                                        -> "All of the following conditions failed:" <> line <> indent 2 (vcat xs')
                                        | otherwise
                                        -> "All of the following conditions failed (and other conditions have been elided to reduce output): "
                                               <> line <> indent 2 (vcat (take detailLimit xs'))

                          return $ vcat [ ppSimError (gl^.Crucible.labeledPredMsg), details ]

                 return (Crux.RunnableState initSt, explainFailure)

ppProofResult ::
  ProofResult (Either Crucible.AssumptionReason Crucible.SimError) -> Doc Void
ppProofResult =
  \case
    Proved _what -> emptyDoc
    NotProved doc model -> doc

ppProvedGoals ::
  ProvedGoals (Either Crucible.AssumptionReason Crucible.SimError) -> Doc Void
ppProvedGoals =
  \case
    AtLoc loc maybeLoc proved -> ppProvedGoals proved
    Branch side1 side2 ->
      nest 2 (vsep ["Branch:", ppProvedGoals side1, ppProvedGoals side2])
    Goal assumptions (error, str) trivial result ->
      viaShow error
      -- ppProofResult result

showProvedGoals ::
  ProvedGoals (Either Crucible.AssumptionReason Crucible.SimError) -> Text
showProvedGoals proved =
  renderStrict (layoutPretty defaultLayoutOptions (ppProvedGoals proved))

-- | The outer loop of bugfinding mode
--
-- TODO(lb): Expand into loop!
bugfindingLoop ::
  (?outputConfig ::  OutputConfig) =>
  CruxOptions ->
  LLVMOptions ->
  IO ExitCode
bugfindingLoop cruxOpts llvmOpts =
  do res <- Crux.runSimulator cruxOpts (simulateLLVM cruxOpts llvmOpts)
     for_ (cruxSimResultGoals res) $ \(processed, proved) ->
       do say "Crux" ("PROCESSED " <> show (totalProcessedGoals processed))
          say "Crux" (Text.unpack $ showProvedGoals proved)
     makeCounterExamplesLLVM cruxOpts llvmOpts res
     Crux.postprocessSimResult cruxOpts res
