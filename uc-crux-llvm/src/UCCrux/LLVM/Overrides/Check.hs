{-
Module       : UCCrux.LLVM.Overrides.Check
Description  : Overrides that check that deduced preconditions are met.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

After UC-Crux-LLVM has deduced the preconditions of a function, it can install
an override that checks that the preconditions are met at callsites.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Overrides.Check
  ( CheckOverrideName (..),
    createCheckOverride,
    checkOverrideFromResult,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Control.Monad (foldM, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable.WithIndex (FoldableWithIndex, ifoldrM)
import           Data.Functor.Compose (Compose(Compose))
import           Data.IORef (IORef, modifyIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IndexF)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.TraversableFC.WithIndex (FoldableFCWithIndex, ifoldrMFC)

-- what4
import           What4.Interface (Pred)

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (LLVM, OverrideTemplate(..), LLVMOverride(..), basic_llvm_override)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (Constraint, Constraints, ConstrainedShape(..), argConstraints)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleDecls, moduleTypes)
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(SomeIndex), translateIndex, toCrucibleType)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr, MapToCrucibleType, ToCrucibleType, pointedToType, arrayElementType)
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol)
import           UCCrux.LLVM.Overrides.Basic (BasicLLVMOverride, makeBasicLLVMOverride)
import           UCCrux.LLVM.Run.Result (BugfindingResult)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Setup.Constraints (constraintToPred)
import qualified UCCrux.LLVM.Shape as Shape
{- ORMOLU_ENABLE -}

newtype CheckOverrideName = CheckOverrideName {getCheckOverrideName :: Text}
  deriving (Eq, Ord, Show)

declName :: L.Declare -> Text
declName decl =
  let L.Symbol name = L.decName decl
   in Text.pack name

-- TODO: Alignment...?
-- TODO: We probably want to use 'loadRaw' and capture the assertions directly
doLoad ::
  forall arch m sym ft.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr ft)) ->
  FullTypeRepr m ('FTPtr ft) ->
  IO (Crucible.RegValue sym (ToCrucibleType arch ft))
doLoad modCtx sym mem val fullTypeRepr =
  let pointedToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
  in LLVMMem.doLoad
       sym
       mem
       val
       (toStorageType pointedToRepr)
       (toCrucibleType modCtx pointedToRepr)
       noAlignment -- TODO Is this right?

ifoldMapM ::
  FoldableWithIndex i t =>
  Monoid m =>
  Monad f =>
  (i -> a -> f m) ->
  t a ->
  f m
ifoldMapM f = ifoldrM (\i x acc -> fmap (<> acc) (f i x)) mempty

ifoldMapMFC ::
  FoldableFCWithIndex t =>
  Monoid m =>
  Monad g =>
  (forall x. IndexF (t f z) x -> f x -> g m) ->
  t f z ->
  g m
ifoldMapMFC f = ifoldrMFC (\i x acc -> fmap (<> acc) (f i x)) mempty

-- | Create a predicate that checks that a Crucible(-LLVM) value conforms to the
-- 'ConstrainedShape'.
--
-- TODO: Add selector for provenance
checkConstraints ::
  forall arch m sym ft.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  ConstrainedShape m ft ->
  FullTypeRepr m ft ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (Seq (Pred sym))
checkConstraints modCtx sym mem cShape fullTypeRepr val =
  case getConstrainedShape cShape of
    Shape.ShapeInt (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeFloat (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeUnallocated ->
      constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeAllocated {}) ->
      constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeInitialized subShapes) ->
      do -- TODO: Is there code from Setup that helps with the other addresses?
         unless (Seq.length subShapes == 1) $ error "Only support length 1"
         ptdToVal <- doLoad modCtx sym mem val fullTypeRepr
         let shape = ConstrainedShape (subShapes `Seq.index` 0)
         let ptdToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         subs <- checkConstraints modCtx sym mem shape ptdToRepr ptdToVal
         here <- constraintsToPreds fullTypeRepr cs val
         return (here <> subs)
    Shape.ShapeFuncPtr (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeOpaquePtr (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeArray (Compose cs) _ subShapes ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstraints
                 modCtx
                 sym
                 mem
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! (fromIntegral (Fin.finToNat i))))
            subShapes
    Shape.ShapeUnboundedArray (Compose cs) subShapes ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstraints
                 modCtx
                 sym
                 mem
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! i))
            subShapes
    Shape.ShapeStruct (Compose cs) _ ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> error "struct"
  where
    foldMapM :: forall t f m' a. Foldable t => Monoid m' => Monad f => (a -> f m') -> t a -> f m'
    foldMapM f = foldM (\acc -> fmap (<> acc) . f) mempty

    constraintsToPreds ::
      forall ft'.
      FullTypeRepr m ft' ->
      [Constraint m ft'] ->
      Crucible.RegValue sym (ToCrucibleType arch ft') ->
      IO (Seq (Pred sym))
    constraintsToPreds ftRepr cs v =
      foldMapM (\c -> Seq.singleton <$> constraintToPred modCtx sym c ftRepr v) cs

createCheckOverride ::
  forall arch sym m argTypes ret blocks rtp l a.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?lc :: TypeContext) =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  -- | Set of check overrides encountered during execution
  --
  -- TODO: Add constraint, selector for provenance
  IORef (Map CheckOverrideName [Pred sym]) ->
  -- | Function argument types
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Function contract to check
  Constraints m argTypes ->
  -- | Function implementation
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Name of function to override
  FuncSymbol m ->
  OverrideTemplate LLVM sym arch rtp l a
createCheckOverride modCtx usedRef argFTys constraints cfg funcSym =
  let decl = modCtx ^. moduleDecls . funcSymbol funcSym
      name = declName decl
  in basic_llvm_override $
       LLVMOverride
         { llvmOverride_declare = decl,
           llvmOverride_args = Crucible.cfgArgTypes cfg,
           llvmOverride_ret = Crucible.cfgReturnType cfg,
           llvmOverride_def =
             \mvar (sym :: sym) args ->
               Override.modifyGlobal mvar $ \mem ->
                 do
                   -- TODO: Lift out into where
                   (argCs :: Seq (Pred sym)) <-
                     liftIO $
                       ifoldMapMFC
                          (\idx constraint ->
                            do SomeIndex idx' Refl <-
                                 pure $
                                   translateIndex
                                     modCtx
                                     (Ctx.size (constraints ^. argConstraints))
                                     idx
                               let arg = args Ctx.! idx'
                               checkConstraints
                                 modCtx
                                 sym
                                 mem
                                 constraint
                                 (argFTys Ctx.! idx)
                                 (Crucible.regValue arg))
                          (constraints ^. argConstraints)
                   -- TODO: Globals
                   let nm = CheckOverrideName name
                   liftIO $
                     modifyIORef usedRef $
                       \m -> foldr (Map.insertWith (++) nm . (:[])) m argCs
                   retEntry <- Crucible.callCFG cfg (Crucible.RegMap args)
                   return (Crucible.regValue retEntry, mem)
         }

-- | Create an override for checking deduced preconditions
checkOverrideFromResult ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?lc :: TypeContext) =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  IORef (Map CheckOverrideName [Pred sym]) ->
  -- | Function argument types
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Function implementation
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Name of function to override
  FuncSymbol m ->
  -- | Result from which to take constraints
  BugfindingResult m arch argTypes ->
  Maybe BasicLLVMOverride
checkOverrideFromResult modCtx ref argFTys cfg f result =
  case Result.summary result of
    Result.SafeWithPreconditions _bounds _unsound constraints ->
      Just $
        makeBasicLLVMOverride $
          createCheckOverride
            modCtx
            ref
            argFTys
            constraints
            cfg
            f
    _ -> Nothing

-- createCheckOverride ::
--   IsSymInterface sym =>
--   HasLLVMAnn sym =>
--   ArchOk arch =>
--   (?lc :: TypeContext) =>
--   ModuleContext m arch ->
--   sym ->
--   -- | Set of check overrides encountered during execution
--   IORef (Map CheckOverrideName [Pred sym]) ->
--   -- | Function contract to check
--   Constraints m argTypes ->
--   -- | Name of function to override
--   FuncSymbol m ->
--   Maybe (OverrideTemplate LLVM sym arch rtp l a)
-- createCheckOverride modCtx sym usedRef constraints funcSym =
--   let decl = modCtx ^. moduleDecls . funcSymbol funcSym
--       name = declName decl
--   in
--     case findFun modCtx funcSym of
--       CFGWithTypes cfg argFTys retFTy (Some varArgs) ->
--         Just $ createCheckOverride' modCtx sym usedRef argFTys constraints cfg funcSym
