{-
Module       : UCCrux.LLVM.Overrides.Skip
Description  : Unsound overrides for skipping execution of functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Overrides.Skip
  ( SkipOverrideName (..),
    ClobberSpecs (..),
    ClobberSpec (..),
    ClobberSelector (..),
    emptyClobberSpecs,
    unionClobberSpecs,
    SomeClobberSpec (..),
    unsoundSkipOverrides,
    createSkipOverride,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), use, to)
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef, modifyIORef)
import           Data.Maybe (mapMaybe, fromMaybe)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (intValue)
import           Data.Parameterized.Some (Some(Some))

-- what4
import           What4.Interface (Pred)
import qualified What4.Interface as What4
import           What4.FunctionName (functionName)
import           What4.ProgramLoc (ProgramLoc)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.FunctionHandle (SomeHandle(..), handleMapToHandles, handleName)
import           Lang.Crucible.Simulator.ExecutionTree (functionBindings, stateContext, fnBindings)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM.Extension (LLVM, ArchWidth)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, LLVMPointerType, MemImpl, MemOptions)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx, llvmDeclToFunHandleRepr')
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (LLVMOverride(..), basic_llvm_override)

import           Crux.Types (OverM)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (ConstrainedTypedValue(..), minimalConstrainedShape, ConstrainedShape)
import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes, moduleTypes, moduleDecls)
import           UCCrux.LLVM.Cursor (Selector(..), Cursor(..), deepenPtr, seekType)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(SometimesClobber))
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import           UCCrux.LLVM.FullType.Translation (FunctionTypes, ftRetType)
import           UCCrux.LLVM.FullType.Type (ModuleTypes, FullType(FTPtr), FullTypeRepr(..), ToCrucibleType, pointedToType, asFullType)
import           UCCrux.LLVM.Module (GlobalSymbol, FuncSymbol, funcSymbol, makeFuncSymbol, isDebug)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Setup (SymValue(getSymValue), generate)
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Setup.Monad (TypedSelector, runSetup, resultAssumptions, resultMem, resultAnnotations)
import qualified UCCrux.LLVM.Shape as Shape
{- ORMOLU_ENABLE -}

newtype SkipOverrideName = SkipOverrideName {getSkipOverrideName :: Text}
  deriving (Eq, Ord, Show)

declName :: L.Declare -> Text
declName decl =
  let L.Symbol name = L.decName decl
   in Text.pack name

-- | Additional overrides that are useful for bugfinding, but not for
-- verification. They skip execution of the specified functions.
--
-- Mostly useful for functions that are declared but not defined.
--
-- This won't register overrides for functions that already have associated
-- CFGs, like if you already registered a normal override for `free` or similar.
unsoundSkipOverrides ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  sym ->
  ModuleTranslation arch ->
  -- | Set of skip overrides encountered during execution
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | What data should get clobbered by this override?
  Map (FuncSymbol m) (ClobberSpecs m) ->
  -- | Postconditions of each override (constraints on return values)
  Map (FuncSymbol m) (ConstrainedTypedValue m) ->
  [L.Declare] ->
  OverM personality sym LLVM [PolymorphicLLVMOverride arch (personality sym) sym]
unsoundSkipOverrides modCtx sym mtrans usedRef annotationRef clobbers postconditions decls =
  do
    let llvmCtx = mtrans ^. transContext
    let ?lc = llvmCtx ^. llvmTypeCtx
    binds <- use (stateContext . functionBindings)
    let alreadyDefined =
          Set.fromList $
            map
              (\(SomeHandle hand) -> functionName (handleName hand))
              (handleMapToHandles (fnBindings binds))
    let create decl =
          case modCtx ^. funcTypes . to (makeFuncSymbol (L.decName decl)) of
            Nothing ->
              panic
                "unsoundSkipOverrides"
                ["Precondition violation: Declaration not in module"]
            Just funcSym ->
              createSkipOverride
                modCtx
                sym
                usedRef
                annotationRef
                (fromMaybe emptyClobberSpecs $ Map.lookup funcSym clobbers)
                (Map.lookup funcSym postconditions)
                funcSym
    pure $
      mapMaybe
        create
        ( filter
            ((`Set.notMember` alreadyDefined) . declName)
            (filter (not . isDebug) decls)
        )

-- | A 'ClobberSelector' points to a spot inside an argument or global variable
data ClobberSelector m (argTypes :: Ctx (FullType m)) inTy atTy
  = ClobberSelectArgument !(Ctx.Index argTypes inTy) (Cursor m inTy atTy)
  | ClobberSelectGlobal !(GlobalSymbol m) (Cursor m inTy atTy)
  deriving Eq

_clobberSelectorToSelector ::
  ClobberSelector m argTypes inTy atTy ->
  Selector m argTypes inTy atTy
_clobberSelectorToSelector =
  \case
    ClobberSelectArgument idx cursor -> SelectArgument idx cursor
    ClobberSelectGlobal glob cursor -> SelectGlobal glob cursor

clobberSelectorCursor ::
  ClobberSelector m argTypes inTy atTy ->
  Cursor m inTy atTy
clobberSelectorCursor =
  \case
    ClobberSelectArgument _idx cursor -> cursor
    ClobberSelectGlobal _glob cursor -> cursor

getContainer ::
  proxy arch ->
  MemImpl sym ->
  Ctx.Assignment (Crucible.RegEntry sym) args ->
  ClobberSelector m argTypes inTy atTy ->
  IO (Crucible.RegValue sym (ToCrucibleType arch inTy))
getContainer proxy mem args =
  \case
    ClobberSelectArgument idx cursor -> error "TODO(lb)"
    ClobberSelectGlobal glob cursor -> error "TODO(lb)"

-- | What data should this override clobber?
data ClobberSpec m (argTypes :: Ctx (FullType m)) inTy atTy
  = ClobberSpec
      { clobberSelector :: ClobberSelector m argTypes inTy ('FTPtr atTy),
        -- | Type of value that contains the pointer
        clobberType :: FullTypeRepr m inTy,
        -- | Constraints on data to write
        clobberShape :: ConstrainedShape m atTy
      }
  deriving Eq

data SomeClobberSpec m
  = forall (argTypes :: Ctx (FullType m)) inTy atTy.
      SomeClobberSpec (ClobberSpec m argTypes inTy atTy)

clobberAtType ::
  ModuleTypes m ->
  ClobberSpec m argTypes inTy atTy ->
  FullTypeRepr m atTy
clobberAtType modTys spec =
  pointedToType
    modTys
    (seekType
      modTys
      (clobberSelectorCursor (clobberSelector spec))
      (clobberType spec))

-- | When and where should this override clobber its arguments?
data ClobberSpecs m
  = ClobberSpecs
      { -- | Stuff to clobber at each call
        alwaysClobber :: [SomeClobberSpec m],
        -- | Stuff to clobber at particular callsites
        sometimesClobber :: Map ProgramLoc [SomeClobberSpec m]
      }

emptyClobberSpecs :: ClobberSpecs m
emptyClobberSpecs =
  ClobberSpecs { alwaysClobber = mempty, sometimesClobber = mempty }

-- | Left-biased union
unionClobberSpecs ::
  ClobberSpecs m ->
  ClobberSpecs m ->
  ClobberSpecs m
unionClobberSpecs cs1 cs2 =
  ClobberSpecs
    { alwaysClobber = alwaysClobber cs1 <> alwaysClobber cs2,
      sometimesClobber = sometimesClobber cs1 <> sometimesClobber cs2
    }

-- TODO(lb): copy-pasted from Check.hs, make new module Mem.hs
-- TODO: Alignment...?
doLoad ::
  forall arch m sym atTy.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
doLoad modCtx sym mem val fullTypeRepr = error "TODO(lb)"

-- | Find a pointer inside of a value
seekPtr ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  -- | Program memory
  MemImpl sym ->
  FullTypeRepr m inTy ->
  -- | Value containing pointer
  Crucible.RegValue sym (ToCrucibleType arch inTy) ->
  -- | Where the pointer is inside the value
  Cursor m inTy ('FTPtr atTy) ->
  IO (Crucible.RegValue sym (LLVMPointerType (ArchWidth arch)))
seekPtr modCtx sym mem fullTypeRepr container cursor =
  case (fullTypeRepr, cursor) of
    -- (FTIntRepr w, _) -> error "absurd"
    -- (FTFloatRepr fi, _) -> error "absurd"
    -- (FTNonVoidFuncPtrRepr {}, _) -> error "absurd"
    -- (FTVoidFuncPtrRepr {}, _) -> error "absurd"
    -- (FTUnboundedArrayRepr {}, _) -> error "absurd"
    -- (FTOpaquePtrRepr _ident, _) -> error "absurd"
    (FTArrayRepr n fullTypeRepr', Index i _ cursor') ->
      seekPtr
        modCtx
        sym
        mem
        fullTypeRepr'
        -- TODO(lb): overflow
        (container Vec.! fromIntegral (intValue i))
        cursor'
    (FTStructRepr {}, _) -> error "TODO(lb): struct"
    (FTPtrRepr ptRepr, Dereference i cursor') ->
      do (_pred, Just newVal) <- doLoad modCtx sym mem container fullTypeRepr
         -- TODO(lb): assert pred
         -- TODO(lb): handle Nothing
         let ftPtdTo = asFullType (modCtx ^. moduleTypes) ptRepr
         seekPtr modCtx sym mem ftPtdTo newVal cursor'
    (FTPtrRepr ptRepr, Here _) -> return container


write ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  -- | Program memory
  MemImpl sym ->
  FullTypeRepr m inTy ->
  -- | Value containing pointer
  Crucible.RegValue sym (ToCrucibleType arch inTy) ->
  -- | Where the pointer is inside the value
  Cursor m inTy ('FTPtr atTy) ->
  -- | Value to write to pointer
  Crucible.RegValue sym (ToCrucibleType arch atTy) ->
  -- | Resulting program memory
  IO (MemImpl sym)
write modCtx sym mem fullTypeRepr container cursor contained =
  error "TODO(lb)"


-- TODO(lb): At some point, it'd be nice to apply heuristics to the manufactured
-- return values, similar to those for function arguments. To do this, this
-- function would probably need to take an IORef in which to insert annotations
-- for values it creates.
createSkipOverride ::
  forall m arch sym argTypes personality.
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  sym ->
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | What data should get clobbered by this override?
  ClobberSpecs m ->
  -- | Constraints on the return value
  Maybe (ConstrainedTypedValue m) ->
  FuncSymbol m ->
  Maybe (PolymorphicLLVMOverride arch (personality sym) sym)
createSkipOverride modCtx sym usedRef annotationRef clobbers postcondition funcSym =
  llvmDeclToFunHandleRepr' decl $
    \args ret ->
      Just $
        makePolymorphicLLVMOverride $
          basic_llvm_override $
            LLVMOverride
              { llvmOverride_declare = decl,
                llvmOverride_args = args,
                llvmOverride_ret = ret,
                llvmOverride_def =
                  \mvar _sym args ->
                    do
                      liftIO $
                        modifyIORef usedRef (Set.insert (SkipOverrideName name))
                      Override.modifyGlobal mvar $
                        \mem ->
                          liftIO $
                            do mem' <- doClobber mem args clobbers
                               returnValue
                                 mem'
                                 ret
                                 (modCtx ^. funcTypes . funcSymbol funcSym)
              }
  where
    decl = modCtx ^. moduleDecls . funcSymbol funcSym
    name = declName decl
    symbolName = L.decName decl

    -- @args@ and @args'@ may differ - a 'ClobberSpec' may give a type signature
    -- that doesn't exactly match the function's declaration, for the purpose of
    -- e.g. saying that a specific type of value should be written to a @void*@.
    clobber ::
      MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) args ->
      ClobberSpec m args' inTy atTy ->
      IO (MemImpl sym)
    clobber mem args spec =
      let modTys = modCtx ^. moduleTypes
      in
        runSetup
          modCtx
          mem
          ( generate
              sym
              modCtx
              (clobberAtType modTys spec)
              (SelectClobbered
                 funcSym
                 (deepenPtr
                   modTys
                   (clobberSelectorCursor (clobberSelector spec))))
              (clobberShape spec)
          )
          >>=
            \case
              (result, value) ->
                do
                  assume name sym (resultAssumptions result)
                  -- The keys are nonces, so they'll never clash, so the
                  -- bias of the union is unimportant.
                  modifyIORef annotationRef (Map.union (resultAnnotations result))
                  container <-
                    getContainer modCtx mem args (clobberSelector spec)
                  write
                    modCtx
                    sym
                    (resultMem result)
                    (clobberType spec)
                    container
                    (clobberSelectorCursor (clobberSelector spec))
                    (value ^. Shape.tag . to getSymValue)

    doClobber ::
      MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) args ->
      ClobberSpecs m ->
      IO (MemImpl sym)
    doClobber mem args clobbers =
      if not (Map.null (sometimesClobber clobbers))
      then unimplemented "doClobber" SometimesClobber
      else
        foldM
          (\mem' (SomeClobberSpec spec) -> clobber mem' args spec)
          mem
          (alwaysClobber clobbers)

    returnValue ::
      MemImpl sym ->
      CrucibleTypes.TypeRepr ty ->
      FunctionTypes m arch ->
      IO (Crucible.RegValue sym ty, MemImpl sym)
    returnValue mem ret fTypes =
      case (ret, ftRetType fTypes) of
        (CrucibleTypes.UnitRepr, Nothing) -> pure ((), mem)
        (CrucibleTypes.UnitRepr, _) ->
          panic
            "createSkipOverride"
            ["Mismatched return types - CFG was void"]
        (_, Nothing) ->
          panic
            "createSkipOverride"
            ["Mismatched return types - CFG was non-void"]
        (_, Just (Some retFullType)) ->
          case testEquality (toCrucibleType (Proxy :: Proxy arch) retFullType) ret of
            Nothing ->
              panic
                "createSkipOverride"
                ["Mismatched return types"]
            Just Refl ->
              runSetup
                modCtx
                mem
                ( generate
                    sym
                    modCtx
                    retFullType
                    ( SelectReturn
                        ( case modCtx ^. funcTypes . to (makeFuncSymbol symbolName) of
                            Nothing ->
                              panic
                                "createSkipOverride"
                                [ "Precondition violation:",
                                  "Declaration not found in module:",
                                  show symbolName
                                ]
                            Just s -> s
                        )
                        (Here retFullType)
                    )
                    ( case postcondition of
                        Just (ConstrainedTypedValue ft shape) ->
                          case testEquality ft retFullType of
                            Just Refl -> shape
                            Nothing ->
                              panic
                                "createSkipOverride"
                                [ "Ill-typed constraints on return value for override "
                                    <> Text.unpack name
                                ]
                        Nothing -> minimalConstrainedShape retFullType
                    )
                )
                >>= \case
                  (result, value) ->
                    do
                      assume name sym (resultAssumptions result)
                      -- The keys are nonces, so they'll never clash, so the
                      -- bias of the union is unimportant.
                      modifyIORef annotationRef (Map.union (resultAnnotations result))
                      pure (value ^. Shape.tag . to getSymValue, resultMem result)
