{-
Module       : Crux.LLVM.Bugfinding.Setup.Monad
Description  : Monad for setting up memory and function args.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Crux.LLVM.Bugfinding.Setup.Monad
  ( Setup
  , SetupError
  , ppSetupError
  , SetupState
  , SetupAssumption(..)
  , SetupResult(..)
  , setupMem
  , TypedSelector(..)
  , freshSymbol
  , assume
  , addAnnotation
  , runSetup
  , seekType
  , malloc
  ) where

import           Control.Lens (to, (.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Control.Monad.Except (throwError, ExceptT, MonadError, runExceptT)
import           Control.Monad.Reader (MonadReader, ask)
import           Control.Monad.State.Strict (MonadState, gets)
import           Control.Monad.Writer (MonadWriter, tell)
import           Control.Monad.RWS (RWST, runRWST)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as What4

import qualified Lang.Crucible.Types as CrucibleTypes

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

-- TODO unsorted
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Bugfinding.Cursor (TypeSeekError, Selector, Cursor, seekMemType)
import           Crux.LLVM.Bugfinding.Context
import           Crux.LLVM.Bugfinding.Constraints (Constraint)
import qualified Lang.Crucible.Backend as Crucible
import Lang.Crucible.LLVM.Extension (ArchWidth)
import Lang.Crucible.LLVM.DataLayout (maxAlignment)
import Data.BitVector.Sized (mkBV)
import Lang.Crucible.LLVM.MemType (SymType, MemType, memTypeSize)
import Lang.Crucible.LLVM.Bytes (bytesToInteger)
import Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))
import qualified Prettyprinter as PP
import           Prettyprinter (Doc)
import Data.Void (Void)

data TypedSelector argTypes tp =
  TypedSelector (Selector argTypes) (CrucibleTypes.BaseTypeRepr tp)

data SetupError
  = SetupTypeSeekError (TypeSeekError SymType)

ppSetupError :: SetupError -> Doc Void
ppSetupError _ = PP.pretty ("unimplemented" :: Text)

data SetupAssumption sym
  = SetupAssumption
      { assumptionReason :: Constraint
      , assumptionPred :: What4.Pred sym
      }

data SetupState sym argTypes =
  SetupState
    { _setupMem :: LLVMMem.MemImpl sym
    , _setupAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector argTypes)
      -- ^ This map tracks where a given expression originated from
    , _symbolCounter :: !Int
      -- ^ Counter for generating unique/fresh symbols
    }

setupMem :: Simple Lens (SetupState sym argTypes) (LLVMMem.MemImpl sym)
setupMem = lens _setupMem (\s v -> s { _setupMem = v })

setupAnnotations :: Simple Lens (SetupState sym argTypes) (MapF (What4.SymAnnotation sym) (TypedSelector argTypes))
setupAnnotations = lens _setupAnnotations (\s v -> s { _setupAnnotations = v })

symbolCounter :: Simple Lens (SetupState sym argTypes) Int
symbolCounter = lens _symbolCounter (\s v -> s { _symbolCounter = v })

newtype Setup arch sym argTypes a =
  Setup
    (ExceptT
      SetupError
      (RWST (Context arch argTypes)
            [SetupAssumption sym]
            (SetupState sym argTypes)
            IO)
      a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadError SetupError (Setup arch sym argTypes)
deriving instance MonadState (SetupState sym argTypes) (Setup arch sym argTypes)
deriving instance MonadReader (Context arch argTypes) (Setup arch sym argTypes)
deriving instance MonadWriter [SetupAssumption sym] (Setup arch sym argTypes)

instance LJ.HasLog Text (Setup arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

data SetupResult sym argTypes =
  SetupResult
    { resultMem :: LLVMMem.MemImpl sym
    , resultAnnotations :: MapF (What4.SymAnnotation sym) (TypedSelector argTypes)
    , resultAssumptions :: [SetupAssumption sym]
    }

runSetup ::
  MonadIO m =>
  Context arch argTypes ->
  LLVMMem.MemImpl sym ->
  Setup arch sym argTypes a ->
  m (Either SetupError (SetupResult sym argTypes, a))
runSetup context mem (Setup computation) = do
  result <-
    liftIO $
      runRWST (runExceptT computation) context (SetupState mem MapF.empty 0)
  pure $
    case result of
      (Left err, _, _) -> Left err
      (Right result', state, assumptions) ->
        Right ( SetupResult (state ^. setupMem)
                            (state ^. setupAnnotations)
                            assumptions
              , result'
              )

freshSymbol :: Setup arch sym argTypes What4.SolverSymbol
freshSymbol =
  do counter <- symbolCounter <+= 1
     pure $ What4.safeSymbol ("fresh" ++ show counter)

assume ::
  Constraint ->
  What4.Pred sym ->
  Setup arch sym argTypes ()
assume constraint predicate = tell [SetupAssumption constraint predicate]

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  What4.SymAnnotation sym tp ->
  Selector argTypes ->
  CrucibleTypes.BaseTypeRepr tp ->
  Setup arch sym argTypes ()
addAnnotation ann selector typeRepr =
  setupAnnotations %= MapF.insert ann (TypedSelector selector typeRepr)

seekType ::
  Cursor ->
  MemType ->
  Setup arch sym argTypes MemType
seekType cursor memType =
  do context <- ask
     let ?lc = context ^. moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
     either (throwError . SetupTypeSeekError) pure (seekMemType cursor memType)


malloc ::
  ( Crucible.IsSymInterface sym
  , ArchOk arch
  ) =>
  sym ->
  MemType ->
  Setup arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
malloc sym memType =
  do context <- ask
     mem <- gets (view setupMem)
     let dl =
           context ^.
             moduleTranslation .
             LLVMTrans.transContext .
             LLVMTrans.llvmTypeCtx .
             to llvmDataLayout
     (ptr, mem') <-
       liftIO $
         do sizeBv <-
              What4.bvLit
                sym
                ?ptrWidth
                (mkBV ?ptrWidth (bytesToInteger (memTypeSize dl memType)))
            LLVMMem.doMalloc
              sym
              LLVMMem.HeapAlloc  -- TODO(lb): Change based on arg/global
              LLVMMem.Mutable  -- TODO(lb): Change based on arg/global
              "crux-llvm bugfinding auto-setup"
              mem
              sizeBv
              (maxAlignment dl) -- TODO is this OK?
     setupMem .= mem'
     pure ptr

{-
debugInfoArgNames :: LLVM.Module -> LLVM.Define -> Map Int Text
debugInfoArgNames m d =
    case Map.lookup "dbg" $ LLVM.defMetadata d of
          Just (LLVM.ValMdRef s) -> scopeArgs s
              _ -> Map.empty
  where
    scopeArgs :: Int -> Map Int Text
    scopeArgs s = go $ LLVM.modUnnamedMd m
      where go :: [LLVM.UnnamedMd] -> Map Int Text
            go [] = Map.empty
            go (LLVM.UnnamedMd
                 { LLVM.umValues =
                   LLVM.ValMdDebugInfo
                     (LLVM.DebugInfoLocalVariable
                       LLVM.DILocalVariable
                       { LLVM.dilvScope = Just (LLVM.ValMdRef s')
                       , LLVM.dilvArg = a
                       , LLVM.dilvName = Just n
                       })}:xs) =
              if s == s' then Map.insert (fromIntegral a) (Text.pack n) $ go xs else go xs
            go (_:xs) = go xs

stmtDebugDeclares :: [LLVM.Stmt] -> Map Int Location
stmtDebugDeclares [] = Map.empty
stmtDebugDeclares
  (LLVM.Result _
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares
  (LLVM.Effect
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares (_:stmts) = stmtDebugDeclares stmts
-}
