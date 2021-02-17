{-
Module           : Crux.LLVM.Bugfinding.FullType.MemType
Description      : Interop between 'FullType' and 'MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Crux.LLVM.Bugfinding.FullType.MemType
  ( toMemType
  , toFullType
  , toFullTypeM
  , asFullType'
  , asFullType
  ) where

import           Data.Functor.Const (Const(Const))
import           Data.Functor.Identity (Identity(runIdentity))
import qualified Data.Vector as Vec
import           Control.Monad.Except (MonadError, runExceptT)
import           Control.Monad.State (MonadState, State, runStateT, get, put, modify)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (mkNatRepr, isPosNat, natValue, LeqProof(..))
import           Data.Parameterized.Some (Some(Some))

import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Overrides (ArchOk)

import           Crux.LLVM.Bugfinding.Errors.Panic (panic)
import           Crux.LLVM.Bugfinding.Errors.Unimplemented (unimplemented)
import           Crux.LLVM.Bugfinding.FullType.Type (FullTypeRepr(..), PartTypeRepr(..))
import           Crux.LLVM.Bugfinding.FullType.ModuleTypes as MT

toMemType :: FullTypeRepr m ft -> MemType
toMemType =
  \case
    FTIntRepr natRepr -> IntType (natValue natRepr)
    FTPtrRepr (PTAliasRepr (Const ident)) -> PtrType (Alias ident)
    FTPtrRepr (PTFullRepr ftRepr) -> PtrType (MemType (toMemType ftRepr))
    FTArrayRepr natRepr fullTypeRepr ->
      ArrayType (natValue natRepr) (toMemType fullTypeRepr)
    FTStructRepr structInfo _ -> StructType structInfo

toFullTypeM ::
  forall arch m f.
  ( MonadState (ModuleTypes m) f
  , MonadError L.Ident f
  ) =>
  MemType ->
  f (Some (FullTypeRepr m))
toFullTypeM memType =
  case memType of
    PtrType (MemType memType) ->
      do Some pointedTo <- toFullTypeM memType
         pure $ Some (FTPtrRepr (PTFullRepr pointedTo))
    -- This case is crucial for safety: We have to store the resulting looked-up
    -- type in the ModuleTypes so that we can look it up in asFullType.
    PtrType (Alias ident) ->
      do mts <- get
         let result = Some (FTPtrRepr (PTAliasRepr (Const ident)))
         case lookupType mts ident of
           Found _ -> -- We've already processed this type, it's safe, move on.
             pure result
           Processing ->
             -- We're processing a recursive circle of types In this case, it's
             -- safe to *not* store the type because our caller will. In fact we
             -- *mustn't* try to calculate it for the sake of termination.
             pure result
           Missing -> -- We haven't yet encountered this type
             do modify (flip processingType ident)
                let ?lc = MT.typeContext mts
                let mt =
                      case asMemType (Alias ident) of
                        Left err ->
                          panic "toFullTypeM"
                                ["Couldn't find type declaration", "Possibly a bug in Clang?"]
                        Right mt -> mt
                Some ftRepr <- toFullTypeM mt
                modify (\mts -> MT.finishedType mts ident (Some ftRepr))
                pure result
    mt@(PtrType _) -> unimplemented "toFullType" ("Translating " ++ show mt)
    IntType w ->
      case mkNatRepr w of
        Some w' | Just LeqProof <- isPosNat w' -> pure (Some (FTIntRepr w'))
        _ -> panic "toPartType" ["Invalid integer width " ++ show w]
    VecType n memType' ->
      do Some contained <- toFullTypeM memType'
         Some natRepr <- pure $ mkNatRepr n
         pure (Some (FTArrayRepr natRepr contained))
    StructType structInfo ->
      do let structInfoFields = MemType.siFields structInfo
         Some fields <-
           Ctx.generateSomeM
             (length structInfoFields)
             (\idx -> toFullTypeM (MemType.fiType (structInfoFields Vec.! idx))
               )
         pure (Some (FTStructRepr structInfo fields))
    _ -> unimplemented "toFullType" ("Translating " ++ show memType)

toFullType ::
  forall arch m.
  ModuleTypes m ->
  MemType ->
  (Either L.Ident (Some (FullTypeRepr m)), ModuleTypes m)
toFullType moduleTypes memType =
  runIdentity $ runStateT (runExceptT (toFullTypeM memType)) moduleTypes

-- | c.f. @asMemType@
asFullType' ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  Either L.Ident (FullTypeRepr m ft)
asFullType' mts =
  \case
    PTFullRepr fullRepr -> Right fullRepr
    PTAliasRepr (Const ident) ->
      let ?lc = MT.typeContext mts
      in case asMemType (Alias ident) of
           Left _err -> Left ident
           Right memType ->
             case toFullType mts memType of
               (Left err, _) -> Left err
               (Right (Some ft), _) ->
                 -- This is safe because of what happens in the Alias case of
                 -- toFullTypeM, namely we check that the alias was properly
                 -- translated in this module.
                 Right (unsafeCoerce ft)

asFullType ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  FullTypeRepr m ft
asFullType mts ptRepr =
  case asFullType' mts ptRepr of
    Right ok -> ok
    Left err ->
      panic "asFullType" [ "Found PartType not made with assignmentToFullType?"
                         , "Don't do that!"
                         ]
