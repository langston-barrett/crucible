{-
Module           : Crux.LLVM.Bugfinding.Cursor
Description      : A 'Cursor' points to a specific part of a function argument.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

A 'Cursor' points to a specific part of a value (i.e. a function argument or
global variable). It's used for describing function preconditions, such as
\"@x->y@ must not be null\", or \"x[4] must be nonzero\".
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Crux.LLVM.Bugfinding.Cursor
  ( Cursor(..)
  , ppCursor
  , Selector(..)
  , selectorCursor
  , TypeSeekError(..)
  , ppTypeSeekError
  , seekLlvmType
  , seekMemType
  ) where

import           Control.Lens (Simple, Lens, lens)
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import           Data.Word (Word64)
import           Data.Void (Void)

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some)

import           Lang.Crucible.Types (CrucibleType)

import           Lang.Crucible.LLVM.MemType (MemType, SymType)
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Bugfinding.FullType (FullType)

data Cursor
  = Here
  | Dereference Cursor
  | Index !Word64 Cursor
  | Field !Word64 Cursor
  deriving (Eq, Ord)

-- TODO: Use more type information?
ppCursor ::
  String {-^ Top level, e.g. the name of a variable -} ->
  Cursor ->
  Doc Void
ppCursor top =
  \case
    Here -> PP.pretty top
    Dereference (Field idx cursor) ->
      ppCursor top cursor <> PP.pretty "->" <> PP.pretty (show idx)
    Dereference what -> PP.pretty "*" <> ppCursor top what
    Index idx cursor -> ppCursor top cursor <> PP.pretty ("[" ++ show idx ++ "]")
    Field idx cursor -> ppCursor top cursor <> PP.pretty ("." ++ show idx)

-- TODO(lb): Not sure why I have to specify the kind here?
data Selector arch (argTypes :: Ctx (FullType arch))
  = SelectArgument !(Some (Ctx.Index argTypes)) Cursor
  | SelectGlobal !L.Symbol Cursor
  deriving (Eq, Ord)

selectorCursor :: Simple Lens (Selector arch argTypes) Cursor
selectorCursor =
  lens
    (\case
      SelectArgument _ cursor -> cursor
      SelectGlobal _ cursor -> cursor)
    (\s v ->
      case s of
        SelectArgument arg _ -> SelectArgument arg v
        SelectGlobal glob _ -> SelectGlobal glob v)

data TypeSeekError ty
  = ArrayIndexOutOfBounds !Word64 !Word64 ty
  | FieldIndexOutOfBounds !Word64 !Word64 ty
  | MismatchedCursorAndType Cursor ty
  | UnsupportedType Cursor ty String

ppTypeSeekError :: Show ty => TypeSeekError ty -> Doc Void
ppTypeSeekError =
  \case
    ArrayIndexOutOfBounds index size ty ->
      PP.nest 2 $
        (PP.vsep [ PP.pretty "Out of bounds array index:"
                 , PP.pretty "Index:" <> PP.viaShow index
                 , PP.pretty "Array size:" <> PP.viaShow size
                 , PP.pretty "Type:" <> PP.viaShow ty
                 ])
    FieldIndexOutOfBounds index size ty ->
      PP.nest 2 $
        (PP.vsep [ PP.pretty "Nonexistent struct field:"
                 , PP.pretty "Index:" <> PP.viaShow index
                 , PP.pretty "Fields:" <> PP.viaShow size
                 , PP.pretty "Type:" <> PP.viaShow ty
                 ])
    MismatchedCursorAndType cursor ty ->
      PP.nest 2 $
        (PP.vsep [ PP.pretty "Mismatched cursor and type:"
                 , PP.pretty "Cursor:" <> ppCursor "<top>" cursor
                 , PP.pretty "Type:" <> PP.viaShow ty
                 ])
    UnsupportedType cursor ty msg ->
      PP.nest 2 $
        (PP.vsep [ PP.pretty "Unsupported type:"
                 , PP.pretty "Cursor:" <> ppCursor "<top>" cursor
                 , PP.pretty "Type:" <> PP.viaShow ty
                 , PP.pretty "Message:" <> PP.viaShow msg
                 ])

seekLlvmType :: Cursor -> L.Type -> Either (TypeSeekError L.Type) L.Type
seekLlvmType cursor llvmType =
  case (cursor, llvmType) of
    (Here, _) -> Right llvmType
    (Dereference cursor', L.PtrTo llvmType') -> seekLlvmType cursor' llvmType'
    (Index i cursor', L.Array size llvmType') ->
      if i >= size
      then Left (ArrayIndexOutOfBounds i size llvmType)
      else seekLlvmType cursor' llvmType'
    (Field i cursor', L.Struct fields) ->
      let len = fromIntegral $ length fields
      in
        if i >= len
        then Left (FieldIndexOutOfBounds i len llvmType)
        else seekLlvmType cursor' (fields !! fromIntegral i)
    _ -> Left (MismatchedCursorAndType cursor llvmType)

seekSymType ::
  (?lc :: TypeContext) =>
  Cursor ->
  SymType ->
  Either (TypeSeekError SymType) MemType
seekSymType cursor symType =
  case asMemType symType of
    Right memType -> seekMemType cursor memType
    Left message -> Left $ UnsupportedType cursor symType message

seekMemType ::
  (?lc :: TypeContext) =>
  Cursor ->
  MemType ->
  Either (TypeSeekError SymType) MemType
seekMemType cursor memType =
  case (cursor, memType) of
    (Here, _) -> Right memType
    (Dereference cursor', MemType.PtrType symType) -> seekSymType cursor' symType
    (Index i cursor', MemType.ArrayType size memType') ->
      let sz = fromIntegral size
      in
        if i >= sz
        then Left (ArrayIndexOutOfBounds i sz (MemType.MemType memType))
        else seekMemType cursor' memType'
    _ -> Left (MismatchedCursorAndType cursor (MemType.MemType memType))
