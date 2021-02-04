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

module Crux.LLVM.Bugfinding.Cursor
  ( Cursor(..)
  , TypeSeekError(..)
  , seekType
  ) where

import           Data.Word (Word64)

import qualified Text.LLVM.AST as L

data Cursor
  = Here
  | Dereference Cursor
  | Index !Word64 Cursor
  | Field !Word64 Cursor

data TypeSeekError
  = ArrayIndexOutOfBounds !Word64 !Word64 L.Type
  | FieldIndexOutOfBounds !Word64 !Word64 L.Type
  | MismatchedCursorAndType Cursor L.Type

seekType :: Cursor -> L.Type -> Either TypeSeekError L.Type
seekType cursor type_ =
  case (cursor, type_) of
    (Here, _) -> Right type_
    (Dereference cursor', L.PtrTo type') -> seekType cursor' type'
    (Index i cursor', L.Array size type') ->
      if i >= size
      then Left (ArrayIndexOutOfBounds i size type_)
      else seekType cursor' type'
    (Field i cursor', L.Struct fields) ->
      let len = fromIntegral $ length fields
      in
        if i >= len
        then Left (FieldIndexOutOfBounds i len type_)
        else seekType cursor' (fields !! fromIntegral i)
    _ -> Left (MismatchedCursorAndType cursor type_)
