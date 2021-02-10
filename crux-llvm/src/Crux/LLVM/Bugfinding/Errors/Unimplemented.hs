{-
Module       : Crux.LLVM.Bugfinding.Errors.Unimplemented
Description  : Dealing with unimplemented features
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module Crux.LLVM.Bugfinding.Errors.Unimplemented
  ( unimplemented
  ) where

import Crux.LLVM.Bugfinding.Errors.Panic (HasCallStack, panic)

unimplemented ::
  HasCallStack =>
  String {- ^ Short name of where the error occured -} ->
  String {- ^ What's the not-yet supported thing? -} ->
  a
unimplemented where_ what =
  panic
    where_
    [ what
    , "is not yet implemented as a feature of crux-llvm bugfinding mode."
    , "If this feature would be useful to you, please report this error."
    ]
