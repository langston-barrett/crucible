{-
Module       : Crux.LLVM.Bugfinding.Errors.Unimplemented
Description  : Dealing with unimplemented features
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}

module Crux.LLVM.Bugfinding.Errors.Unimplemented
  ( unimplemented
  , catchUnimplemented
  ) where

import Control.Exception (try)
import Panic hiding (panic)
import qualified Panic

data Unimplemented = Unimplemented

instance PanicComponent Unimplemented where

  panicComponentName _ = "crux-llvm bugfinding mode"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# NOINLINE panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

unimplemented ::
  HasCallStack =>
  String {- ^ Short name of where the error occured -} ->
  String {- ^ What's the not-yet supported thing? -} ->
  a
unimplemented where_ what =
  Panic.panic
    Unimplemented
    where_
    [ what
    , "is not yet implemented as a feature of crux-llvm bugfinding mode."
    , "If this feature would be useful to you, please report this error."
    ]

catchUnimplemented :: forall a. IO a -> IO (Either String a)
catchUnimplemented computation =
  either
    (\panic@(Panic Unimplemented _ _ _) -> Left (show panic))
    pure
    <$> try computation
