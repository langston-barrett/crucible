{-# LANGUAGE RankNTypes #-}
{- |
Module           : Lang.Crucible.CFG.Util
Description      : Utility operations on CFGs
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>
-}

{-# LANGUAGE GADTs #-}

module Lang.Crucible.CFG.Util where

import           Data.Functor.Identity
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Lang.Crucible.CFG.Core
-- import           Data.Parameterized.Context.Unsafe
import           Data.Parameterized.Context

-- | Drop the type-level information in an 'Assignment'
assignToList :: Assignment f ctx -> [Some f]
assignToList = runIdentity . traverseAndCollect (\_idx f -> Identity [Some f])

-- | Get the block map of a CFG, throwing away typing information
getBlockMap :: CFG ext blocks init ret -> [Some (Block ext blocks ret)]
getBlockMap cfg =
  assignToList (cfgBlockMap cfg)
