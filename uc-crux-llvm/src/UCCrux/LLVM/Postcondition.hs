{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-
Module       : UCCrux.LLVM.Postcondition
Description  : Postconditions for LLVM functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Postcondition
  ( ClobberPtr(..)
  , Postcondition
  , emptyPostcondition
  )
where

import           Data.Map (Map)
import qualified Data.Map as Map

import           Data.Parameterized.Context (Ctx)
import qualified Data.Parameterized.Context as Ctx

import           UCCrux.LLVM.Constraints (ConstrainedShape, ConstrainedTypedValue)
import           UCCrux.LLVM.Cursor (Cursor)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr)
import           UCCrux.LLVM.Module (GlobalSymbol)

data ClobberGlobal m (inTy :: FullType m) = forall inTy atTy. ClobberGlobal
  { clobberGlobalCursor :: Cursor m inTy atTy,
    clobberGlobalValue :: ConstrainedShape m inTy,
    clobberGlobalType :: FullTypeRepr m inTy
  }

data ClobberPtr m (ft :: FullType m) where
  NoClobber :: ClobberPtr m ft
  ClobberPtr ::
    ConstrainedShape m ('FTPtr inTy) ->
    Cursor m ('FTPtr inTy) atTy ->
    ClobberPtr m ('FTPtr inTy)

-- | Postcondition of an LLVM function.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data Postcondition m (argTypes :: Ctx (FullType m)) = Postcondition
  { _argClobbers :: Ctx.Assignment (ClobberPtr m) argTypes,
    _globalClobbers :: Map (GlobalSymbol m) (ConstrainedTypedValue m),
    _returnValue :: Maybe (ConstrainedTypedValue m)
  }

emptyPostcondition :: Ctx.Size argTypes -> Postcondition m argTypes
emptyPostcondition sz =
  Postcondition
    { _argClobbers = Ctx.replicate sz NoClobber,
      _globalClobbers = Map.empty,
      _returnValue = Nothing
    }
