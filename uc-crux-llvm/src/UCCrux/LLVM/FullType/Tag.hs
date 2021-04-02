{-
Module           : UCCrux.LLVM.FullType.Tag
Description      : A description of the outermost layer of a 'FullType'.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.Tag
  ( type FullTypeTag (..),
    FullTypeTagRepr (..),
    FullTypeToTag,
    checkTag,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Type.Equality ((:~:)(Refl))

import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr(..))
{- ORMOLU_ENABLE -}

-- | A description of the outermost layer of a 'FullType'.
--
-- Type level only.
data FullTypeTag
  = FTIntTag
  | FTPtrTag
  | FTFloatTag
  | FTArrayTag
  | FTStructTag
  | FTFuncPtrTag
  | FTOpaquePtrTag

type family FullTypeToTag (ft :: FullType m) :: FullTypeTag where
  FullTypeToTag (FTInt _) = FTIntTag
  FullTypeToTag (FTPtr _) = FTPtrTag
  FullTypeToTag (FTFloat _) = FTFloatTag
  FullTypeToTag (FTArray _ _) = FTArrayTag
  FullTypeToTag (FTStruct _) = FTStructTag
  FullTypeToTag (FTFuncPtr _ _ _) = FTFuncPtrTag
  FullTypeToTag FTOpaquePtr = FTOpaquePtrTag

data FullTypeTagRepr (ftt :: FullTypeTag) where
  FTIntTagRepr :: FullTypeTagRepr FTIntTag
  FTPtrTagRepr :: FullTypeTagRepr FTPtrTag
  FTFloatTagRepr :: FullTypeTagRepr FTFloatTag
  FTArrayTagRepr :: FullTypeTagRepr FTArrayTag
  FTStructTagRepr :: FullTypeTagRepr FTStructTag
  FTFuncPtrTagRepr :: FullTypeTagRepr FTFuncPtrTag
  FTOpaquePtrTagRepr :: FullTypeTagRepr FTOpaquePtrTag

checkTag :: FullTypeTagRepr ftt -> FullTypeRepr m ft -> Maybe (FullTypeToTag ft :~: ftt)
checkTag fttRepr ftRepr =
  case (fttRepr, ftRepr) of
    (FTIntTagRepr, FTIntRepr {}) -> Just Refl
    (FTPtrTagRepr, FTPtrRepr {}) -> Just Refl
    (FTFloatTagRepr, FTFloatRepr {}) -> Just Refl
    (FTArrayTagRepr, FTArrayRepr {}) -> Just Refl
    (FTStructTagRepr, FTStructRepr {}) -> Just Refl
    (FTFuncPtrTagRepr, FTVoidFuncPtrRepr {}) -> Just Refl
    (FTFuncPtrTagRepr, FTNonVoidFuncPtrRepr {}) -> Just Refl
    (FTOpaquePtrTagRepr, FTOpaquePtrRepr {}) -> Just Refl
    _ -> Nothing
