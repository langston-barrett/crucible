{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.Syntax.TypeScheme
  ( Kind(..)
  , TypeScheme(..)
  , Instantiation
  , emptyInst
  , match
  , instantiate
  ) where

import Data.Parameterized.Context qualified as Ctx
import Lang.Crucible.Types
import Data.Kind (Type)
import Data.Parameterized (Some(Some))
import Control.Lens qualified as Lens
import Data.Parameterized.Classes (ixF')

data Kind
  = KType
  | KArrow Kind Kind

data TypeScheme :: Ctx.Ctx Kind -> Kind -> Type where
  SUnit :: TypeScheme ks KType
  SApp ::
    TypeScheme ks (KArrow ki kr) ->
    TypeScheme ks ki ->
    TypeScheme ks kr
  SVar :: Ctx.Index ks k -> TypeScheme ks k
  SVec :: TypeScheme ks (KArrow KType KType)
  -- SArrow :: TypeScheme ks (KArrow KType (KArrow KType KType))
  SArrow :: [TypeScheme ks KType] -> TypeScheme ks KType -> TypeScheme ks KType

-- ex :: TypeScheme Ctx.EmptyCtx KType
-- ex = SApp (SApp SArrow SUnit) SUnit

type family Inst (k :: Kind) :: Type where
  Inst KType = Some TypeRepr
  Inst (KArrow ki kr) = Inst ki -> Inst kr

data Instantiation k where
  Inst :: Maybe (Inst k) -> Instantiation k

emptyInst :: Ctx.Size ks -> Ctx.Assignment Instantiation ks
emptyInst sz = Ctx.generate sz (\_ -> Inst Nothing)

_matchApp ::
  TypeScheme ks (KArrow KType KType) ->
  Some TypeRepr ->
  Ctx.Assignment Instantiation ks ->
  Ctx.Assignment Instantiation ks
_matchApp scheme repr insts =
  case (scheme, repr) of
    (SVar idx, Some (VectorRepr {})) ->
      let f (Some tpr) = Some (VectorRepr tpr) in
      Lens.set (ixF' idx) (Inst (Just f)) insts
    _ -> insts

match ::
  TypeScheme ks KType ->
  Some TypeRepr ->
  Ctx.Assignment Instantiation ks ->
  Ctx.Assignment Instantiation ks
match scheme repr insts =
  case (scheme, repr) of
    (SVar idx, _) -> Lens.set (ixF' idx) (Inst (Just repr)) insts
    (SApp SVec s, Some (VectorRepr r)) -> match s (Some r) insts
    _ -> insts

instantiate ::
  forall ks k.
  Ctx.Assignment Instantiation ks ->
  TypeScheme ks k ->
  Maybe (Inst k)
instantiate insts =
  \case
    SVar idx -> do
      Inst f <- Just (Lens.view (ixF' idx) insts)
      f
    SVec -> Just (\(Some t) -> Some (VectorRepr t))
    SUnit -> Just (Some UnitRepr)
    SApp con arg -> do
      con' <- instantiate insts con
      arg' <- instantiate insts arg
      Just (con' arg')
    SArrow params ret ->  do
      params' <- traverse (instantiate insts) params
      Some ret' <- instantiate insts ret
      Some params'' <- Just (Ctx.fromList params')
      Just (Some (FunctionHandleRepr params'' ret'))
