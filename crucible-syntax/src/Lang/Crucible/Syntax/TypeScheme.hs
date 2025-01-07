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
  , Inst
  , Inst'(..)
  , emptyInst
  , fullInst
  , TypeError(..)
  , match
  , instantiate
  ) where

import Control.Lens qualified as Lens
import Control.Monad qualified as Monad
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Kind (Type)
import Data.Parameterized.Classes (ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.Some (viewSome)
import Data.Parameterized.TraversableFC (traverseFC, toListFC)
import Lang.Crucible.Types
import Prettyprinter qualified as PP

-- | Data-kind for kinds of 'TypeScheme's
data Kind
  = KString
  | KType
  | KArrow Kind Kind

data TypeScheme :: Ctx.Ctx Kind -> Kind -> Type where
  SUnit :: TypeScheme ks KType
  SBool :: TypeScheme ks KType
  SNat :: TypeScheme ks KType
  SApp ::
    TypeScheme ks (KArrow ki kr) ->
    TypeScheme ks ki ->
    TypeScheme ks kr
  SVar :: Ctx.Index ks k -> TypeScheme ks k
  SString :: TypeScheme ks (KArrow KString KType)
  SStringInfo :: StringInfoRepr si -> TypeScheme ks KString
  SVec :: TypeScheme ks (KArrow KType KType)
  SArrow :: [TypeScheme ks KType] -> TypeScheme ks KType -> TypeScheme ks KType

instance PP.Pretty (TypeScheme ks k) where
  pretty =
    \case
      SUnit -> PP.pretty "Unit"
      SBool -> PP.pretty "Bool"
      SNat -> PP.pretty "Nat"
      SApp i r -> PP.pretty i PP.<+> PP.pretty r
      SString -> PP.pretty "String"
      SStringInfo si -> PP.viaShow si
      SVec -> PP.pretty "Vec"
      SVar idx -> PP.pretty "x" PP.<> PP.viaShow (Ctx.indexVal idx)
      SArrow args ret ->
        PP.fillSep (PP.punctuate (PP.pretty "->") (map PP.pretty (args ++ [ret])))

instance Show (TypeScheme ks k) where
  show = show . PP.pretty

type family Inst (k :: Kind) :: Type where
  Inst KString = Some StringInfoRepr
  Inst KType = Some TypeRepr
  Inst (KArrow ki kr) = Inst ki -> Inst kr

newtype Inst' k = Inst' (Inst k)

emptyInst :: Ctx.Size ks -> Ctx.Assignment (Compose Maybe Inst') ks
emptyInst sz = Ctx.generate sz (\_ -> Compose Nothing)

fullInst :: Ctx.Assignment (Compose Maybe Inst') ks -> Maybe (Ctx.Assignment Inst' ks)
fullInst = traverseFC getCompose

data TypeError ks
  = TypeError
    { typeErrorExpected :: TypeScheme ks KType
    , typeErrorFound :: Some TypeRepr
    }

instance PP.Pretty (TypeError ks) where
  pretty err =
    PP.vcat
    [ PP.pretty "Type error!"
    , PP.pretty "Expected:" PP.<+> PP.pretty (typeErrorExpected err)
    , PP.pretty "Found:" PP.<+> viewSome PP.viaShow (typeErrorFound err)
    ]

instance Show (TypeError ks) where
  show = show . PP.pretty

_matchApp ::
  TypeScheme ks (KArrow KType KType) ->
  Some TypeRepr ->
  Ctx.Assignment (Compose Maybe Inst') ks ->
  Ctx.Assignment (Compose Maybe Inst') ks
_matchApp scheme repr insts =
  case (scheme, repr) of
    (SVar idx, Some (VectorRepr {})) ->
      let f (Some tpr) = Some (VectorRepr tpr) in
      Lens.set (ixF' idx) (Compose (Just (Inst' f))) insts
    _ -> insts

match ::
  TypeScheme ks KType ->
  Some TypeRepr ->
  Ctx.Assignment (Compose Maybe Inst') ks ->
  Either (TypeError ks) (Ctx.Assignment (Compose Maybe Inst') ks)
match scheme repr insts = do
  case (scheme, repr) of
    (SVar idx, _) ->
      Right (Lens.set (ixF' idx) (Compose (Just (Inst' repr))) insts)
    (SApp SVec s, Some (VectorRepr r)) ->
      match s (Some r) insts
    (SApp SVec _, _) -> Left (TypeError scheme repr)
    (SApp SString (SStringInfo si), Some (StringRepr si')) ->
      case testEquality si si' of
        Just Refl -> Right insts
        Nothing -> Left (TypeError scheme repr)
    (SApp SString _, _) -> Left (TypeError scheme repr)
    (SApp (SVar {}) _, _) -> Left (TypeError scheme repr)
    (SApp (SApp {}) _, _) -> Left (TypeError scheme repr)
    (SUnit, Some UnitRepr) -> Right insts
    (SUnit, _) -> Left (TypeError scheme repr)
    (SNat, Some NatRepr) -> Right insts
    (SNat, _) -> Left (TypeError scheme repr)
    (SBool, Some BoolRepr) -> Right insts
    (SBool, _) -> Left (TypeError scheme repr)
    (SArrow sargs sret, Some (FunctionHandleRepr targs tret)) ->
      let targs' = toListFC Some targs in
      if length sargs /= length targs'
      then Left (TypeError scheme repr)
      else do
        insts' <- Monad.foldM (\is (s, t) -> match s t is) insts (zip sargs targs')
        match sret (Some tret) insts'
    (SArrow {}, _) -> Left (TypeError scheme repr)

instantiate ::
  forall ks k.
  Ctx.Assignment (Compose Maybe Inst') ks ->
  TypeScheme ks k ->
  Maybe (Inst k)
instantiate insts =
  \case
    SVar idx -> do
      Inst' f <- getCompose (Lens.view (ixF' idx) insts)
      Just f
    SString -> Just (\(Some si) -> Some (StringRepr si))
    SVec -> Just (\(Some t) -> Some (VectorRepr t))
    SStringInfo si -> Just (Some si)
    SUnit -> Just (Some UnitRepr)
    SBool -> Just (Some BoolRepr)
    SNat -> Just (Some NatRepr)
    SApp con arg -> do
      con' <- instantiate insts con
      arg' <- instantiate insts arg
      Just (con' arg')
    SArrow params ret ->  do
      params' <- traverse (instantiate insts) params
      Some ret' <- instantiate insts ret
      Some params'' <- Just (Ctx.fromList params')
      Just (Some (FunctionHandleRepr params'' ret'))
