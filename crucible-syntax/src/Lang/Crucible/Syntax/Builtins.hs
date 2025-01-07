{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.Syntax.Builtins
  ( Builtin(..)
  , SomeBuiltin(..)
  , builtins
  ) where

import Data.Functor.Const (Const (..))
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.List qualified as PList
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.TraversableFC (toListFC)
import Lang.Crucible.CFG.Expr (App(..))
import Lang.Crucible.Syntax.Atoms (Keyword (..), Atomic (..))
import Lang.Crucible.Syntax.Expr
import Lang.Crucible.Syntax.Monad (MonadSyntax)
import Lang.Crucible.Syntax.TypeScheme
import Lang.Crucible.Types (TypeRepr(..))
import Prettyprinter qualified as PP

data Builtin ks args
  = Builtin
    { builtinKw :: Keyword
    , builtinTVars :: Ctx.Size ks
    , builtinArgs :: PList.List (Const (TypeScheme ks KType)) args
    , builtinRet :: TypeScheme ks KType
    , builtinSemantics ::
        forall m s ext.
        MonadSyntax Atomic m =>
        Ctx.Assignment Inst' ks ->
        PList.List (Const (SomeExpr ext s)) args ->
        m (SomeExpr ext s)
    }

instance PP.Pretty (Builtin ks args) where
  pretty builtin =
    PP.fillSep
    [ PP.viaShow (builtinKw builtin)
    , ":"
    , PP.pretty
      (SArrow (toListFC getConst (builtinArgs builtin)) (builtinRet builtin))
    ]

data SomeBuiltin = forall ks args. SomeBuiltin (Builtin ks args)

builtins :: [SomeBuiltin]
builtins =
  [ SomeBuiltin $
    Builtin
    { builtinKw = Not_
    , builtinTVars = Ctx.zeroSize
    , builtinArgs = Const SBool PList.:< PList.Nil
    , builtinRet = SBool
    , builtinSemantics =
      \Ctx.Empty (Const b PList.:< PList.Nil) ->
        SomeE BoolRepr . EApp . Not <$> evalSomeExpr BoolRepr b
    }
  , SomeBuiltin $
    Builtin
    { builtinKw = StringConcat_
    , builtinTVars = Ctx.size1
    , builtinArgs =
      Const (SApp SString (SVar Ctx.baseIndex)) PList.:<
      Const (SApp SString (SVar Ctx.baseIndex)) PList.:<
      PList.Nil
    , builtinRet = SApp SString (SVar Ctx.baseIndex)
    , builtinSemantics =
      \(Ctx.Empty Ctx.:> Inst' (Some si))
       (Const e1 PList.:< Const e2 PList.:< PList.Nil) ->
       SomeE (StringRepr si) . EApp <$>
         (StringConcat si <$>
          evalSomeExpr (StringRepr si) e1 <*>
          evalSomeExpr (StringRepr si) e2)
    }
  , SomeBuiltin $
    Builtin
    { builtinKw = VectorCons_
    , builtinTVars = Ctx.size1
    , builtinArgs =
      Const (SVar Ctx.baseIndex) PList.:<
      Const (SApp SVec (SVar Ctx.baseIndex)) PList.:<
      PList.Nil
    , builtinRet = SApp SVec (SVar Ctx.baseIndex)
    , builtinSemantics =
      \(Ctx.Empty Ctx.:> Inst' (Some t))
       (Const a PList.:< Const v PList.:< PList.Nil) ->
       SomeE (VectorRepr t) . EApp <$>
        (VectorCons t <$> evalSomeExpr t a <*> evalSomeExpr (VectorRepr t) v)
    }
  , SomeBuiltin $
    Builtin
    { builtinKw = VectorGetEntry_
    , builtinTVars = Ctx.size1
    , builtinArgs =
      Const (SApp SVec (SVar Ctx.baseIndex)) PList.:<
      Const SNat  PList.:<
      PList.Nil
    , builtinRet = SVar Ctx.baseIndex
    , builtinSemantics =
      \(Ctx.Empty Ctx.:> Inst' (Some t))
       (Const v PList.:< Const n PList.:< PList.Nil) ->
       SomeE t . EApp <$>
         (VectorGetEntry t <$> evalSomeExpr (VectorRepr t) v <*> evalSomeExpr NatRepr n)
    }
  , SomeBuiltin $
    Builtin
    { builtinKw = VectorIsEmpty_
    , builtinTVars = Ctx.size1
    , builtinArgs =
      Const (SApp SVec (SVar Ctx.baseIndex)) PList.:< PList.Nil
    , builtinRet = SBool
    , builtinSemantics =
      \(Ctx.Empty Ctx.:> Inst' (Some t))
       (Const v PList.:< PList.Nil) ->
        SomeE BoolRepr . EApp . VectorIsEmpty <$> evalSomeExpr (VectorRepr t) v
    }
  , SomeBuiltin $
    Builtin
    { builtinKw = VectorSize_
    , builtinTVars = Ctx.size1
    , builtinArgs =
      Const (SApp SVec (SVar Ctx.baseIndex)) PList.:< PList.Nil
    , builtinRet = SNat
    , builtinSemantics =
      \(Ctx.Empty Ctx.:> Inst' (Some t))
       (Const v PList.:< PList.Nil) ->
        SomeE NatRepr . EApp . VectorSize <$> evalSomeExpr (VectorRepr t) v
    }
  ]
