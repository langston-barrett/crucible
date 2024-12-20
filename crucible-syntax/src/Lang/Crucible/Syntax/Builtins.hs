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
  ( AST
  , E(..)
  , SomeExpr(..)
  , evalSomeExpr
  , evalOverloaded
  , Builtin(..)
  , SomeBuiltin(..)
  , builtins
  ) where

import Control.Applicative (empty)
import Data.BitVector.Sized qualified as BV
import Data.Functor.Const (Const (..))
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.List qualified as PList
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.TraversableFC (toListFC)
import Data.Text qualified as T
import Data.Type.Equality ((:~:)(..), testEquality)
import Lang.Crucible.CFG.Core (ReferenceType)
import Lang.Crucible.CFG.Expr (App(..))
import Lang.Crucible.CFG.Generator (Atom)
import Lang.Crucible.CFG.Reg (Reg, GlobalVar)
import Lang.Crucible.Syntax.Atoms (Keyword (..), Atomic (..))
import Lang.Crucible.Syntax.Monad (MonadSyntax, later, describe, withFocus)
import Lang.Crucible.Syntax.SExpr (Syntax)
import Lang.Crucible.Syntax.TypeScheme
import Lang.Crucible.Types (TypeRepr(..))
import Prettyprinter qualified as PP
import What4.ProgramLoc (Position)

type AST s = Syntax Atomic

data E ext s t where
  EAtom  :: !(Atom s t) -> E ext s t
  EReg   :: !Position -> !(Reg s t) -> E ext s t
  EGlob  :: !Position -> !(GlobalVar t) -> E ext s t
  EDeref :: !Position -> !(E ext s (ReferenceType t)) -> E ext s t
  EApp   :: !(App ext (E ext s) t) -> E ext s t

data SomeExpr ext s where
  SomeE :: TypeRepr t -> E ext s t -> SomeExpr ext s
  SomeOverloaded :: AST s -> Keyword -> [SomeExpr ext s] -> SomeExpr ext s
  SomeIntLiteral :: AST s -> Integer -> SomeExpr ext s

evalIntLiteral :: MonadSyntax Atomic m => AST s -> TypeRepr tpr -> Integer -> m (E ext s tpr)
evalIntLiteral _ NatRepr i | i >= 0 = return $ EApp $ NatLit (fromInteger i)
evalIntLiteral _ IntegerRepr i = return $ EApp $ IntLit i
evalIntLiteral _ RealValRepr i = return $ EApp $ RationalLit (fromInteger i)
evalIntLiteral ast tpr _i =
  withFocus ast $ later $ describe ("literal " <> T.pack (show tpr) <> " value") empty


evalOverloaded :: forall m s t ext. MonadSyntax Atomic m => AST s -> TypeRepr t -> Keyword -> [SomeExpr ext s] -> m (E ext s t)
evalOverloaded ast tpr k = withFocus ast .
  case (k, tpr) of
    (Plus, NatRepr)     -> nary NatAdd    (NatLit 0)
    (Plus, IntegerRepr) -> nary IntAdd    (IntLit 0)
    (Plus, RealValRepr) -> nary RealAdd   (RationalLit 0)
    (Plus, BVRepr w)    -> nary (BVAdd w) (BVLit w (BV.zero w))

    (Times, NatRepr)     -> nary NatMul    (NatLit 1)
    (Times, IntegerRepr) -> nary IntMul    (IntLit 1)
    (Times, RealValRepr) -> nary RealMul   (RationalLit 1)
    (Times, BVRepr w)    -> nary (BVMul w) (BVLit w (BV.one w))

    (Minus, NatRepr)     -> bin NatSub
    (Minus, IntegerRepr) -> bin IntSub
    (Minus, RealValRepr) -> bin RealSub
    (Minus, BVRepr w)    -> bin (BVSub w)

    (Div, NatRepr)       -> bin NatDiv
    (Div, IntegerRepr)   -> bin IntDiv
    (Div, RealValRepr)   -> bin RealDiv
    (Div, BVRepr w)      -> bin (BVUdiv w)

    (Mod, NatRepr)       -> bin NatMod
    (Mod, IntegerRepr)   -> bin IntMod
    (Mod, RealValRepr)   -> bin RealMod
    (Mod, BVRepr w)      -> bin (BVUrem w)

    (Negate, IntegerRepr) -> u IntNeg
    (Negate, RealValRepr) -> u RealNeg
    (Negate, BVRepr w)    -> u (BVNeg w)

    (Abs, IntegerRepr)   -> u IntAbs

    _ -> \_ -> later $ describe ("operation at type " <> T.pack (show tpr)) $ empty
 where
 u :: (E ext s t -> App ext (E ext s) t) -> [SomeExpr ext s] -> m (E ext s t)
 u f [x] = EApp . f <$> evalSomeExpr tpr x
 u _ _ = later $ describe "one argument" $ empty

 bin :: (E ext s t -> E ext s t -> App ext (E ext s) t) -> [SomeExpr ext s] -> m (E ext s t)
 bin f [x,y] = EApp <$> (f <$> evalSomeExpr tpr x <*> evalSomeExpr tpr y)
 bin _ _ = later $ describe "two arguments" $ empty

 nary :: (E ext s t -> E ext s t -> App ext (E ext s) t) -> App ext (E ext s) t -> [SomeExpr ext s] -> m (E ext s t)
 nary _ z []     = return $ EApp z
 nary _ _ [x]    = evalSomeExpr tpr x
 nary f _ (x:xs) = go f <$> evalSomeExpr tpr x <*> mapM (evalSomeExpr tpr) xs

 go f x (y:ys) = go f (EApp $ f x y) ys
 go _ x []     = x

evalSomeExpr :: MonadSyntax Atomic m => TypeRepr t -> SomeExpr ext s -> m (E ext s t)
evalSomeExpr tpr (SomeE tpr' e)
  | Just Refl <- testEquality tpr tpr' = return e
  | otherwise = later $ describe ("matching types (" <> T.pack (show tpr)
                                  <> " /= " <> T.pack (show tpr') <> ")") empty
evalSomeExpr tpr (SomeOverloaded ast k args) = evalOverloaded ast tpr k args
evalSomeExpr tpr (SomeIntLiteral ast i) = evalIntLiteral ast tpr i

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
  ]
