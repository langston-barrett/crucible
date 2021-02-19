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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Crux.LLVM.Bugfinding.Cursor
  ( Cursor(..)
  , SomeCursor
  , ppCursor

  -- * Operations on 'Cursor'
  , findBottom
  , deepenPtr
  , deepenStruct
  , TypeSeekError(..)
  , ppTypeSeekError
  , seekLlvmType
  , seekMemType

  -- * 'Selector'
  , Selector(..)
  , SomeSelector(..)
  , SomeInSelector(..)
  , selectorCursor
  ) where

import           Control.Lens (Lens, lens)
import           Data.Semigroupoid (Semigroupoid(o))
import           Data.Word (Word64)
import           Data.Void (Void)
import           Data.Type.Equality
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (OrdF(compareF))
import           Data.Parameterized.NatRepr (NatRepr, type (<=), natValue)
import qualified Data.Parameterized.TH.GADT as U

import           Lang.Crucible.LLVM.MemType (MemType, SymType)
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Bugfinding.FullType (FullType(..), FullTypeRepr(..))
import           Crux.LLVM.Bugfinding.FullType.ModuleTypes (ModuleTypes)
import           Crux.LLVM.Bugfinding.FullType.MemType (asFullType)

data Cursor m (inTy :: FullType m) (atTy :: FullType m) where
  Here :: FullTypeRepr m atTy -> Cursor m atTy atTy
  Dereference :: Cursor m inTy atTy -> Cursor m ('FTPtr inTy) atTy
  Index ::
    (i <= n) => -- TODO should be <
    NatRepr i ->
    NatRepr n ->
    Cursor m inTy atTy ->
    Cursor m ('FTArray n inTy) atTy
  Field ::
    Ctx.Assignment (FullTypeRepr m) fields ->
    Ctx.Index fields inTy ->
    Cursor m inTy atTy ->
    Cursor m ('FTStruct fields) atTy

instance Semigroupoid (Cursor m) where
  o cursor1 cursor2 =
    case (cursor1, cursor2) of
      (Here _, _) -> cursor2
      (_, Here _) -> cursor1
      (_, Field ftReprs idx cursor3) -> Field ftReprs idx (o cursor1 cursor3)
      (_, Index i n cursor3) -> Index i n (o cursor1 cursor3)
      (_, Dereference cursor3) -> Dereference (o cursor1 cursor3)

findBottom :: Cursor m inTy atTy -> FullTypeRepr m atTy
findBottom =
  \case
    Here repr -> repr
    Dereference cursor' -> findBottom cursor'
    Index _ _ cursor' -> findBottom cursor'
    Field _ _ cursor' -> findBottom cursor'

deepenPtr ::
  ModuleTypes m ->
  Cursor m inTy ('FTPtr atTy) ->
  Cursor m inTy atTy
deepenPtr mts =
  \case
    Here (FTPtrRepr ptRepr) -> Dereference (Here (asFullType mts ptRepr))
    Dereference cursor -> Dereference (deepenPtr mts cursor)
    Index i n cursor -> Index i n (deepenPtr mts cursor)
    Field fields idx cursor -> Field fields idx (deepenPtr mts cursor)

deepenStruct ::
  Ctx.Index fields atTy ->
  Cursor m inTy ('FTStruct fields) ->
  Cursor m inTy atTy
deepenStruct idx =
  \case
    Here (FTStructRepr _structInfo fields) ->
      Field fields idx (Here (fields Ctx.! idx))
    Dereference cursor -> Dereference (deepenStruct idx cursor)
    Index i n cursor -> Index i n (deepenStruct idx cursor)
    Field fields idx' cursor -> Field fields idx' (deepenStruct idx cursor)

data SomeCursor = forall m inTy atTy. SomeCursor (Cursor m inTy atTy)

-- TODO: Use more type information?
ppCursor ::
  String {-^ Top level, e.g. the name of a variable -} ->
  Cursor m inTy atTy ->
  Doc Void
ppCursor top =
  \case
    Here _ft -> PP.pretty top
    Dereference (Field _fieldTypes idx cursor) ->
      ppCursor top cursor <> PP.pretty "->" <> PP.pretty (show idx)
    Dereference what -> PP.pretty "*" <> ppCursor top what
    Index idx _len cursor -> ppCursor top cursor <> PP.pretty ("[" ++ show idx ++ "]")
    Field _fieldTypes idx cursor ->
      ppCursor top cursor <> PP.pretty ("." ++ show idx)

-- TODO(lb): Not sure why I have to specify the kind here?
data Selector m (argTypes :: Ctx (FullType m)) inTy atTy
  = SelectArgument !(Ctx.Index argTypes inTy) (Cursor m inTy atTy)
  | SelectGlobal !L.Symbol (Cursor m inTy atTy)
  -- TODO
  -- deriving (Eq, Ord)

data SomeSelector m argTypes
  = forall inTy atTy. SomeSelector (Selector m argTypes inTy atTy)

data SomeInSelector m argTypes atTy
  = forall inTy. SomeInSelector (Selector m argTypes inTy atTy)

selectorCursor ::
  Lens
    (Selector m argTypes inTy atTy)
    (Selector m argTypes inTy atTy')
    (Cursor m inTy atTy)
    (Cursor m inTy atTy')
selectorCursor =
  lens
    (\case
      SelectArgument _ cursor -> cursor
      SelectGlobal _ cursor -> cursor)
    (\s v ->
      case s of
        SelectArgument arg _ -> SelectArgument arg v
        SelectGlobal glob _ -> SelectGlobal glob v)

data TypeSeekError ty
  = ArrayIndexOutOfBounds !Word64 !Word64 ty
  | FieldIndexOutOfBounds !Word64 !Word64 ty
  | MismatchedCursorAndType SomeCursor ty
  | UnsupportedType SomeCursor ty String

ppTypeSeekError :: Show ty => TypeSeekError ty -> Doc Void
ppTypeSeekError =
  \case
    ArrayIndexOutOfBounds index size ty ->
      PP.nest 2 $
        PP.vsep [ PP.pretty "Out of bounds array index:"
                , PP.pretty "Index:" <> PP.viaShow index
                , PP.pretty "Array size:" <> PP.viaShow size
                , PP.pretty "Type:" <> PP.viaShow ty
                ]
    FieldIndexOutOfBounds index size ty ->
      PP.nest 2 $
        PP.vsep [ PP.pretty "Nonexistent struct field:"
                , PP.pretty "Index:" <> PP.viaShow index
                , PP.pretty "Fields:" <> PP.viaShow size
                , PP.pretty "Type:" <> PP.viaShow ty
                ]
    MismatchedCursorAndType (SomeCursor cursor) ty ->
      PP.nest 2 $
        PP.vsep [ PP.pretty "Mismatched cursor and type:"
                , PP.pretty "Cursor:" <> ppCursor "<top>" cursor
                , PP.pretty "Type:" <> PP.viaShow ty
                ]
    UnsupportedType (SomeCursor cursor) ty msg ->
      PP.nest 2 $
        PP.vsep [ PP.pretty "Unsupported type:"
                , PP.pretty "Cursor:" <> ppCursor "<top>" cursor
                , PP.pretty "Type:" <> PP.viaShow ty
                , PP.pretty "Message:" <> PP.viaShow msg
                ]

seekLlvmType :: Cursor m inTy atTy -> L.Type -> Either (TypeSeekError L.Type) L.Type
seekLlvmType cursor llvmType =
  case (cursor, llvmType) of
    (Here _ft, _) -> Right llvmType
    (Dereference cursor', L.PtrTo llvmType') -> seekLlvmType cursor' llvmType'
    (Index i _len cursor', L.Array size llvmType') ->
      let indexVal = fromIntegral (natValue i)
      in if indexVal >= size
         then Left (ArrayIndexOutOfBounds indexVal size llvmType)
         else seekLlvmType cursor' llvmType'
    (Field _fieldTypes i cursor', L.Struct fields) ->
      let len = fromIntegral (length fields)
          indexVal = fromIntegral (Ctx.indexVal i)
      in
        if indexVal >= len
        then Left (FieldIndexOutOfBounds indexVal len llvmType)
        else seekLlvmType cursor' (fields !! fromIntegral indexVal)
    _ -> Left (MismatchedCursorAndType (SomeCursor cursor) llvmType)

seekSymType ::
  (?lc :: TypeContext) =>
  Cursor m inTy atTy ->
  SymType ->
  Either (TypeSeekError SymType) MemType
seekSymType cursor symType =
  case asMemType symType of
    Right memType -> seekMemType cursor memType
    Left message -> Left $ UnsupportedType (SomeCursor cursor) symType message

seekMemType ::
  (?lc :: TypeContext) =>
  Cursor m inTy atTy->
  MemType ->
  Either (TypeSeekError SymType) MemType
seekMemType cursor memType =
  case (cursor, memType) of
    (Here _ft, _) -> Right memType
    (Dereference cursor', MemType.PtrType symType) -> seekSymType cursor' symType
    (Index i _len cursor', MemType.ArrayType size memType') ->
      let sz = fromIntegral size
          indexVal = fromIntegral (natValue i)
      in
        if indexVal >= sz
        then Left (ArrayIndexOutOfBounds indexVal sz (MemType.MemType memType))
        else seekMemType cursor' memType'
    _ -> Left (MismatchedCursorAndType (SomeCursor cursor) (MemType.MemType memType))

-- TODO split modules
$(return [])

instance TestEquality (Cursor m inTy) where
  testEquality =
    $(U.structuralTypeEquality [t|Cursor|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (Cursor m inTy) where
  compareF =
    $(U.structuralTypeOrd [t|Cursor|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))

instance TestEquality (Selector m argTypes inTy) where
  testEquality =
    $(U.structuralTypeEquality [t|Selector|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (Selector m argTypes inTy) where
  compareF =
    $(U.structuralTypeOrd [t|Selector|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (appAny (U.ConType [t|Cursor|])))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))
