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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Crux.LLVM.Bugfinding.Cursor
  ( Cursor(..)
  , SomeCursor
  , ppCursor
  , Selector(..)
  , selectorCursor
  , TypeSeekError(..)
  , ppTypeSeekError
  , seekLlvmType
  , seekMemType
  ) where

import           Control.Lens (Simple, Lens, lens)
import           Data.Type.Equality (TestEquality(testEquality))
import           Data.Word (Word64)
import           Data.Void (Void)
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (OrdF(compareF))
import           Data.Parameterized.NatRepr (NatRepr, type (<=), natValue)
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U

import           Lang.Crucible.LLVM.MemType (MemType, SymType)
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType)

import           Crux.LLVM.Bugfinding.FullType (FullType(..), FullTypeRepr)

-- data Cursor (inTy :: FullType arch) (atTy :: FullType arch) where
--   Here :: FullTypeRepr atTy -> Cursor inTy atTy
--   Dereference :: Cursor inTy atTy -> Cursor ('FTPtr inTy) atTy
--   Index :: (i <= n) => NatRepr i -> Cursor inTy atTy -> Cursor ('FTArray n inTy) atTy
--   Field :: Ctx.Index fields inTy -> Cursor inTy atTy -> Cursor ('FTStruct fields) atTy

data Cursor m (ft :: FullType m) where
  Here :: FullTypeRepr m ft -> Cursor m ft
  Dereference :: Cursor m ft -> Cursor m ('FTPtr ft)
  Index :: (i <= n) => NatRepr i -> NatRepr n -> Cursor m ft -> Cursor m ('FTArray n ft)
  Field ::
    Ctx.Assignment (FullTypeRepr m) fields ->
    Ctx.Index fields ft ->
    Cursor m ft ->
    Cursor m ('FTStruct fields)

data SomeCursor = forall m ft. SomeCursor (Cursor m ft)

-- TODO: Use more type information?
ppCursor ::
  String {-^ Top level, e.g. the name of a variable -} ->
  Cursor m ft ->
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
data Selector m (argTypes :: Ctx (FullType m)) ft
  = SelectArgument !(Ctx.Index argTypes ft) (Cursor m ft)
  | SelectGlobal !L.Symbol (Cursor m ft)
  -- TODO
  -- deriving (Eq, Ord)

selectorCursor :: Simple Lens (Selector m argTypes ft) (Cursor m ft)
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

seekLlvmType :: Cursor m ft -> L.Type -> Either (TypeSeekError L.Type) L.Type
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
  Cursor m ft ->
  SymType ->
  Either (TypeSeekError SymType) MemType
seekSymType cursor symType =
  case asMemType symType of
    Right memType -> seekMemType cursor memType
    Left message -> Left $ UnsupportedType (SomeCursor cursor) symType message

seekMemType ::
  (?lc :: TypeContext) =>
  Cursor m ft->
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

instance TestEquality (Cursor m) where
  testEquality =
    $(U.structuralTypeEquality [t|Cursor|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (Cursor m) where
  compareF =
    $(U.structuralTypeOrd [t|Cursor|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))

instance TestEquality (Selector m argTypes) where
  testEquality =
    $(U.structuralTypeEquality [t|Selector|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|testEquality|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|testEquality|]
            )
          ]))

instance OrdF (Selector m argTypes) where
  compareF =
    $(U.structuralTypeOrd [t|Selector|]
      (let appAny con = U.TypeApp con U.AnyType
       in [ ( appAny (U.ConType [t|NatRepr|])
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|FullTypeRepr|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Cursor|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Assignment|]))
            , [|compareF|]
            )
          , ( appAny (appAny (U.ConType [t|Ctx.Index|]))
            , [|compareF|]
            )
          ]))
