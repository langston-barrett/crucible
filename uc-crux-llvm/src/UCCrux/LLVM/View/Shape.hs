{-
Module           : UCCrux.LLVM.View.Shape
Description      : See "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module UCCrux.LLVM.View.Shape
  ( PtrShapeView(..),
    ptrShapeView,
    viewPtrShape,
    ShapeView(..),
    shapeView,
    viewShape,
  )
where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Foldable (toList)
import           Data.List.NonEmpty (NonEmpty, nonEmpty)
import           Data.Sequence (Seq)
import           GHC.Generics (Generic)

import           Data.Parameterized.TraversableFC (toListFC)

import           UCCrux.LLVM.FullType.Type (FullTypeRepr)
import           UCCrux.LLVM.Shape (PtrShape(..), Shape(..))

data PtrShapeView vtag
  = VShapeUnallocated
  | VShapeAllocated Int
  | VShapeInitialized (Seq (ShapeView vtag))
  deriving (Eq, Generic, Ord, Show)

ptrShapeView ::
  (forall t. tag t -> vtag) ->
  PtrShape m tag ft ->
  PtrShapeView vtag
ptrShapeView tag =
  \case
    ShapeUnallocated -> VShapeUnallocated
    ShapeAllocated n -> VShapeAllocated n
    ShapeInitialized s -> VShapeInitialized (fmap (shapeView tag) s)

viewPtrShape ::
  (forall t. vtag -> Either e (tag t)) ->
  FullTypeRepr m ft ->
  PtrShapeView vtag ->
  Either e (PtrShape m tag ft)
viewPtrShape tag ft =
  \case
    VShapeUnallocated -> Right ShapeUnallocated
    VShapeAllocated n -> Right (ShapeAllocated n)
    VShapeInitialized s ->
      ShapeInitialized <$> traverse (viewShape tag ft) s

data ShapeView vtag
  = VShapeInt vtag
  | VShapeFloat vtag
  | VShapePtr vtag (PtrShapeView vtag)
  | VShapeFuncPtr vtag
  | VShapeOpaquePtr vtag
  | VShapeArray vtag (NonEmpty (ShapeView vtag))
  | VShapeUnboundedArray vtag (Seq (ShapeView vtag))
  | VShapeStruct vtag [ShapeView vtag]
  deriving (Eq, Generic, Ord, Show)

shapeView ::
  (forall t. tag t -> vtag) ->
  Shape m tag ft ->
  ShapeView vtag
shapeView tag =
  \case
    ShapeInt t -> VShapeInt (tag t)
    ShapeFloat t -> VShapeFloat (tag t)
    ShapePtr t ps -> VShapePtr (tag t) (ptrShapeView tag ps)
    ShapeFuncPtr t -> VShapeFuncPtr (tag t)
    ShapeOpaquePtr t -> VShapeOpaquePtr (tag t)
    ShapeArray t _nr vec ->
      case nonEmpty (map (shapeView tag) (toList vec)) of
        Nothing -> error "Impossible"
        Just vec' -> VShapeArray (tag t) vec'
    ShapeUnboundedArray t s ->
      VShapeUnboundedArray (tag t) (fmap (shapeView tag) s)
    ShapeStruct t fields ->
      VShapeStruct (tag t) (toListFC (shapeView tag) fields)

viewShape ::
  (forall t. vtag -> Either e (tag t)) ->
  FullTypeRepr m ft ->
  ShapeView vtag ->
  Either e (Shape m tag ft)
viewShape tag ft = _

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''PtrShapeView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''ShapeView)
