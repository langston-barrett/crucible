{-|
Module      : Lang.Crucible.Solver.SemiRing
Copyright   : (c) Galois Inc, 2017
License     : BSD3
Maintainer  : rdockins@galois.com

Define a notion of semirings on base types, and operations thereon.  This
is used to allow us to define a generic notion of linear combinations of
terms that is useful for gathering coefficents in expressions on 
natural numbers, integers, reals and complex numbers.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.Solver.SemiRing
  ( SemiRing(..)
  , Coefficent
  , WSum
  , constWSum
  , zeroWSum
  , oneWSum
  , addWSum
  , termWSum
  , smulWSum
  , addConst
  , ppSemiRingSum
  ) where

--import           Data.Complex

import           Lang.MATLAB.Utils.Nat
import           Data.Parameterized.Classes

import           Lang.Crucible.BaseTypes
import qualified Lang.Crucible.Solver.WeightedSum as WS
import           Lang.Crucible.Solver.WeightedSum (WeightedSum)

data SemiRing (tp :: BaseType) where
  SemiRingNat  :: SemiRing BaseNatType
  SemiRingInt  :: SemiRing BaseIntegerType
  SemiRingReal :: SemiRing BaseRealType
--  SemiRingCplx :: SemiRing BaseComplexType

type family Coefficent (tp :: BaseType) where
  Coefficent BaseNatType     = Nat
  Coefficent BaseIntegerType = Integer
  Coefficent BaseRealType    = Rational
--  Coefficent BaseComplexType = Complex Rational

type WSum (f :: BaseType -> *) (tp :: BaseType) = WeightedSum (Coefficent tp) f tp

constWSum :: HashableF f => SemiRing tp -> Coefficent tp -> WSum f tp
constWSum SemiRingNat  = WS.constant
constWSum SemiRingInt  = WS.constant
constWSum SemiRingReal = WS.constant
--constWSum SemiRingCplx = WS.constant

zeroWSum :: HashableF f => SemiRing tp -> WSum f tp
zeroWSum SemiRingNat  = WS.constant 0
zeroWSum SemiRingInt  = WS.constant 0
zeroWSum SemiRingReal = WS.constant 0
--zeroWSum SemiRingCplx = WS.constant 0

oneWSum :: HashableF f => SemiRing tp -> WSum f tp
oneWSum SemiRingNat  = WS.constant 1
oneWSum SemiRingInt  = WS.constant 1
oneWSum SemiRingReal = WS.constant 1
--oneWSum SemiRingCplx = WS.constant 1

addWSum :: (HashableF f, Ord (f tp))
        => SemiRing tp
        -> WSum f tp
        -> WSum f tp
        -> WSum f tp
addWSum SemiRingNat  = WS.add
addWSum SemiRingInt  = WS.add
addWSum SemiRingReal = WS.add
--addWSum SemiRingCplx = WS.add

addConst :: SemiRing tp
         -> Coefficent tp
         -> WSum f tp
         -> WSum f tp
addConst SemiRingNat  c x = WS.addConstant x c
addConst SemiRingInt  c x = WS.addConstant x c
addConst SemiRingReal c x = WS.addConstant x c

termWSum :: HashableF f
         => SemiRing tp
         -> Coefficent tp
         -> f tp
         -> WSum f tp
termWSum SemiRingNat  = WS.scaledVar
termWSum SemiRingInt  = WS.scaledVar
termWSum SemiRingReal = WS.scaledVar

smulWSum :: HashableF f
         => SemiRing tp
         -> Coefficent tp
         -> WSum f tp
         -> WSum f tp
smulWSum SemiRingNat  = WS.scale
smulWSum SemiRingInt  = WS.scale
smulWSum SemiRingReal = WS.scale


ppSemiRingSum :: SemiRing tp
              -> WSum f tp
              -> 
prettyApp (tpname++"Sum") (WSum.eval (++) ppEntry ppConstant s)
      where tpname = case sr of
                        SemiRingNat  -> "nat"
                        SemiRingInt  -> "int"
                        SemiRingReal -> "real"
            ppConstant 0 = []
            ppConstant c = [ stringPrettyArg (ppRat c)]
            ppEntry 1 e = [ eltPrettyArg e ]
            ppEntry sm e = [ stringPrettyArg (ppRat sm ++ "*"), eltPrettyArg e ]
            ppRat r | d == 1 = show n
                    | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
              where n = numerator r
                    d = denominator r
