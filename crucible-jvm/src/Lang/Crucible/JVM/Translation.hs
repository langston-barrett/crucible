{- |
Module           : Lang.Crucible.JVM.Translation
Description      : Translation of JVM AST into Crucible control-flow graph
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -haddock #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Lang.Crucible.JVM.Translation where

import Data.Monoid((<>))
import Control.Monad.State.Strict
import Control.Monad.ST
import Control.Lens hiding (op, (:>))
import Data.Int (Int32)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Data.Text (Text)

import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR


import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState   as C
import qualified Lang.Crucible.Simulator.OverrideSim   as C
import qualified Lang.Crucible.Simulator.RegValue      as C

import qualified Lang.Crucible.Analysis.Postdom        as C
import qualified Lang.Crucible.Utils.MuxTree           as C


import           What4.ProgramLoc (Position(InternalPos))
import           What4.Interface (IsExprBuilder)
import qualified What4.Interface                       as W4
import qualified What4.Partial                         as W4

import Debug.Trace

----------------------------------------------------------------------
-- JVM types

-- | JVM extension.
{-
newtype JVM = JVM () -- TODO
type instance ExprExtension JVM = EmptyExprExtension
type instance StmtExtension JVM = EmptyStmtExtension
-}
type JVM = ()

type JVMObjectType = RecursiveType "JVM_object" EmptyCtx

type JVMDoubleType = FloatType DoubleFloat
type JVMFloatType  = FloatType SingleFloat
type JVMIntType    = BVType 32
type JVMLongType   = BVType 64
type JVMRefType    = MaybeType (ReferenceType JVMObjectType)

-- | A JVM value is either a double, float, int, long, or reference.
type JVMValueType = VariantType JVMValueCtx

type JVMValueCtx =
  EmptyCtx
  ::> JVMDoubleType
  ::> JVMFloatType
  ::> JVMIntType
  ::> JVMLongType
  ::> JVMRefType


-- | An initialization state is 
--      "data Initialization Status = NotStarted | Started | Initialized | Erroneous"
-- We encode this type in Crucible using 2 bits
type InitializationStatus = BVType 2

-- these pattern synonyms would be easier to define if  Data.Parameterized.NatRepr
-- included some for NatReprs
pattern NotStarted, Started, Initialized, Erroneous :: Expr JVM f InitializationStatus
pattern NotStarted  <- App (BVLit n 0) where
  NotStarted   =  App $ BVLit knownRepr 0
pattern Started     <- App (BVLit n 1) where
  Started      = App $ BVLit knownRepr 1
pattern Initialized <- App (BVLit n 2) where
  Initialized  = App $ BVLit knownRepr 2
pattern Erroneous   <- App (BVLit n 3) where
  Erroneous    = App $ BVLit knownRepr 3


-- | An entry in the class table contains information about a loaded class:
-- its name, initialization status, and superclass name
--   data Class = MkClass { className :: String
--                        , initializationStatus :: InitializationStatus
--                        , superClass :: Maybe String }
--
type JVMClassType =
  StructType (EmptyCtx ::> StringType ::> InitializationStatus ::> MaybeType StringType)

-- Construction
jvmMkClassType :: Expr JVM f StringType
               -> Expr JVM f InitializationStatus
               -> Expr JVM f (MaybeType StringType)
               -> Expr JVM f JVMClassType
jvmMkClassType name ini super =
  App $ MkStruct knownRepr (Ctx.empty `Ctx.extend` name `Ctx.extend` ini `Ctx.extend` super)

-- | Textual representation of the name of a class
classText :: J.Class -> Text
classText c = fromString (J.unClassName (J.className c))

-- | update the global class table to include an entry for this class
-- 
jvmInitializeClassType :: GlobalVar JVMClassTableType -> J.Class
                       -> Generator JVM h s t ret (Expr JVM s JVMClassType)
jvmInitializeClassType gv c  = do
  let className  = App $ TextLit $ classText c
  let superClass = App $ NothingValue knownRepr  -- TODO!
  let str        = App $ MkStruct knownRepr (Ctx.empty `Ctx.extend` className
                                             `Ctx.extend` NotStarted `Ctx.extend` superClass)
  sm <- readGlobal gv
  let expr = App $ InsertStringMapEntry knownRepr sm className (App $ JustValue knownRepr str)
  writeGlobal gv expr
  return str
  
-- Access
jvmGetClassName :: Expr JVM f JVMClassType -> Expr JVM f StringType
jvmGetClassName ct = App (GetStruct ct Ctx.i1of3 knownRepr)

jvmGetClassInitializationStatus :: Expr JVM f JVMClassType -> Expr JVM f InitializationStatus
jvmGetClassInitializationStatus ct = App (GetStruct ct Ctx.i2of3 knownRepr)

jvmGetClassSuper :: Expr JVM f JVMClassType -> Expr JVM f (MaybeType StringType)
jvmGetClassSuper ct = App (GetStruct ct Ctx.i3of3 knownRepr)

-- Update




-- | The dynamic class table is a data structure that can be queried at runtime
-- for information about loaded classes
type JVMClassTableType = StringMapType JVMClassType


-- | A class instance contains a table of fields
-- and an (immutable) pointer to the class (object).
type JVMInstanceType =
  StructType (EmptyCtx ::> StringMapType JVMValueType ::> JVMClassType)

-- | An array is a length paired with a vector of values.
type JVMArrayType =
  StructType (EmptyCtx ::> JVMIntType ::> VectorType JVMValueType)

-- | An object is either a class instance or an array.
type JVMObjectImpl =
  VariantType (EmptyCtx ::> JVMInstanceType ::> JVMArrayType)

instance IsRecursiveType "JVM_object" where
  type UnrollType "JVM_object" ctx = JVMObjectImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMObjectImpl

----------------------------------------------------------------------
-- Index values for sums and products

tagD :: Ctx.Index JVMValueCtx JVMDoubleType
tagD = Ctx.i1of5

tagF :: Ctx.Index JVMValueCtx JVMFloatType
tagF = Ctx.i2of5

tagI :: Ctx.Index JVMValueCtx JVMIntType
tagI = Ctx.i3of5

tagL :: Ctx.Index JVMValueCtx JVMLongType
tagL = Ctx.i4of5

tagR :: Ctx.Index JVMValueCtx JVMRefType
tagR = Ctx.i5of5

----------------------------------------------------------------------
-- JVMValue

type JVMBool   s = Expr JVM s BoolType
type JVMDouble s = Expr JVM s JVMDoubleType
type JVMFloat  s = Expr JVM s JVMFloatType
type JVMInt    s = Expr JVM s JVMIntType
type JVMLong   s = Expr JVM s JVMLongType
type JVMRef    s = Expr JVM s JVMRefType
type JVMObject s = Expr JVM s JVMObjectType

{-
data JVMValue f
  = DValue (f JVMDoubleType)
  | FValue (f JVMFloatType)
  | IValue (f JVMIntType)
  | LValue (f JVMLongType)
  | RValue (f JVMRefType)
type JVMExpr s = JVMValue (Expr JVM s)
type JVMReg s = JVMValue (Reg s)
-}

data JVMValue s
  = DValue (JVMDouble s)
  | FValue (JVMFloat s)
  | IValue (JVMInt s)
  | LValue (JVMLong s)
  | RValue (JVMRef s)

data JVMReg s
  = DReg (Reg s JVMDoubleType)
  | FReg (Reg s JVMFloatType)
  | IReg (Reg s JVMIntType)
  | LReg (Reg s JVMLongType)
  | RReg (Reg s JVMRefType)

data JVMFrame v
  = JVMFrame
    { _operandStack :: ![v]
    , _localVariables :: !(Map J.LocalVariableIndex v)
    }

instance Functor JVMFrame where
  fmap f (JVMFrame os lv) = JVMFrame (fmap f os) (fmap f lv)

instance Foldable JVMFrame where
  foldr f z (JVMFrame os lv) = foldr f (foldr f z lv) os

instance Traversable JVMFrame where
  traverse f (JVMFrame os lv) = JVMFrame <$> traverse f os <*> traverse f lv

operandStack :: Simple Lens (JVMFrame v) [v]
operandStack = lens _operandStack (\s v -> s{ _operandStack = v})

localVariables :: Simple Lens (JVMFrame v) (Map J.LocalVariableIndex v)
localVariables = lens _localVariables (\s v -> s{ _localVariables = v})

type JVMExprFrame s = JVMFrame (JVMValue s)
type JVMRegisters s = JVMFrame (JVMReg s)

----------------------------------------------------------------------
-- JVMRef

rIsNull :: JVMRef s -> JVMGenerator h s ret (JVMBool s)
rIsNull mr =
  caseMaybe mr knownRepr
  MatchMaybe {
    onNothing = return bTrue,
    onJust = \_ -> return bFalse
    }

rEqual :: JVMRef s -> JVMRef s -> JVMGenerator h s ret (JVMBool s)
rEqual mr1 mr2 =
  caseMaybe mr1 knownRepr
  MatchMaybe {
    onNothing = rIsNull mr2,
    onJust = \r1 ->
    caseMaybe mr2 knownRepr
    MatchMaybe {
      onNothing = return bFalse,
      onJust = \r2 -> return (App (ReferenceEq knownRepr r1 r2))
      }
    }

----------------------------------------------------------------------
-- | Class Initialization
-- 
-- Make sure that static fields have their initial values
--

--data InitializationStatus = NotStarted | Started | Initialized | Erroneous
--  deriving (Eq,Ord,Show)

  
-- REVISIT: it may make sense for this to be dynamic
skipInit :: J.ClassName -> Bool
skipInit cname = cname `elem` [ "java/lang/Object"
                              , "java/lang/System"
                              , "java/io/Reader"
                              , "java/io/InputStreamReader"
                              ]

-- | Returns a default value for objects with given type, suitable for
-- initializing fields.
defaultValue :: J.Type -> JVMValue s
defaultValue (J.ArrayType _tp) = RValue $ App $ NothingValue knownRepr
defaultValue J.BooleanType     = IValue $ App $ BVLit knownRepr 0
defaultValue J.ByteType        = IValue $ App $ BVLit knownRepr 0
defaultValue J.CharType        = IValue $ App $ BVLit knownRepr 0
defaultValue (J.ClassType _st) = RValue $ App $ NothingValue knownRepr
defaultValue J.DoubleType      = DValue $ App $ DoubleLit 0.0
defaultValue J.FloatType       = FValue $ App $ FloatLit 0.0
defaultValue J.IntType         = IValue $ App $ BVLit knownRepr 0
defaultValue J.LongType        = LValue $ App $ BVLit knownRepr 0
defaultValue J.ShortType       = IValue $ App $ BVLit knownRepr 0


-- | Compute the initial value of a field based on its
-- static initializer and/or type
initialFieldValue :: J.ClassName -> J.Field -> JVMValue s
initialFieldValue name f = 
  case J.fieldConstantValue f of
     Just (J.Double v) ->
        (DValue (App (DoubleLit v)))
     Just (J.Float v) ->
        (FValue (App (FloatLit v)))
     Just (J.Integer v) ->
        (IValue (App (BVLit knownRepr (toInteger v))))
     Just (J.Long v) ->
        (LValue (App (BVLit knownRepr (toInteger v))))
     Just (J.String v) ->
        error "TODO: constant string initializers unsupported"
     Nothing ->
       (defaultValue (J.fieldType f))
     Just tp -> error $ "Unsupported field type" ++ show tp


setStaticFieldValueCtx :: JVMContext -> J.FieldId -> JVMValue s -> JVMGenerator h s ret ()
setStaticFieldValueCtx ctx fieldId val = do
    let cName = J.fieldIdClass fieldId 
    case Map.lookup (cName, J.fieldIdName fieldId) (staticTable ctx) of
         Just glob -> do
           --traceM $ "Setting " ++ show glob
           dyn <- toJVMDynamic (J.fieldIdType fieldId) val
           writeGlobal glob dyn
         Nothing -> 
           jvmFail "putstatic: field not found"

initializeField :: JVMContext -> J.ClassName -> J.Field -> JVMGenerator h s ret ()
initializeField ctx name f = 
  let fieldId = J.FieldId name (J.fieldName f) (J.fieldType f)
  in
    when (J.fieldIsStatic f) $ 
      setStaticFieldValueCtx ctx fieldId (initialFieldValue name f)


-- This needs to be in the Generator monad so that we can do case analysis
-- in the simulator
initializeClass :: forall h s ret . JVMContext -> J.ClassName -> JVMGenerator h s ret ()
initializeClass ctx name = if (name == "java/lang/Object") then (return ()) else do
  
  let mc = lookupClassCtx ctx name

  c <- maybe (jvmFail $ "Class " ++ J.unClassName name ++ " not found") return mc
  
  traceM $ "initializing class:" ++ J.unClassName name
  status <- getInitializationStatus ctx c

  let ifNotStarted :: JVMGenerator h s ret ()
      ifNotStarted = do
      
      setInitializationStatus ctx c Started
      
      maybe (return ()) (initializeClass ctx) (J.superClass c)

      -- initialize all of the fields with default values
      mapM_ (initializeField ctx name) $ J.classFields c

      -- run the static initializer for the class
      let clinit = (J.MethodKey "<clinit>" [] Nothing)
      case c `J.lookupMethod` clinit  of
          Just _ -> 
            unless (skipInit name) $ do
              handle <- getMethodCtx ctx name clinit
              callJVMHandleUnit handle
          Nothing -> return ()
          
      setInitializationStatus ctx c Initialized

  ifte_ (App $ BVEq knownRepr status NotStarted) ifNotStarted (return ())
  
{-          
    Erroneous   -> return () -- createAndThrow "java/lang/NoClassDefFoundError"
    Started     -> return ()
    Initialized -> return ()
-}


----------------------------------------------------------------------
-- | JVMContext
-- 
-- Contains information about crucible Function handles and Global variables
-- that is statically known during the class translation.
-- 

data JVMHandleInfo where
  JVMHandleInfo :: J.Method -> FnHandle init ret -> JVMHandleInfo

data JVMContext =
  JVMContext
  {  symbolMap   :: Map (J.ClassName, J.MethodKey) JVMHandleInfo
      -- ^ map from method names to Crucible function handles
  , staticTable :: Map (J.ClassName, String) (GlobalVar JVMValueType)
      -- ^ map from field names to Crucible global variables
  , classTable  :: Map J.ClassName J.Class
      -- ^ map from class names to their declarations
  , dynamicClassTable :: GlobalVar JVMClassTableType
      -- ^ a global variable storing information about the class that can be
      -- used at runtime: initialization status, 
  }

-- left-biased merge of two contexts
-- maybe this should be a semi-group instead???
-- NOTE: There should only every be one dynamic class table. 
instance Monoid JVMContext where
  mempty = JVMContext Map.empty Map.empty Map.empty undefined
  mappend c1 c2 =
    JVMContext { symbolMap         = Map.union (symbolMap   c1) (symbolMap   c2)
               , staticTable       = Map.union (staticTable c1) (staticTable c2)
               , classTable        = Map.union (classTable  c1) (classTable  c2)
               , dynamicClassTable = dynamicClassTable c1
               }


getMethodCtx :: JVMContext -> J.ClassName -> J.MethodKey -> JVMGenerator h s ret JVMHandleInfo
getMethodCtx ctx className methodKey = do
   let mhandle = Map.lookup (className, methodKey) (symbolMap ctx)
   case mhandle of
      Nothing -> jvmFail $ "getMethod: method " ++ show methodKey ++ " in class "
                               ++ show className ++ " not found"
      Just handle -> return handle

             
getMethod :: J.ClassName -> J.MethodKey -> JVMStmtGen h s ret JVMHandleInfo
getMethod className methodKey = do
   --traceM $ "getMethod " ++ show (J.methodKeyName methodKey) ++ " in class " ++ show className
   ctx <- lift $ gets jsContext
   lift $ getMethodCtx ctx className methodKey

getStaticFieldValue :: J.FieldId -> JVMStmtGen h s ret (JVMValue s)
getStaticFieldValue fieldId = do
      let cls = J.fieldIdClass fieldId
      ctx <- lift $ gets jsContext
      lift $ initializeClass ctx cls
      case Map.lookup (J.fieldIdClass fieldId, J.fieldIdName fieldId) (staticTable ctx) of
        Just glob -> do
          ---traceM $ "reading from " ++ show glob
          r <- lift $ readGlobal glob
          fromJVMDynamic (J.fieldIdType fieldId) r
        Nothing -> 
          sgFail $ "getstatic: field " ++ J.fieldIdName fieldId ++ " not found"
  
setStaticFieldValue :: J.FieldId -> JVMValue s -> JVMStmtGen h s ret ()
setStaticFieldValue fieldId val = do
   let cName = J.fieldIdClass fieldId
   ctx <- lift $ gets jsContext
   case Map.lookup (cName, J.fieldIdName fieldId) (staticTable ctx) of
         Just glob -> do
           --traceM $ "Setting " ++ show glob
           dyn <- lift $ toJVMDynamic (J.fieldIdType fieldId) val
           lift $ writeGlobal glob dyn
         Nothing -> 
           sgFail "putstatic: field not found"


lookupClassCtx :: JVMContext -> J.ClassName -> Maybe J.Class
lookupClassCtx ctx cName = 
  Map.lookup cName (classTable ctx) 


-- | lookup the class information (i.e. methods, fields, superclass)
lookupClass :: J.ClassName -> JVMStmtGen h s ret J.Class
lookupClass cName = do
  ctx <- lift $ gets jsContext
  case Map.lookup cName (classTable ctx) of
    Just cls -> return cls
    Nothing  -> sgFail $ "no information about class " ++ J.unClassName cName
  -- mcl <- liftIO $ J.tryLookupClass cb cName


------------------------------------------------------------------------
-- JVMState

data JVMState ret s
  = JVMState
  { _jsLabelMap :: !(Map J.BBId (Label s))
  , _jsFrameMap :: !(Map J.BBId (JVMFrame (JVMReg s)))
  , _jsCFG :: J.CFG
  , jsRetType :: TypeRepr ret
  , jsContext :: JVMContext
  }

jsLabelMap :: Simple Lens (JVMState ret s) (Map J.BBId (Label s))
jsLabelMap = lens _jsLabelMap (\s v -> s { _jsLabelMap = v })

jsFrameMap :: Simple Lens (JVMState ret s) (Map J.BBId (JVMFrame (JVMReg s)))
jsFrameMap = lens _jsFrameMap (\s v -> s { _jsFrameMap = v })

jsCFG :: Simple Lens (JVMState ret s) J.CFG
jsCFG = lens _jsCFG (\s v -> s { _jsCFG = v })


-- | Access the class table entry of in the dynamic class table
-- If this class table entry has not yet been defined, define it
-- (Note: this function does not call the class initializer.)
getClassTableEntry :: J.Class -> JVMContext -> JVMGenerator h s ret (Expr JVM s JVMClassType)
getClassTableEntry c st = do 
  let gv = (dynamicClassTable st)
  sm <- readGlobal gv
  let cn = App $ TextLit (classText c)
  let lu = App $ LookupStringMapEntry knownRepr sm cn
  caseMaybe lu knownRepr
    MatchMaybe 
      { onNothing = jvmInitializeClassType gv c                     
      , onJust    = return
      }
      
-- | Access the initialization status of the class in the dynamic class table
-- If the class table entry for this class has not yet been defined, define it
getInitializationStatus :: JVMContext ->  J.Class -> JVMGenerator h s ret (Expr JVM s InitializationStatus)
getInitializationStatus st c = do
  let gv = (dynamicClassTable st)
  sm <- readGlobal gv
  let cn = App $ TextLit (classText c)
  let lu = App $ LookupStringMapEntry knownRepr sm cn
  caseMaybe lu knownRepr
    MatchMaybe 
      { onNothing = do _ <- jvmInitializeClassType gv c
                       return NotStarted
      , onJust    = return . jvmGetClassInitializationStatus
      }

-- | Update the initialization status of the class in the dynamic class table
setInitializationStatus :: JVMContext -> J.Class 
                        -> (Expr JVM f InitializationStatus) -> JVMGenerator h s ret ()
setInitializationStatus ctx c status = do
  let gv = dynamicClassTable ctx
  sm <- readGlobal gv
  let name = App $ TextLit $ classText c
  let err  = App $ TextLit "Class Init error"
  let entry = App $ LookupStringMapEntry knownRepr sm name
  writeGlobal gv (App $ InsertStringMapEntry knownRepr sm name entry)
                        
------------------------------------------------------------------------
-- 
-- Generator to construct a CFG from sequence of monadic actions:
-- See [Lang.Crucible.CFG.Generator]
--
-- 'h' is parameter from underlying ST monad
-- 's' is phantom to prevent mixing constructs from different CFGs
-- 'ret' is return type of CFG

type JVMGenerator h s ret = Generator JVM h s (JVMState ret) ret

-- | Indicate that CFG generation failed due to ill-formed JVM code.
jvmFail :: String -> JVMGenerator h s ret a
jvmFail msg = fail msg

newJVMReg :: JVMValue s -> JVMGenerator h s ret (JVMReg s)
newJVMReg val =
  case val of
    DValue v -> DReg <$> newReg v
    FValue v -> FReg <$> newReg v
    IValue v -> IReg <$> newReg v
    LValue v -> LReg <$> newReg v
    RValue v -> RReg <$> newReg v

readJVMReg :: JVMReg s -> JVMGenerator h s ret (JVMValue s)
readJVMReg reg =
  case reg of
    DReg r -> DValue <$> readReg r
    FReg r -> FValue <$> readReg r
    IReg r -> IValue <$> readReg r
    LReg r -> LValue <$> readReg r
    RReg r -> RValue <$> readReg r

writeJVMReg :: JVMReg s -> JVMValue s -> JVMGenerator h s ret ()
writeJVMReg (DReg r) (DValue v) = assignReg r v
writeJVMReg (FReg r) (FValue v) = assignReg r v
writeJVMReg (IReg r) (IValue v) = assignReg r v
writeJVMReg (LReg r) (LValue v) = assignReg r v
writeJVMReg (RReg r) (RValue v) = assignReg r v
writeJVMReg _ _ = jvmFail "writeJVMReg"

saveStack :: [JVMReg s] -> [JVMValue s] -> JVMGenerator h s ret ()
saveStack [] [] = return ()
saveStack (r : rs) (v : vs) = writeJVMReg r v >> saveStack rs vs
saveStack _ _ = jvmFail "saveStack"

saveLocals ::
  Map J.LocalVariableIndex (JVMReg s) ->
  Map J.LocalVariableIndex (JVMValue s) ->
  JVMGenerator h s ret ()
saveLocals rs vs
  | Map.keys rs == Map.keys vs = sequence_ (Map.intersectionWith writeJVMReg rs vs)
  | otherwise                  = jvmFail "saveLocals"

newRegisters :: JVMExprFrame s -> JVMGenerator h s ret (JVMRegisters s)
newRegisters = traverse newJVMReg

readRegisters :: JVMRegisters s -> JVMGenerator h s ret (JVMExprFrame s)
readRegisters = traverse readJVMReg

writeRegisters :: JVMRegisters s -> JVMExprFrame s -> JVMGenerator h s ret ()
writeRegisters rs vs =
  do saveStack (rs^.operandStack) (vs^.operandStack)
     saveLocals (rs^.localVariables) (vs^.localVariables)

forceJVMValue :: JVMValue s -> JVMGenerator h s ret (JVMValue s)
forceJVMValue val =
  case val of
    DValue v -> DValue <$> forceEvaluation v
    FValue v -> FValue <$> forceEvaluation v
    IValue v -> IValue <$> forceEvaluation v
    LValue v -> LValue <$> forceEvaluation v
    RValue v -> RValue <$> forceEvaluation v

w8 :: NatRepr 8
w8 = knownNat

w16 :: NatRepr 16
w16 = knownNat

w32 :: NatRepr 32
w32 = knownNat

w64 :: NatRepr 64
w64 = knownNat


{-----
-- | Information about a JVM basic block
data JVMBlockInfo s
  = JVMBlockInfo
    {
      -- The crucible block label corresponding to this JVM block
      block_label    :: Label s

      -- map from labels to assignments that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map    :: !(Map J.BBId (Seq (L.Ident, L.Type, L.Value)))
    }

buildBlockInfoMap :: J.CFG -> LLVMEnd h s ret (Map J.BBId (Label s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: J.BasicBlock -> JVMEnd h s ret (J.BBId, Label s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let Just blk_lbl = L.bbLabel bb
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_label = lab
                                })
-------------------------------------------------------------------------------}

generateBasicBlock ::
  J.BasicBlock ->
  JVMRegisters s ->
  JVMGenerator h s ret a
generateBasicBlock bb rs =
  do -- Record the registers for this block.
     -- This also signals that generation of this block has started.
     jsFrameMap %= Map.insert (J.bbId bb) rs
     -- Read initial values
     vs <- readRegisters rs
     -- Translate all instructions
     (_, eframe) <- runStateT (mapM_ generateInstruction (J.bbInsts bb)) vs
     -- If we didn't already handle a block-terminating instruction,
     -- jump to the successor block, if there's only one.
     cfg <- use jsCFG
     case J.succs cfg (J.bbId bb) of
       [J.BBId succPC] ->
         do lbl <- processBlockAtPC succPC eframe
            _ <- jump lbl
            jvmFail "generateBasicBlock: ran off end of block"
       [] -> jvmFail "generateBasicBlock: no terminal instruction and no successor"
       _  -> jvmFail "generateBasicBlock: no terminal instruction and multiple successors"

-- | Prepare for a branch or jump to the given address, by generating
-- a transition block to copy the values into the appropriate
-- registers. If the target has already been translated (or is
-- currently being translated) then the registers already exist, so we
-- simply write into them. If the target has not been started yet, we
-- copy the values into fresh registers, and also recursively call
-- 'generateBasicBlock' on the target block to start translating it.
processBlockAtPC :: J.PC -> JVMExprFrame s -> JVMGenerator h s ret (Label s)
processBlockAtPC pc vs =
  defineBlockLabel $
  do bb <- getBasicBlockAtPC pc
     lbl <- getLabelAtPC pc
     fm <- use jsFrameMap
     case Map.lookup (J.bbId bb) fm of
       Just rs ->
         do writeRegisters rs vs
       Nothing ->
         do rs <- newRegisters vs
            defineBlock lbl (generateBasicBlock bb rs)
     jump lbl

getBasicBlockAtPC :: J.PC -> JVMGenerator h s ret J.BasicBlock
getBasicBlockAtPC pc =
  do cfg <- use jsCFG
     case J.bbByPC cfg pc of
       Nothing -> jvmFail "getBasicBlockAtPC"
       Just bb -> return bb

getLabelAtPC :: J.PC -> JVMGenerator h s ret (Label s)
getLabelAtPC pc =
  do bb <- getBasicBlockAtPC pc
     lm <- use jsLabelMap
     case Map.lookup (J.bbId bb) lm of
       Nothing -> jvmFail "getLabelAtPC"
       Just lbl -> return lbl

----------------------------------------------------------------------
-- JVM statement generator monad


-- | This has extra state that is only relevant in the context of a
-- single basic block: It tracks the values of the operand stack and
-- local variable array at each instruction.
type JVMStmtGen h s ret = StateT (JVMExprFrame s) (JVMGenerator h s ret)

-- | Indicate that CFG generation failed due to ill-formed JVM code.
sgFail :: String -> JVMStmtGen h s ret a
sgFail msg = lift $ jvmFail msg

sgUnimplemented :: String -> JVMStmtGen h s ret a
sgUnimplemented msg = sgFail $ "unimplemented: " ++ msg

getStack :: JVMStmtGen h s ret [JVMValue s]
getStack = use operandStack

putStack :: [JVMValue s] -> JVMStmtGen h s ret ()
putStack vs = operandStack .= vs

popValue :: JVMStmtGen h s ret (JVMValue s)
popValue =
  do vs <- getStack
     case vs of
       [] -> sgFail "popValue: empty stack"
       (v : vs') ->
         do putStack vs'
            return v

pushValue :: JVMValue s -> JVMStmtGen h s ret ()
pushValue v =
  do v' <- lift $ forceJVMValue v
     vs <- getStack
     putStack (v' : vs)

pushValues :: [JVMValue s] -> JVMStmtGen h s ret ()
pushValues vs =
  do vs' <- getStack
     putStack (vs ++ vs')

isType1 :: JVMValue s -> Bool
isType1 v =
  case v of
    DValue _ -> False
    LValue _ -> False
    _        -> True

isType2 :: JVMValue s -> Bool
isType2 = not . isType1

popType1 :: JVMStmtGen h s ret (JVMValue s)
popType1 =
  do v <- popValue
     if isType1 v then return v else sgFail "popType1"

popType2 :: JVMStmtGen h s ret [JVMValue s]
popType2 =
  do vs <- getStack
     case vs of
       v : vs' | isType2 v ->
         putStack vs' >> return [v]
       v1 : v2 : vs' | isType1 v1 && isType1 v2 ->
         putStack vs' >> return [v1, v2]
       _ ->
         sgFail "popType2"

fromIValue :: JVMValue s -> JVMGenerator h s ret (JVMInt s)
fromIValue (IValue v) = return v
fromIValue _ = jvmFail "fromIValue"

fromLValue :: JVMValue s -> JVMGenerator h s ret (JVMLong s)
fromLValue (LValue v) = return v
fromLValue _ = jvmFail "fromLValue"

fromDValue :: JVMValue s -> JVMGenerator h s ret (JVMDouble s)
fromDValue (DValue v) = return v
fromDValue _ = jvmFail "fromDValue"

fromFValue :: JVMValue s -> JVMGenerator h s ret (JVMFloat s)
fromFValue (FValue v) = return v
fromFValue _ = jvmFail "fromFValue"

fromRValue :: JVMValue s -> JVMGenerator h s ret (JVMRef s)
fromRValue (RValue v) = return v
fromRValue _ = jvmFail "fromRValue"

iPop :: JVMStmtGen h s ret (JVMInt s)
iPop = popValue >>= lift . fromIValue

lPop :: JVMStmtGen h s ret (JVMLong s)
lPop = popValue >>= lift . fromLValue

rPop :: JVMStmtGen h s ret (JVMRef s)
rPop = popValue >>= lift . fromRValue

dPop :: JVMStmtGen h s ret (JVMDouble s)
dPop = popValue >>= lift . fromDValue

fPop :: JVMStmtGen h s ret (JVMFloat s)
fPop = popValue >>= lift . fromFValue

iPush :: JVMInt s -> JVMStmtGen h s ret ()
iPush i = pushValue (IValue i)

lPush :: JVMLong s -> JVMStmtGen h s ret ()
lPush l = pushValue (LValue l)

fPush :: JVMFloat s -> JVMStmtGen h s ret ()
fPush f = pushValue (FValue f)

dPush :: JVMDouble s -> JVMStmtGen h s ret ()
dPush d = pushValue (DValue d)

rPush :: JVMRef s -> JVMStmtGen h s ret ()
rPush r = pushValue (RValue r)

setLocal :: J.LocalVariableIndex -> JVMValue s -> JVMStmtGen h s ret ()
setLocal idx v =
  do v' <- lift $ forceJVMValue v
     localVariables %= Map.insert idx v'

getLocal :: J.LocalVariableIndex -> JVMStmtGen h s ret (JVMValue s)
getLocal idx =
  do vs <- use localVariables
     case Map.lookup idx vs of
       Just v -> return v
       Nothing -> sgFail "getLocal"

throwIfRefNull ::
  JVMRef s -> JVMStmtGen h s ret (Expr JVM s (ReferenceType JVMObjectType))
throwIfRefNull r = lift $ assertedJustExpr r "null dereference"

projectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s (VariantType ctx) ->
  JVMStmtGen h s ret (Expr JVM s tp)
projectVariant tag var =
  do let mx = App (ProjectVariant knownRepr tag var)
     lift $ assertedJustExpr mx "incorrect variant"

injectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s tp ->
  Expr JVM s (VariantType ctx)
injectVariant tag val = App (InjectVariant knownRepr tag val)

fromJVMDynamic :: J.Type -> Expr JVM s JVMValueType -> JVMStmtGen h s ret (JVMValue s)
fromJVMDynamic ty dyn =
  case ty of
    J.BooleanType -> IValue <$> projectVariant tagI dyn
    J.ArrayType _ -> RValue <$> projectVariant tagR dyn
    J.ByteType    -> IValue <$> projectVariant tagI dyn
    J.CharType    -> IValue <$> projectVariant tagI dyn
    J.ClassType _ -> RValue <$> projectVariant tagR dyn
    J.DoubleType  -> DValue <$> projectVariant tagD dyn
    J.FloatType   -> FValue <$> projectVariant tagF dyn
    J.IntType     -> IValue <$> projectVariant tagI dyn
    J.LongType    -> LValue <$> projectVariant tagL dyn
    J.ShortType   -> IValue <$> projectVariant tagI dyn

toJVMDynamic :: J.Type -> JVMValue s -> JVMGenerator h s ret (Expr JVM s JVMValueType)
toJVMDynamic ty val =
  case ty of
    J.BooleanType -> injectVariant tagI <$> fmap boolFromInt (fromIValue val)
    J.ArrayType _ -> injectVariant tagR <$> fromRValue val
    J.ByteType    -> injectVariant tagI <$> fmap byteFromInt (fromIValue val)
    J.CharType    -> injectVariant tagI <$> fmap charFromInt (fromIValue val)
    J.ClassType _ -> injectVariant tagR <$> fromRValue val
    J.DoubleType  -> injectVariant tagD <$> fromDValue val
    J.FloatType   -> injectVariant tagF <$> fromFValue val
    J.IntType     -> injectVariant tagI <$> fromIValue val
    J.LongType    -> injectVariant tagL <$> fromLValue val
    J.ShortType   -> injectVariant tagI <$> fmap shortFromInt (fromIValue val)



arrayLength :: Expr JVM s JVMArrayType -> JVMInt s
arrayLength arr = App (GetStruct arr Ctx.i1of2 knownRepr)

throw :: JVMRef s -> JVMStmtGen h s ret ()
throw _ = sgUnimplemented "throw"

rNull :: JVMRef s
rNull = App (NothingValue knownRepr)

iZero :: JVMInt s
iZero = App (BVLit w32 0)

bTrue :: JVMBool s
bTrue = App (BoolLit True)

bFalse :: JVMBool s
bFalse = App (BoolLit False)

processBlockAtPC' :: J.PC -> JVMStmtGen h s ret (Label s)
processBlockAtPC' pc =
  do vs <- get
     lift $ processBlockAtPC pc vs

nextPC :: J.PC -> JVMStmtGen h s ret J.PC
nextPC pc =
  do cfg <- lift $ use jsCFG
     case J.nextPC cfg pc of
       Nothing -> sgFail "nextPC"
       Just pc' -> return pc'

-- TODO
-- | read from a static variable. The static map should be stored in the
-- class table. But how do we make sure that the class table is initialized
-- in a way that all static references will see the same table?
{- getStaticMap ::
  J.ClassName -> JVMStmtGen h s ret (Expr JVM s (StringMapType JVMValueType))
getStaticMap _className = do
  let jvmClassTable :: GlobalVar JVMClassTableType
      jvmClassTable = error "define jvmClassTable"
  (ct :: Expr JVM s JVMClassTableType) <- readGlobal jvmClassTable
  LookupStringMapEntry  -}

putStaticMap ::
  J.ClassName -> Expr JVM s (StringMapType JVMValueType) -> JVMStmtGen h s ret ()
putStaticMap _className _ = sgUnimplemented "putStaticMap"

-- | lookup the static data structure associated with a class
-- Q: Where is this information initialized?
getClassObject ::
  J.ClassName -> JVMStmtGen h s ret (Expr JVM s JVMClassType)
getClassObject name = do
  ctx <- lift $ gets jsContext
  c <- lookupClass name
  lift $ getClassTableEntry c ctx
  
{-  dct <- lift $ gets jsDynamicClassTable
  case Map.lookup className dct of
    Just ref -> return ref
    Nothing -> sgFail $ "Cannot find class reference for " ++ J.unClassName className  -}

-- look up initial values for the object's fields.
-- NB: stringmaps are mutable in crucible. We can't return the same one each time...
getInstanceInit ::
  J.ClassName -> JVMStmtGen h s ret (Expr JVM s (StringMapType (MaybeType JVMValueType)))
getInstanceInit _className = sgUnimplemented "getInstanceInit"

----------------------------------------------------------------------

-- Compare an implicit type repr with an explicit one
eqI :: forall tp1 tp2. (KnownRepr TypeRepr tp1) =>
  TypeRepr tp2 -> Maybe (tp1 :~: tp2)
eqI = testEquality (knownRepr :: TypeRepr tp1)


-- Does this definition of pushRet look nicer? It is a little more obvious
-- that it is doing a case analysis. And the helper function is more
-- generic. But it does require the explicit type application, even though
-- the type is already known
pushRet ::
  forall h s ret tp. TypeRepr tp -> Expr JVM s tp -> JVMStmtGen h s ret ()
pushRet tp 
  | Just Refl <- eqI @JVMDoubleType tp = dPush
  | Just Refl <- eqI @JVMFloatType  tp = fPush
  | Just Refl <- eqI @JVMIntType    tp = iPush
  | Just Refl <- eqI @JVMLongType   tp = lPush
  | Just Refl <- eqI @JVMRefType    tp = rPush
  | Just Refl <- eqI @UnitType      tp = \_ -> return ()   -- ignore unit results?
  | otherwise = \_ -> sgFail $ "pushRet: invalid type " ++ show tp

{-  
  tryPush dPush $
  tryPush fPush $
  tryPush iPush $
  tryPush lPush $
  tryPush rPush $
  sgFail "pushRet: invalid type"
  where
    tryPush ::
      forall t. KnownRepr TypeRepr t =>
      (Expr JVM s t -> JVMStmtGen h s ret ()) ->
      JVMStmtGen h s ret () -> JVMStmtGen h s ret ()
    tryPush push k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> push expr
        Nothing -> k
-}
  
popArgument ::
  forall tp h s ret. TypeRepr tp -> JVMStmtGen h s ret (Expr JVM s tp)
popArgument tp =
  tryPop dPop $
  tryPop fPop $
  tryPop iPop $
  tryPop lPop $
  tryPop rPop $
  sgFail "pushRet: invalid type"
  where
    tryPop ::
      forall t. KnownRepr TypeRepr t =>
      JVMStmtGen h s ret (Expr JVM s t) ->
      JVMStmtGen h s ret (Expr JVM s tp) ->
      JVMStmtGen h s ret (Expr JVM s tp)
    tryPop pop k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> pop
        Nothing -> k

-- | Pop arguments from the stack; the last argument should be at the
-- top of the stack.
popArguments ::
  forall args h s ret.
  CtxRepr args -> JVMStmtGen h s ret (Ctx.Assignment (Expr JVM s) args)
popArguments args =
  case Ctx.viewAssign args of
    Ctx.AssignEmpty -> return Ctx.empty
    Ctx.AssignExtend tps tp ->
      do x <- popArgument tp
         xs <- popArguments tps
         return (Ctx.extend xs x)

callJVMHandleUnit :: JVMHandleInfo -> JVMGenerator h s ret ()
callJVMHandleUnit (JVMHandleInfo _method handle) =
  do let argTys = handleArgTypes handle
         retTy  = handleReturnType handle
     case (testEquality argTys (knownRepr :: Ctx.Assignment TypeRepr Ctx.EmptyCtx),
           testEquality retTy  (knownRepr :: TypeRepr UnitType)) of
       (Just Refl, Just Refl) -> do
         _ <- call (App (HandleLit handle)) knownRepr
         return ()
       (_,_) -> error "Internal error: can only call functions with no args/result"

callJVMHandle :: JVMHandleInfo -> JVMStmtGen h s ret ()
callJVMHandle (JVMHandleInfo _method handle) =
  do args <- popArguments (handleArgTypes handle)
     result <- lift $ call (App (HandleLit handle)) args
     pushRet (handleReturnType handle) result

----------------------------------------------------------------------

-- | Do the heavy lifting of translating JVM instructions to crucible code.
generateInstruction ::
  forall h s ret.
  (J.PC, J.Instruction) ->
  JVMStmtGen h s ret ()
generateInstruction (pc, instr) =
  case instr of
    -- Type conversion instructions
    J.D2f -> unary dPop fPush floatFromDouble
    J.D2i -> unary dPop iPush intFromDouble
    J.D2l -> unary dPop lPush longFromDouble
    J.F2d -> unary fPop dPush doubleFromFloat
    J.F2i -> unary fPop iPush intFromFloat
    J.F2l -> unary fPop lPush longFromFloat
    J.I2b -> unary iPop iPush byteFromInt
    J.I2c -> unary iPop iPush charFromInt
    J.I2d -> unary iPop dPush doubleFromInt
    J.I2f -> unary iPop fPush floatFromInt
    J.I2l -> unary iPop lPush longFromInt
    J.I2s -> unary iPop iPush shortFromInt
    J.L2d -> unary lPop dPush doubleFromLong
    J.L2f -> unary lPop fPush floatFromLong
    J.L2i -> unary lPop iPush intFromLong

    -- Arithmetic instructions
    J.Dadd  -> binary dPop dPop dPush dAdd
    J.Dsub  -> binary dPop dPop dPush dSub
    J.Dneg  -> unary dPop dPush dNeg
    J.Dmul  -> binary dPop dPop dPush dMul
    J.Ddiv  -> binary dPop dPop dPush dDiv
    J.Drem  -> binary dPop dPop dPush dRem
    J.Dcmpg -> binary dPop dPop iPush (error "dCmpg")
    J.Dcmpl -> binary dPop dPop iPush (error "dCmpl")
    J.Fadd  -> binary fPop fPop fPush fAdd
    J.Fsub  -> binary fPop fPop fPush fSub
    J.Fneg  -> unary fPop fPush (error "fNeg")
    J.Fmul  -> binary fPop fPop fPush fMul
    J.Fdiv  -> binary fPop fPop fPush fDiv
    J.Frem  -> binary fPop fPop fPush fRem
    J.Fcmpg -> binary fPop fPop iPush (error "fCmpg")
    J.Fcmpl -> binary fPop fPop iPush (error "fCmpl")
    J.Iadd  -> binary iPop iPop iPush (\a b -> App (BVAdd w32 a b))
    J.Isub  -> binary iPop iPop iPush (\a b -> App (BVSub w32 a b))
    J.Imul  -> binary iPop iPop iPush (\a b -> App (BVMul w32 a b))
    J.Idiv  -> binary iPop iPop iPush
               (\a b -> App (AddSideCondition (BaseBVRepr w32) (App (BVNonzero w32 b))
                             "java/lang/ArithmeticException"
                             (App (BVSdiv w32 a b))))
    J.Irem -> binary iPop iPop iPush
               (\a b -> App (AddSideCondition (BaseBVRepr w32) (App (BVNonzero w32 b))
                             "java/lang/ArithmeticException"
                             (App (BVSrem w32 a b))))
    J.Ineg  -> unary iPop iPush (error "iNeg")
    J.Iand  -> binary iPop iPop iPush (\a b -> App (BVAnd w32 a b))
    J.Ior   -> binary iPop iPop iPush (\a b -> App (BVOr  w32 a b))
    J.Ixor  -> binary iPop iPop iPush (\a b -> App (BVXor w32 a b))
    J.Ishl  -> binary iPop iPop iPush (\a b -> App (BVShl w32 a b))
    J.Ishr  -> binary iPop iPop iPush (\a b -> App (BVAshr w32 a b))
    J.Iushr -> binary iPop iPop iPush (\a b -> App (BVLshr w32 a b))
    J.Ladd  -> binary lPop lPop lPush (\a b -> App (BVAdd w64 a b))
    J.Lsub  -> binary lPop lPop lPush (\a b -> App (BVSub w64 a b))
    J.Lmul  -> binary lPop lPop lPush (\a b -> App (BVMul w64 a b))
    J.Lneg  -> unary lPop lPush (error "lNeg")
    J.Ldiv  -> binary lPop lPop (error "lPush")
               (\a b -> App (AddSideCondition (BaseBVRepr w64) (App (BVNonzero w64 b))
                             "java/lang/ArithmeticException"
                             (App (BVSdiv w64 a b))))
    J.Lrem -> binary lPop lPop lPush
               (\a b -> App (AddSideCondition (BaseBVRepr w64) (App (BVNonzero w64 b))
                             "java/lang/ArithmeticException"
                             (App (BVSrem w64 a b))))
    J.Land  -> binary lPop lPop lPush (\a b -> App (BVAnd w64 a b))
    J.Lor   -> binary lPop lPop lPush (\a b -> App (BVOr  w64 a b))
    J.Lxor  -> binary lPop lPop lPush (\a b -> App (BVXor w64 a b))
    J.Lcmp  -> binary lPop lPop iPush (error "lCmp")
    J.Lshl  -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVShl w64 a b))
    J.Lshr  -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVAshr w64 a b))
    J.Lushr -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVLshr w64 a b))

    -- Load and store instructions
    J.Iload idx -> getLocal idx >>= pushValue
    J.Lload idx -> getLocal idx >>= pushValue
    J.Fload idx -> getLocal idx >>= pushValue
    J.Dload idx -> getLocal idx >>= pushValue
    J.Aload idx -> getLocal idx >>= pushValue
    J.Istore idx -> popValue >>= setLocal idx
    J.Lstore idx -> popValue >>= setLocal idx
    J.Fstore idx -> popValue >>= setLocal idx
    J.Dstore idx -> popValue >>= setLocal idx
    J.Astore idx -> popValue >>= setLocal idx
    J.Ldc cpv ->
      case cpv of
        J.Double v   -> dPush (dConst v)
        J.Float v    -> fPush (fConst v)
        J.Integer v  -> iPush (iConst (toInteger v))
        J.Long v     -> lPush (lConst (toInteger v))
        J.String _v  -> sgUnimplemented "ldc string" -- pushValue . RValue =<< refFromString v
        J.ClassRef _ -> sgUnimplemented "ldc class"  -- pushValue . RValue =<< getClassObject c

    -- Object creation and manipulation
    -- TODO
    J.New name -> do
      --traceM $ "new " ++ show name
      clsObj <- getClassObject name
      cls <- lookupClass name
      fields <- mapM createField (J.classFields cls)
      newInstanceInstr clsObj fields

    J.Getfield fieldId ->
      do --traceM $ "getfield " ++ show (J.fieldIdName fieldId)
         objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         obj <- lift $ readRef rawRef
         let (uobj :: Expr JVM s JVMObjectImpl ) =
               App (UnrollRecursive knownRepr knownRepr obj)
               
         inst <- projectVariant Ctx.i1of2 uobj

         let fields = App (GetStruct inst Ctx.i1of2 knownRepr)

         let key = App (TextLit (fromString (J.fieldIdName fieldId)))
         
         let mval = App (LookupStringMapEntry knownRepr fields key)
         dyn <- lift $ assertedJustExpr mval "getfield: field not found"
         val <- fromJVMDynamic (J.fieldIdType fieldId) dyn
         pushValue val

    J.Putfield fieldId -> 
      do -- traceM $ "putfield " ++ show (J.fieldIdName fieldId)
         val <- popValue
         objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         obj <- lift $ readRef rawRef
         let uobj = App (UnrollRecursive knownRepr knownRepr obj)
         let minst = App (ProjectVariant knownRepr Ctx.i1of2 uobj)
         inst <- lift $ assertedJustExpr minst "putfield: not a valid class instance"
         let fields = App (GetStruct inst Ctx.i1of2 knownRepr)
         dyn <- lift $ toJVMDynamic (J.fieldIdType fieldId) val
         let key = App (TextLit (fromString (J.fieldIdName fieldId)))
         let mdyn = App (JustValue knownRepr dyn)
         let fields' = App (InsertStringMapEntry knownRepr fields key mdyn)
         let inst'  = App (SetStruct knownRepr inst Ctx.i1of2 fields')
         let uobj' = App (InjectVariant knownRepr Ctx.i1of2 inst')
         let obj' = App (RollRecursive knownRepr knownRepr uobj')
         lift $ writeRef rawRef obj'

    J.Getstatic fieldId -> do
      
      val <- getStaticFieldValue fieldId
      pushValue val

    J.Putstatic fieldId -> do
      val <- popValue
      setStaticFieldValue fieldId val

    -- Array creation and manipulation
    J.Newarray arrayType ->
      do count <- iPop
         let nonneg = App (BVSle w32 (iConst 0) count)
         lift $ assertExpr nonneg "java/lang/NegativeArraySizeException"
         -- FIXME: why doesn't jvm-parser just store the element type?
         case arrayType of
           J.ArrayType elemType ->
             case elemType of
               J.BooleanType -> newarrayInstr tagI count (iConst 0)
               J.ArrayType _ -> sgFail "newarray: invalid element type"
               J.ByteType    -> newarrayInstr tagI count (iConst 0)
               J.CharType    -> newarrayInstr tagI count (iConst 0)
               J.ClassType _ -> sgFail "newarray: invalid element type"
               J.DoubleType  -> newarrayInstr tagD count (dConst 0)
               J.FloatType   -> newarrayInstr tagF count (fConst 0)
               J.IntType     -> newarrayInstr tagI count (iConst 0)
               J.LongType    -> newarrayInstr tagL count (lConst 0)
               J.ShortType   -> newarrayInstr tagI count (iConst 0)
           _ -> sgFail "newarray: expected array type"
    J.Multianewarray _elemType dimensions ->
      do counts <- reverse <$> sequence (replicate (fromIntegral dimensions) iPop)
         forM_ counts $ \count -> do
           let nonneg = App (BVSle w32 (iConst 0) count)
           lift $ assertExpr nonneg "java/lang/NegativeArraySizeException"
         sgUnimplemented "multianewarray" --pushValue . RValue =<< newMultiArray arrayType counts

    -- Load an array component onto the operand stack
    J.Baload -> aloadInstr tagI IValue -- byte
    J.Caload -> aloadInstr tagI IValue -- char
    J.Saload -> aloadInstr tagI IValue -- short
    J.Iaload -> aloadInstr tagI IValue
    J.Laload -> aloadInstr tagL LValue
    J.Faload -> aloadInstr tagF FValue
    J.Daload -> aloadInstr tagD DValue
    J.Aaload -> aloadInstr tagR RValue

    -- Store a value from the operand stack as an array component
    J.Bastore -> iPop >>= astoreInstr tagI byteFromInt
    J.Castore -> iPop >>= astoreInstr tagI charFromInt
    J.Sastore -> iPop >>= astoreInstr tagI shortFromInt
    J.Iastore -> iPop >>= astoreInstr tagI id
    J.Lastore -> lPop >>= astoreInstr tagL id
    J.Fastore -> fPop >>= astoreInstr tagF id
    J.Dastore -> dPop >>= astoreInstr tagD id
    J.Aastore -> rPop >>= astoreInstr tagR id

    -- Stack management instructions
    J.Pop ->
      do void popType1
    J.Pop2 ->
      do void popType2
    J.Dup ->
      do value <- popType1
         pushValue value
         pushValue value
    J.Dup_x1 ->
      do value1 <- popType1
         value2 <- popType1
         pushValue value1
         pushValue value2
         pushValue value1
    J.Dup_x2 ->
      do value1 <- popType1
         value2 <- popType2
         pushValue value1
         pushValues value2
         pushValue value1
    J.Dup2 ->
      do value <- popType2
         pushValues value
         pushValues value
    J.Dup2_x1 ->
      do value1 <- popType2
         value2 <- popType1
         pushValues value1
         pushValue value2
         pushValues value1
    J.Dup2_x2 ->
      do value1 <- popType2
         value2 <- popType2
         pushValues value1
         pushValues value2
         pushValues value1
    J.Swap ->
      do value1 <- popType1
         value2 <- popType1
         pushValue value1
         pushValue value2

    -- Conditional branch instructions
    J.If_acmpeq pc' ->
      do r2 <- rPop
         r1 <- rPop
         eq <- lift $ rEqual r1 r2
         pc'' <- nextPC pc
         branchIf eq pc' pc''
    J.If_acmpne pc' ->
      do r2 <- rPop
         r1 <- rPop
         eq <- lift $ rEqual r1 r2
         pc'' <- nextPC pc
         branchIf (App (Not eq)) pc' pc''
    J.Ifnonnull pc' ->
      do r <- rPop
         n <- lift $ rIsNull r
         pc'' <- nextPC pc
         branchIf (App (Not n)) pc' pc''
    J.Ifnull pc' ->
      do r <- rPop
         n <- lift $ rIsNull r
         pc'' <- nextPC pc
         branchIf n pc' pc''

    J.If_icmpeq pc' -> icmpInstr pc pc' $ \a b -> App (BVEq w32 a b)
    J.If_icmpne pc' -> icmpInstr pc pc' $ \a b -> App (Not (App (BVEq w32 a b)))
    J.If_icmplt pc' -> icmpInstr pc pc' $ \a b -> App (BVSlt w32 a b)
    J.If_icmpge pc' -> icmpInstr pc pc' $ \a b -> App (BVSle w32 b a)
    J.If_icmpgt pc' -> icmpInstr pc pc' $ \a b -> App (BVSlt w32 b a)
    J.If_icmple pc' -> icmpInstr pc pc' $ \a b -> App (BVSle w32 a b)

    J.Ifeq pc' -> ifInstr pc pc' $ \a -> App (Not (App (BVNonzero w32 a)))
    J.Ifne pc' -> ifInstr pc pc' $ \a -> App (BVNonzero w32 a)
    J.Iflt pc' -> ifInstr pc pc' $ \a -> App (BVSlt w32 a iZero)
    J.Ifge pc' -> ifInstr pc pc' $ \a -> App (BVSle w32 iZero a)
    J.Ifgt pc' -> ifInstr pc pc' $ \a -> App (BVSlt w32 iZero a)
    J.Ifle pc' -> ifInstr pc pc' $ \a -> App (BVSle w32 a iZero)

    J.Tableswitch pc' lo _hi pcs ->
      do iPop >>= switchInstr pc' (zip [lo ..] pcs)
    J.Lookupswitch pc' table ->
      do iPop >>= switchInstr pc' table
    J.Goto pc' ->
      do vs <- get
         lbl <- lift $ processBlockAtPC pc' vs
         lift $ jump lbl
    J.Jsr _pc' -> sgFail "generateInstruction: jsr/ret not supported"
    J.Ret _idx -> sgFail "ret" --warning "jsr/ret not implemented"

    -- Method invocation and return instructions
    J.Invokevirtual (J.ClassType className) methodKey -> do
      ctx <- lift $ gets jsContext
      lift $ initializeClass ctx className
      handle <- getMethod className methodKey
      callJVMHandle handle

    -- TODO
    J.Invokevirtual   tp        _methodKey -> sgUnimplemented $ "Invokevirtual for " ++ show tp
    J.Invokeinterface _className _methodKey -> sgUnimplemented "Invokeinterface"
    
    J.Invokespecial   (J.ClassType methodClass) methodKey ->
      generateInstruction (pc, (J.Invokestatic methodClass methodKey))
      
    J.Invokespecial   tp _methodKey -> sgUnimplemented $ "Invokespecial for " ++ show tp
      
    J.Invokestatic    className methodKey
      -- don't run the constructor for the object class (we don't have this
      -- class information)
      | className == "java/lang/Object" && J.methodKeyName methodKey == "<init>" ->
        return ()

      | otherwise -> do
        -- make sure that *this* class has already been initialized
        ctx <- lift $ gets jsContext
        lift $ initializeClass ctx className
        handle <- getMethod className methodKey
        callJVMHandle handle
           
    J.Invokedynamic   _word16 -> sgUnimplemented "Invokedynamic"

    J.Ireturn -> returnInstr iPop
    J.Lreturn -> returnInstr lPop
    J.Freturn -> returnInstr fPop
    J.Dreturn -> returnInstr dPop
    J.Areturn -> returnInstr rPop
    J.Return  -> returnInstr (return (App EmptyApp)) 

    -- Other XXXXX
    J.Aconst_null ->
      do rPush rNull
    J.Arraylength ->
      do arrayRef <- rPop
         rawRef <- throwIfRefNull arrayRef
         obj <- lift $ readRef rawRef
         let uobj = App (UnrollRecursive knownRepr knownRepr obj)
         len <- lift $
           do k <- newLambdaLabel
              l1 <- newLambdaLabel
              l2 <- newLambdaLabel
              defineLambdaBlock l1 (\_ -> reportError (App (TextLit "arraylength")))
              defineLambdaBlock l2 (jumpToLambda k . arrayLength)
              let labels = Ctx.empty `Ctx.extend` l1 `Ctx.extend` l2
              continueLambda k (branchVariant uobj labels)
         iPush len
    J.Athrow ->
      do _objectRef <- rPop
         -- For now, we assert that exceptions won't happen
         lift $ reportError (App (TextLit "athrow"))
         --throwIfRefNull objectRef
         --throw objectRef
    J.Checkcast _tp ->
      do objectRef <- rPop
         () <- sgUnimplemented "checkcast" --assertTrueM (isNull objectRef ||| objectRef `hasType` tp) "java/lang/ClassCastException"
         rPush objectRef
    J.Iinc idx constant ->
      do value <- getLocal idx >>= lift . fromIValue
         let constValue = iConst (fromIntegral constant)
         setLocal idx (IValue (App (BVAdd w32 value constValue)))
    J.Instanceof _tp ->
      do _objectRef <- rPop
         sgUnimplemented "instanceof" -- objectRef `instanceOf` tp
    J.Monitorenter ->
      do void rPop
    J.Monitorexit ->
      do void rPop
    J.Nop ->
      do return ()

unary ::
  JVMStmtGen h s ret a ->
  (b -> JVMStmtGen h s ret ()) ->
  (a -> b) ->
  JVMStmtGen h s ret ()
unary pop push op =
  do value <- pop
     push (op value)

binary ::
  JVMStmtGen h s ret a ->
  JVMStmtGen h s ret b ->
  (c -> JVMStmtGen h s ret ()) ->
  (a -> b -> c) ->
  JVMStmtGen h s ret ()
binary pop1 pop2 push op =
  do value2 <- pop2
     value1 <- pop1
     push (value1 `op` value2)

createField :: J.Field -> JVMStmtGen h s ret (Expr JVM s StringType, Expr JVM s (MaybeType JVMValueType))
createField field = do
  let str = App (TextLit (fromString (J.fieldName field)))
  let val0 = defaultValue (J.fieldType field)
  expr <- lift $ toJVMDynamic (J.fieldType field) val0
  let val = App $ JustValue knownRepr expr
  return (str, val)

newInstanceInstr ::
  Expr JVM s JVMClassType
  -- ^ class data structure
  ->  [(Expr JVM s StringType, Expr JVM s (MaybeType JVMValueType))]
  -- ^ Field names and appropriate initial values
  ->  JVMStmtGen h s ret () 
newInstanceInstr cls objFields = do
    let strMap = foldr addField (App (EmptyStringMap dynRepr)) objFields
    let ctx    = Ctx.empty `Ctx.extend` strMap `Ctx.extend` cls
    let inst   = App (MkStruct knownRepr ctx)
    let uobj   = injectVariant Ctx.i1of2 inst
    let obj    = App (RollRecursive knownRepr knownRepr uobj)
    rawRef     <- lift $ newRef obj
    let ref    = App (JustValue knownRepr rawRef)
    rPush ref
  where
    dynRepr :: TypeRepr JVMValueType
    dynRepr  = knownRepr
    addField (f,i) fs = 
      App (InsertStringMapEntry dynRepr fs f i)

newarrayInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  -- type tag
  JVMInt s ->
  -- array size, must be nonnegative
  Expr JVM s t ->
  -- Initial value for array element
  JVMStmtGen h s ret ()
newarrayInstr tag count x =
  do let val = injectVariant tag x
     let vec = App (VectorReplicate knownRepr (App (BvToNat w32 count)) val)
     let ctx = Ctx.empty `Ctx.extend` count `Ctx.extend` vec
     let arr = App (MkStruct knownRepr ctx)
     let uobj = injectVariant Ctx.i2of2 arr
     let obj = App (RollRecursive knownRepr knownRepr uobj)
     rawRef <- lift $ newRef obj
     let ref = App (JustValue knownRepr rawRef)
     rPush ref

aloadInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> JVMValue s) ->
  JVMStmtGen h s ret ()
aloadInstr tag mkVal =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     let uobj = App (UnrollRecursive knownRepr knownRepr obj)
     let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
     arr <- lift $ assertedJustExpr marr "aload: not a valid array"
     let vec = App (GetStruct arr Ctx.i2of2 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (VectorGetEntry knownRepr vec (App (BvToNat w32 idx)))
     let mx = App (ProjectVariant knownRepr tag val)
     x <- lift $ assertedJustExpr mx "aload: invalid element type"
     pushValue (mkVal x)

astoreInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> Expr JVM s t) ->
  Expr JVM s t ->
  JVMStmtGen h s ret ()
astoreInstr tag f x =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     let uobj = App (UnrollRecursive knownRepr knownRepr obj)
     let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
     arr <- lift $ assertedJustExpr marr "astore: not a valid array"
     let vec = App (GetStruct arr Ctx.i2of2 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (InjectVariant knownRepr tag (f x))
     let vec' = App (VectorSetEntry knownRepr vec (App (BvToNat w32 idx)) val)
     let arr' = App (SetStruct knownRepr arr Ctx.i2of2 vec')
     let uobj' = App (InjectVariant knownRepr Ctx.i2of2 arr')
     let obj' = App (RollRecursive knownRepr knownRepr uobj')
     lift $ writeRef rawRef obj'

icmpInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMInt s -> JVMBool s) ->
  JVMStmtGen h s ret ()
icmpInstr pc_old pc_t cmp =
  do i2 <- iPop
     i1 <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i1 i2) pc_t pc_f

ifInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMBool s) ->
  JVMStmtGen h s ret ()
ifInstr pc_old pc_t cmp =
  do i <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i) pc_t pc_f

branchIf ::
  JVMBool s ->
  J.PC {- ^ true label -} ->
  J.PC {- ^ false label -} ->
  JVMStmtGen h s ret ()
branchIf cond pc_t pc_f =
  do vs <- get
     lbl_t <- lift $ processBlockAtPC pc_t vs
     lbl_f <- lift $ processBlockAtPC pc_f vs
     lift $ branch cond lbl_t lbl_f

switchInstr ::
  J.PC {- ^ default target -} ->
  [(Int32, J.PC)] {- ^ jump table -} ->
  JVMInt s {- ^ scrutinee -} ->
  JVMStmtGen h s ret ()
switchInstr def [] _ =
  do vs <- get
     lift $ processBlockAtPC def vs >>= jump
switchInstr def ((i, pc) : table) x =
  do vs <- get
     l <- lift $ processBlockAtPC pc vs
     let cond = App (BVEq w32 x (iConst (toInteger i)))
     lift $ whenCond cond (jump l)
     switchInstr def table x

returnInstr ::
  forall h s ret tp.
  KnownRepr TypeRepr tp =>
  JVMStmtGen h s ret (Expr JVM s tp) ->
  JVMStmtGen h s ret ()
returnInstr pop =
  do retType <- lift $ jsRetType <$> get
     case testEquality retType (knownRepr :: TypeRepr tp) of
       Just Refl -> pop >>= (lift . returnFromFunction)
       Nothing -> sgFail "ireturn: type mismatch"

----------------------------------------------------------------------
-- Basic Value Operations

charFromInt :: JVMInt s -> JVMInt s
charFromInt i = App (BVZext w32 w16 (App (BVTrunc w16 w32 i)))

floatFromDouble :: JVMDouble s -> JVMFloat s
floatFromDouble _ = error "floatFromDouble"

intFromDouble :: JVMDouble s -> JVMInt s
intFromDouble _ = error "intFromDouble"

longFromDouble :: JVMDouble s -> JVMLong s
longFromDouble _ = error "longFromDouble"

doubleFromFloat :: JVMFloat s -> JVMDouble s
doubleFromFloat _ = error "doubleFromFloat"

intFromFloat :: JVMFloat s -> JVMInt s
intFromFloat _ = error "intFromFloat"

longFromFloat :: JVMFloat s -> JVMLong s
longFromFloat _ = error "longFromFloat"

boolFromInt :: JVMInt s -> JVMInt s
boolFromInt _ = error "boolFromInt"

byteFromInt :: JVMInt s -> JVMInt s
byteFromInt i = App (BVSext w32 w8 (App (BVTrunc w8 w32 i)))

doubleFromInt :: JVMInt s -> JVMDouble s
doubleFromInt _ = error "doubleFromInt"

floatFromInt :: JVMInt s -> JVMFloat s
floatFromInt _ = error "floatFromInt"

longFromInt :: JVMInt s -> JVMLong s
longFromInt _ = error "longFromInt"

shortFromInt :: JVMInt s -> JVMInt s
shortFromInt i = App (BVSext w32 w16 (App (BVTrunc w16 w32 i)))

doubleFromLong :: JVMLong s -> JVMDouble s
doubleFromLong _ = error "doubleFromLong"

floatFromLong :: JVMLong s -> JVMFloat s
floatFromLong _ = error "floatFromLong"

intFromLong :: JVMLong s -> JVMInt s
intFromLong _ = error "intFromLong"

iConst :: Integer -> JVMInt s
iConst i = App (BVLit w32 i)

lConst :: Integer -> JVMLong s
lConst i = App (BVLit w64 i)

dConst :: Double -> JVMDouble s
dConst _ = error "dConst"

fConst :: Float -> JVMFloat s
fConst _ = error "fConst"

dAdd, dSub, dMul, dDiv, dRem :: JVMDouble s -> JVMDouble s -> JVMDouble s
dAdd = error "dAdd"
dSub = error "dAdd"
dMul = error "dAdd"
dDiv = error "dAdd"
dRem = error "dAdd"

dNeg :: JVMDouble s -> JVMDouble s
dNeg = error "dNeg"

fAdd, fSub, fMul, fDiv, fRem :: JVMFloat s -> JVMFloat s -> JVMFloat s
fAdd = error "dAdd"
fSub = error "dAdd"
fMul = error "dAdd"
fDiv = error "dAdd"
fRem = error "dAdd"

----------------------------------------------------------------------

-- | Given a JVM type and a type context and a register assignment,
-- peel off the rightmost register from the assignment, which is
-- expected to match the given LLVM type. Pass the register and the
-- remaining type and register context to the given continuation.
--
-- This procedure is used to set up the initial state of the registers
-- at the entry point of a function.
packTypes ::
  [J.Type] ->
  CtxRepr ctx ->
  Ctx.Assignment (Atom s) ctx ->
  [JVMValue s]
packTypes [] ctx _asgn
  | Ctx.null ctx = []
  | otherwise = error "packTypes: arguments do not match JVM types"
packTypes (t : ts) ctx asgn =
  jvmTypeAsRepr t $ \mkVal ctp ->
  case ctx of
    Ctx.Empty ->
      error "packTypes: arguments do not match JVM types"
    ctx' Ctx.:> ctp' ->
      case testEquality ctp ctp' of
        Nothing -> error $ unwords ["crucible type mismatch", show ctp, show ctp']
        Just Refl ->
          mkVal (AtomExpr (Ctx.last asgn)) : packTypes ts ctx' (Ctx.init asgn)
  where
    jvmTypeAsRepr ::
      J.Type ->
      (forall tp. (Expr JVM s tp -> JVMValue s) -> TypeRepr tp -> [JVMValue s]) ->
      [JVMValue s]
    jvmTypeAsRepr ty k =
      case ty of
        J.ArrayType _ -> k RValue (knownRepr :: TypeRepr JVMRefType)
        J.BooleanType -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.ByteType    -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.CharType    -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.ClassType _ -> k RValue (knownRepr :: TypeRepr JVMRefType)
        J.DoubleType  -> k DValue (knownRepr :: TypeRepr JVMDoubleType)
        J.FloatType   -> k FValue (knownRepr :: TypeRepr JVMFloatType)
        J.IntType     -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.LongType    -> k LValue (knownRepr :: TypeRepr JVMLongType)
        J.ShortType   -> k IValue (knownRepr :: TypeRepr JVMIntType)

initialJVMExprFrame ::
  J.ClassName ->
  J.Method ->
  CtxRepr ctx ->
  Ctx.Assignment (Atom s) ctx ->
  JVMExprFrame s
initialJVMExprFrame cn method ctx asgn = JVMFrame [] locals
  where
    args = J.methodParameterTypes method
    static = J.methodIsStatic method
    args' = if static then args else J.ClassType cn : args
    vals = reverse (packTypes (reverse args') ctx asgn)
    idxs = J.methodParameterIndexes method
    idxs' = if static then idxs else 0 : idxs
    locals = Map.fromList (zip idxs' vals)

----------------------------------------------------------------------

-- | Build the initial JVM generator state upon entry to the entry
-- point of a method.
initialState :: JVMContext -> J.Method -> TypeRepr ret -> JVMState ret s
initialState ctx method ret =
  JVMState {
    _jsLabelMap = Map.empty,
    _jsFrameMap = Map.empty,
    _jsCFG = methodCFG method,
    jsRetType = ret,
    jsContext = ctx
  }

methodCFG :: J.Method -> J.CFG
methodCFG method =
  case J.methodBody method of
    J.Code _ _ cfg _ _ _ _ -> cfg
    _                      -> error ("Method " ++ show method ++ " has no body")

generateMethod ::
  J.ClassName ->
  J.Method ->
  CtxRepr init ->
  Ctx.Assignment (Atom s) init ->
  JVMGenerator h s ret a
generateMethod cn method ctx asgn =
  do let cfg = methodCFG method
     let bbLabel bb = (,) (J.bbId bb) <$> newLabel
     lbls <- traverse bbLabel (J.allBBs cfg)
     jsLabelMap .= Map.fromList lbls
     bb0 <- maybe (jvmFail "no entry block") return (J.bbById cfg J.BBIdEntry)
     let vs0 = initialJVMExprFrame cn method ctx asgn
     rs0 <- newRegisters vs0
     generateBasicBlock bb0 rs0

{-
-- | Translate a single JVM method into a crucible CFG.
defineMethod ::
  JVMContext -> J.ClassName -> J.Method -> ST h (C.AnyCFG JVM)
defineMethod ctx cn method = do
  traceM $ "Defining entry method " ++ J.methodName method
  case Map.lookup (cn, J.methodKey method) (symbolMap ctx) of
    Nothing -> fail "internal error: Could not find method"
    Just (JVMHandleInfo _ (h :: FnHandle args ret)) ->
      do let argTypes = handleArgTypes h
         let retType  = handleReturnType h
         let def :: FunctionDef JVM h (JVMState ret) args ret
             def inputs = (s, f)
               where s = initialState ctx method retType
                     f = generateMethod cn method argTypes inputs
         (SomeCFG g, []) <- defineFunction InternalPos h def
         case toSSA g of
           C.SomeCFG g_ssa -> return (C.AnyCFG g_ssa)


-- | Translate a single JVM method into a crucible CFG, given a handle
-- for the function.  This version of the function produces a Crucible
-- FnBinding based on the CFG, which can then be used to register the
-- function for symbolic simulation.
defineMethod_CFG :: J.ClassName -> JVMContext -> JVMHandleInfo -> ST h (C.FnBinding p sym JVM)
defineMethod_CFG mcls ctx (JVMHandleInfo meth (h :: FnHandle args ret)) = do
  traceM $ "Defining method " ++ J.methodName meth ++ " in class " ++ J.unClassName mcls
  let argTypes = handleArgTypes h
  let retType  = handleReturnType h
  let def :: FunctionDef JVM h (JVMState ret) args ret
      def inputs = (s, f)
               where s = initialState ctx meth retType
                     f = generateMethod mcls meth argTypes inputs
  (SomeCFG g, []) <- defineFunction InternalPos h def
  case toSSA g of
    C.SomeCFG g_ssa -> return (C.FnBinding h (C.UseCFG g_ssa (C.postdomInfo g_ssa)))

-- | Produce an override for the method that will lazily define the CFG for the entire class
-- that contains the method
defineMethod_Override :: J.ClassName -> JVMContext -> JVMHandleInfo -> ST h (C.FnBinding p sym JVM)
defineMethod_Override mcls ctx (JVMHandleInfo meth (h :: FnHandle args ret)) = do
  let argTypes = handleArgTypes h
  let retType  = handleReturnType h
  undefined
-}

-- | Define a block with a fresh lambda label, returning the label.
defineLambdaBlockLabel ::
  (IsSyntaxExtension ext, KnownRepr TypeRepr tp) =>
  (forall a. Expr ext s tp -> Generator ext h s t ret a) ->
  Generator ext h s t ret (LambdaLabel s tp)
defineLambdaBlockLabel action =
  do l <- newLambdaLabel
     defineLambdaBlock l action
     return l

-----------------------------------------------------------------------------     

-- | The ClassTable is a map from class names to class instances
-- For now, the table is immutable (i.e. all classes must be known at compile time)
-- In the future, we may add a reference so that we can update the set of
-- classes tracked during simulation.

javaTypeToRepr :: J.Type -> Some TypeRepr
javaTypeToRepr t =
  case t of
    (J.ArrayType _) -> refRepr
    J.BooleanType   -> intRepr
    J.ByteType      -> intRepr
    J.CharType      -> intRepr
    (J.ClassType _) -> refRepr
    J.DoubleType    -> doubleRepr
    J.FloatType     -> floatRepr
    J.IntType       -> intRepr
    J.LongType      -> longRepr
    J.ShortType     -> intRepr
  where
    refRepr    = Some (knownRepr :: TypeRepr JVMRefType)
    intRepr    = Some (knownRepr :: TypeRepr JVMIntType)
    longRepr   = Some (knownRepr :: TypeRepr JVMLongType)
    doubleRepr = Some (knownRepr :: TypeRepr JVMDoubleType)
    floatRepr  = Some (knownRepr :: TypeRepr JVMFloatType)


{-
makeClassTable :: forall sym s. (IsExprBuilder sym) => sym
               -> HandleAllocator s
               -> [J.Class]
               -> ST s (C.RegValue sym JVMClassTableType)
makeClassTable sym halloc classes = do
   let classText c = fromString $ J.unClassName $ J.className c 
   let rv :: J.Class -> ST s (C.RegValue sym JVMClassType)
       rv cls = do 
          -- name of the class
          let nameval = undefined
          -- nameval <- W4.stringLit sym (classText cls)
           -- names of the static fields
          let staticFields = filter J.fieldIsStatic (J.classFields cls)              
          let names = map (fromString . J.fieldName) staticFields
          -- static fields are all reference cells that are uninitialized
          --freshRefs <- mapM (\ _ ->
          --               freshRefCell halloc (knownRepr :: TypeRepr JVMObjectType)) staticFields
                       
          let staticInitVals :: [W4.PartExpr (W4.Pred sym) (C.RegValue sym JVMValueType)]
              staticInitVals = map (\_ -> W4.maybePartExpr sym Nothing) staticFields
               {- map (C.injectVariant sym knownRepr tagR .
                                     W4.justPartExpr sym .
                                     C.toMuxTree sym) freshRefs -}

          let statics :: C.RegValue sym (StringMapType JVMValueType)
              statics = Map.fromList (zip names staticInitVals)
          return $ Ctx.empty `Ctx.extend` C.RV nameval -- `Ctx.extend` C.RV statics
   classData <- mapM rv classes
   return $ Map.fromList (zipWith (\c d -> (classText c,W4.justPartExpr sym d))
                                   classes
                                   classData)
-}

type StaticTable = Map (J.ClassName, String) (GlobalVar JVMValueType)


-- | Given the name of a class and the field name, define the name of the global variable
globalVarName :: J.ClassName -> String -> Text
globalVarName cn fn = fromString (J.unClassName cn ++ "." ++ fn)

accM :: (Monad m, Foldable t) => t a -> b -> (b -> a -> m b) ->  m b
accM d b f = foldM f b d




nullRegValue :: forall sym. (IsExprBuilder sym) => sym -> C.RegValue sym JVMValueType
nullRegValue sym = C.injectVariant sym knownRepr tagR (W4.maybePartExpr sym Nothing)


-----------------------------------------------------------------------------
-- | translateClass

type SymbolMap = Map (J.ClassName, J.MethodKey) JVMHandleInfo

data MethodTranslation = forall args ret. MethodTranslation
   { methodHandle :: FnHandle args ret
   , methodCCFG   :: C.SomeCFG JVM args ret
   }

-- Note the classname may not be the same one as the current class if this is
-- an inherited method(?). However, it is available for this class.
data ClassTranslation =
  ClassTranslation { cfgMap        :: Map (J.ClassName,J.MethodKey) MethodTranslation
                   , initCFG       :: C.AnyCFG JVM 
                   , _transContext :: JVMContext
                   }

-- left biased
instance Monoid ClassTranslation where
  mempty = ClassTranslation { cfgMap = Map.empty , initCFG = undefined, _transContext = mempty }
  mappend ct1 ct2 = ClassTranslation { cfgMap  = Map.union (cfgMap ct1) (cfgMap ct2)
                                     , initCFG = initCFG ct1 
                                     , _transContext = _transContext ct1 <> _transContext ct2
                                     }


transContext :: Simple Lens ClassTranslation JVMContext
transContext = lens _transContext (\s v -> s{ _transContext = v})


allParameterTypes :: J.Class -> J.Method -> [J.Type]
allParameterTypes c m
  | J.methodIsStatic m = J.methodParameterTypes m
  | otherwise = J.ClassType (J.className c) : J.methodParameterTypes m

-- | allocate a new method handle and add it to the SymbolMap
declareMethod :: HandleAllocator s -> J.Class -> SymbolMap -> J.Method ->  ST s SymbolMap
declareMethod halloc mcls ctx meth = do
   let args  = Ctx.fromList (map javaTypeToRepr (allParameterTypes mcls meth))
       ret   = maybe (Some C.UnitRepr) javaTypeToRepr (J.methodReturnType meth)
       cname = J.className mcls
       mkey  = J.methodKey meth
   case (args, ret) of
     (Some argsRepr, Some retRepr) -> do
       h <- mkHandle' halloc (fromString (J.methodName meth)) argsRepr retRepr
       return $ Map.insert (cname, mkey) (JVMHandleInfo meth h) ctx


-- | allocate the static fields and add it to the StaticTable
declareStaticField :: HandleAllocator s
    -> J.Class
    -> StaticTable
    -> J.Field
    -> ST s StaticTable
declareStaticField halloc c m f = do
  let cn = J.className c
  let fn = J.fieldName f
  let ty = J.fieldType f
  gvar <- C.freshGlobalVar halloc (globalVarName cn fn) (knownRepr :: TypeRepr JVMValueType)
  return $ (Map.insert (cn,fn) gvar m)

-- | Create the initial JVMContext
mkJVMContext :: HandleAllocator s -> J.Class -> ST s JVMContext
mkJVMContext halloc c = do
  sm <- foldM (declareMethod halloc c) Map.empty (J.classMethods c)
  st <- foldM (declareStaticField halloc c) Map.empty (J.classFields c)
  gv <- C.freshGlobalVar halloc (fromString "JVM_CLASS_TABLE") (knownRepr :: TypeRepr JVMClassTableType)
  return $ JVMContext
    { symbolMap         = sm
    , staticTable       = st
    , classTable        = Map.singleton (J.className c) c
    , dynamicClassTable = gv
    }


-- | Translate a single JVM method definition into a crucible CFG
translateMethod :: JVMContext
                -> J.Class
                -> J.Method
                -> ST s ((J.ClassName, J.MethodKey), MethodTranslation)
translateMethod ctx c m = do
  let cName = J.className c
  let mKey  = J.methodKey m
  traceM $ "translating " ++ J.unClassName cName ++ "/" ++ J.methodName m 
  case Map.lookup (cName,mKey) (symbolMap ctx)  of
    Just (JVMHandleInfo _ h)  -> 
      case (handleArgTypes h, handleReturnType h) of
        ((argTypes :: CtxRepr args), (retType :: TypeRepr ret)) -> do
          let  def :: FunctionDef JVM h (JVMState ret) args ret
               def inputs = (s, f)
                  where s = initialState ctx m retType
                        f = generateMethod cName m argTypes inputs
          (SomeCFG g, []) <- defineFunction InternalPos h def
          let g' = toSSA g
          --traceM $ show g'
          return ((cName,mKey), MethodTranslation h g')
    Nothing -> fail $ "internal error: Could not find method " ++ show mKey

------------------------------------------------------------------------
-- | initMemProc
--
-- make sure that we have added the class table to the global environment

--initStaticField :: J.Field -> GlobalVar (JVMValue s) -> JVMStmtGen h s ret ()
--initStaticField f gvar =
  


initCFGProc :: HandleAllocator s
            -> JVMContext
            -> ST s (C.AnyCFG JVM)
initCFGProc halloc ctx = do
   h <- mkHandle halloc "class_table_init"
   let gv = dynamicClassTable ctx
   let meth = undefined
       def :: FunctionDef JVM s (JVMState UnitType) EmptyCtx UnitType
       def _inputs = (s, f)
              where s = initialState ctx meth knownRepr
                    f = do writeGlobal gv (App $ EmptyStringMap knownRepr)
                           return (App EmptyApp)
                    
   (SomeCFG g,[]) <- defineFunction InternalPos h def
   case toSSA g of
     C.SomeCFG g' -> return $! C.AnyCFG g'


translateClass :: HandleAllocator s -- ^ Generator for nonces
               -> J.Class           -- ^ Class to translate
               -> ST s ClassTranslation
translateClass halloc c = do
  
  -- create initial context, declaring the statically known methods and fields.
  ctx <- mkJVMContext halloc c

  let methods = J.classMethods c
  
  -- translate methods
  pairs <- mapM (translateMethod ctx c) (J.classMethods c)

  -- initialization code
  initCFG0 <- initCFGProc halloc ctx

  -- return result
  return $ ClassTranslation { cfgMap        = Map.fromList pairs
                            , initCFG       = initCFG0
                            , _transContext = ctx
                            }

