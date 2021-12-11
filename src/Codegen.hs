--  File     : Codegen.hs
--  Author   : Ashutosh Rishi Ranjan
--  Purpose  : Generate and emit LLVM from basic blocks of a module
--  Copyright: (c) 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Codegen (
  Codegen(..), CodegenState(..), BlockState(..), Translation,
  emptyModule, evalCodegen, addExtern, addGlobalConstant, getGlobalResource,
  execCodegen, emptyCodegen, evalTranslation, getCount, putCount,
  -- * Blocks
  createBlocks, setBlock, addBlock, entryBlockName,
  callWybe, callC, externf, ret, globalDefine, externalC, externalWybe,
  phi, br, cbr, getBlock, retNothing, fresh,
  -- * Symbol storage
  alloca, store, local, assign, load, getVar, localVar, preservingSymtab,
  makeGlobalResourceVariable,
  operandType, doAlloca, doLoad, 
  bitcast, cbitcast, inttoptr, cinttoptr, ptrtoint, cptrtoint,
  trunc, ctrunc, zext, czext, sext, csext,
  -- * Types
  int_t, phantom_t, float_t, char_t, ptr_t, void_t, string_t, array_t,
  struct_t, address_t, byte_ptr_t,
  -- * Custom Types
  int_c, float_c,
  -- * Instructions
  instr, namedInstr, voidInstr,
  iadd, isub, imul, idiv, fadd, fsub, fmul, fdiv, sdiv, urem, srem, frem,
  cons, uitofp, sitofp, fptoui, fptosi,
  icmp, fcmp, lOr, lAnd, lXor, shl, lshr, ashr,
  constInttoptr,
  -- * Structure instructions
  insertvalue, extractvalue,
  -- * GetElementPtr
  getElementPtrInstr

  -- * Testing

  ) where

import           Data.Function
import           Data.List
import qualified Data.Map                        as Map
import           Data.Maybe                      (fromMaybe)
import           Data.String
import           Data.Word

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Extra             (whenM)
import           Control.Monad.State

import           LLVM.AST
import qualified LLVM.AST                        as LLVMAST
import           LLVM.AST.Global
import qualified LLVM.AST.Global                 as G

import           LLVM.AST.AddrSpace
import qualified LLVM.AST.Attribute              as A
import qualified LLVM.AST.CallingConvention      as CC
import qualified LLVM.AST.Constant               as C
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.IntegerPredicate       as IP

import           AST                             hiding (Stmt(..))
import           LLVM.Context
import           LLVM.Module
import           Options                         (LogSelection (Blocks,Codegen))
import           Config                          (wordSize, functionDefSection)
import           Unsafe.Coerce
import           Debug.Trace
import LLVM.AST.Linkage (Linkage(ExternWeak, External))

----------------------------------------------------------------------------
-- Types                                                                  --
----------------------------------------------------------------------------

int_t :: Type
int_t = IntegerType 32

ptr_t :: Type -> Type
ptr_t ty = PointerType ty (AddrSpace 0)

phantom_t :: Type
phantom_t = VoidType

string_t :: Word64 -> Type
string_t size = ArrayType size char_t

void_t :: Type
void_t = VoidType

float_t :: Type
float_t = FloatingPointType DoubleFP

char_t :: Type
char_t = IntegerType 8

array_t :: Word64 -> Type -> Type
array_t = ArrayType

struct_t :: [LLVMAST.Type] -> LLVMAST.Type
struct_t types = LLVMAST.StructureType False types

address_t :: Type
address_t = int_c $ fromIntegral wordSize

byte_ptr_t :: Type
byte_ptr_t = ptr_t char_t

-- Custom Types
int_c :: Word32 -> Type
int_c = IntegerType

float_c :: Word32 -> Type
float_c 16  = FloatingPointType HalfFP
float_c 32  = FloatingPointType FloatFP
float_c 64  = FloatingPointType DoubleFP
float_c 128 = FloatingPointType FP128FP
float_c 80  = FloatingPointType X86_FP80FP
float_c n   = error $ "Invalid floating point width " ++ show n


----------------------------------------------------------------------------
-- Codegen State                                                          --
----------------------------------------------------------------------------
-- | 'SymbolTable' is a simple mapping of scope variable names and their
-- representation as an LLVM.AST.Operand.Operand.


-- | A Map of all the assigned names to assist in supplying new unique names.
type Names = Map.Map String Int


-- | 'CodegenState' will hold a global Definition level code.
data CodegenState
    = CodegenState {
        currentBlock  :: Name     -- ^ Name of the active block to append to
      , blocks        :: Map.Map Name BlockState 
                                  -- ^ Blocks for function
      , symtab        :: Map.Map String (Operand,TypeRepresentation) 
                                  -- ^ Local symbol table of a function
      , blockCount    :: Int      -- ^ Incrementing count of basic blocks
      , count         :: Word     -- ^ Count for temporary operands
      , names         :: Names    -- ^ Name supply
      , externs       :: [Prim]   -- ^ Primitives which need to be declared
      , globalVars    :: [Global] -- ^ Needed global variables/constants
      , resources     :: Map.Map ResourceSpec Global
                                  -- ^ Needed global variables for resources
      , modProtos     :: [PrimProto] 
                                  -- ^ Module procedures prototypes
      } deriving Show

-- | 'BlockState' will generate the code for basic blocks inside of
-- function definitions.
-- A LLVM function consists of a sequence of basic blocks containing a
-- stack of Named/Unnamed instructions. During compilation basic blocks
-- will roughly correspond to labels in the native assembly output.
data BlockState
    = BlockState {
        idx   :: Int -- ^ Block
      , stack :: [Named Instruction]
      , term  :: Maybe (Named Terminator)
      } deriving Show


-- | The 'Codegen' state monad will hold the state of the code generator
-- That is, a map of block names to their 'BlockState' representation
-- newtype Codegen a = Codegen { runCodegen :: StateT CodegenState Compiler a }
--     deriving (Functor, Applicative, Monad, MonadState CodegenState)

type Codegen = StateT CodegenState Compiler

execCodegen :: Word -> [PrimProto] -> Codegen a 
            -> Compiler CodegenState
execCodegen startCount protos codegen =
    execStateT codegen (emptyCodegen startCount protos)

evalCodegen :: [PrimProto] -> Codegen t -> Compiler t
evalCodegen protos codegen = evalStateT codegen (emptyCodegen 0 protos)

type Translation = StateT Word Compiler

evalTranslation :: Word -> Translation a -> Compiler a
evalTranslation = flip evalStateT

getCount :: Translation Word
getCount = get

putCount :: Word -> Translation ()
putCount = put

-- | Gets a new incremental word suffix for a temporary local operands
fresh :: Codegen Word
fresh = do
  ix <- gets count
  modify $ \s -> s { count = 1 + ix }
  return (ix + 1)

-- | Update the list of externs which will be needed. The 'Prim' will be
-- converted to an extern declaration later.
addExtern :: Prim -> Codegen ()
addExtern p =
    do ex <- gets externs
       modify $ \s -> s { externs = p : ex }
       return ()

-- | Creates a Global value for a constant, given the type and appends it
-- to the CodegenState list. This list will be used to convert these Global
-- values into Global module level definitions. A UnName is generated too
-- for reference.
addGlobalConstant :: LLVMAST.Type -> C.Constant -> Codegen Name
addGlobalConstant ty con =
    do modName <- lift $ fmap showModSpec getModuleSpec
       gs <- gets globalVars
       n <- fresh
       let ref = Name $ fromString $ modName ++ "." ++ show n
       let gvar = globalVariableDefaults { name = ref
                                         , isConstant = True
                                         , G.type' = ty
                                         , initializer = Just con }
       modify $ \s -> s { globalVars = gvar : gs }
       return ref


getGlobalResource :: ResourceSpec -> Type -> Codegen Operand
getGlobalResource spec@(ResourceSpec mod nm) ty = do
    ress <- gets resources
    nm <- case Map.lookup spec ress of
            Nothing -> do
                global <- lift $ makeGlobalResourceVariable spec ty
                modify $ \s -> s { resources = Map.insert spec global ress }
                return $ G.name global
            Just ref -> return $ G.name ref
    return $ ConstantOperand $ C.GlobalReference (ptr_t ty) nm


makeGlobalResourceVariable :: ResourceSpec -> Type -> Compiler Global
makeGlobalResourceVariable spec@(ResourceSpec mod nm) ty = do
    unless (ty /= VoidType) 
        $ shouldnt $ "global resource " ++ show spec ++ " cant have voidtype"
    let ref = Name $ fromString $ makeGlobalResourceName spec 
    thisMod <- getModuleSpec 
    let (linkage, init) = if thisMod == mod
                          then (External, Just $ C.Undef ty)
                          else (External, Nothing)
    return globalVariableDefaults { name = ref
                                  , isConstant = False
                                  , G.type' = ty
                                  , G.linkage = linkage
                                  , initializer = init
                                  }

-- | Create an empty LLVMAST.Module which would be converted into
-- LLVM IR once the moduleDefinitions field is filled.
emptyModule :: String -> LLVMAST.Module
emptyModule label = defaultModule { moduleName = fromString label }


-- | Create a global Function Definition to store in the LLVMAST.Module.
-- A Definition body is a list of BasicBlocks. A LPVM procedure roughly
-- correspond to this global function definition.  isForeign means the
-- function will be called from foreign code, so it should use C calling
-- conventions.
globalDefine :: Bool -> Type -> String -> [(Type, Name)]
             -> [BasicBlock] -> Definition
globalDefine isForeign rettype label argtypes body
             = GlobalDefinition $ functionDefaults {
                 G.callingConvention = if isForeign then CC.C else CC.Fast
               , name = Name $ fromString label
               , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes],
                               False)
               , returnType = rettype
               , basicBlocks = body
               , section = fromString <$> functionDefSection label
               }


-- | create a global declaration of an external function for the specified
-- calling convention
externalFunction :: CC.CallingConvention -> Type -> String -> [(Type, Name)]
                 -> Definition
externalFunction cconv rettype label argtypes
    = GlobalDefinition $ functionDefaults {
        G.callingConvention = cconv
      , name = Name $ fromString label
      , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes], False)
      , returnType = rettype
      , basicBlocks = []
      }


-- | 'externalC' creates a global declaration of an external C function
externalC :: Type -> String -> [(Type, Name)] -> Definition
externalC = externalFunction CC.C


-- | 'externalC' creates a global declaration of an external C function
externalWybe :: Type -> String -> [(Type, Name)] -> Definition
externalWybe = externalFunction CC.Fast


----------------------------------------------------------------------------
-- Blocks                                                                 --
----------------------------------------------------------------------------

entry :: Codegen Name
entry = gets currentBlock

-- | Sample name for the 'entry' block. (Usually 'entry')
entryBlockName :: String
entryBlockName = "entry"

-- | Initializes an empty new block
emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing

-- | Initialize an empty CodegenState for a new Definition.
emptyCodegen :: Word -> [PrimProto] -> CodegenState
emptyCodegen startCount =
  CodegenState
    (Name $ fromString entryBlockName)
    Map.empty
    Map.empty
    1
    startCount
    Map.empty
    []
    []
    Map.empty

-- | 'addBlock' creates and adds a new block to the current blocks
addBlock :: String -> Codegen Name
addBlock bname = do
  -- Retrieving the current field values
  blks <- gets blocks
  ix <- gets blockCount
  ns <- gets names
  let new = emptyBlock ix
      (qname, supply) = uniqueName bname ns
  -- updating with new block appended
  modify $ \s -> s { blocks = Map.insert (Name $ fromString qname) new blks
                   , blockCount = ix + 1
                   , names = supply
                   }
  return (Name $ fromString qname)

-- | Set the current block label.
setBlock :: Name -> Codegen Name
setBlock bname =
    do modify $ \s -> s { currentBlock = bname }
       return bname

-- | Get the current block being written to.
getBlock :: Codegen Name
getBlock = gets currentBlock


-- | Replace the current block with a 'new' block
modifyBlock :: BlockState -> Codegen ()
modifyBlock new = do
  active <- gets currentBlock
  modify $ \s -> s { blocks = Map.insert active new (blocks s) }


-- | Find the current block in the list of blocks (Map of blocks)
current :: Codegen BlockState
current = do
  curr <- gets currentBlock
  blks <- gets blocks
  case Map.lookup curr blks of
    Just x  -> return x
    Nothing -> error $ "No such block found: " ++ show curr


-- | Generate the list of BasicBlocks added to the CodegenState for a global
-- definition. This list would be in order of execution. This list forms the
-- body of a global function definition.
createBlocks :: CodegenState -> [BasicBlock]
createBlocks m = map makeBlock $ sortBlocks $ Map.toList (blocks m)

-- | Convert our BlockState to the LLVM BasicBlock Type.
makeBlock :: (Name, BlockState) -> BasicBlock
makeBlock (l, (BlockState _ s t)) = BasicBlock l s (maketerm t)
  where
    maketerm (Just x) = x
    maketerm Nothing  = error $ "Block has no terminator: " ++ (show l)

-- | Sort the blocks on their ids. Blocks do get out of order since any block
-- can be brought to be the 'currentBlock'.
sortBlocks :: [(Name, BlockState)] -> [(Name, BlockState)]
sortBlocks = sortBy (compare `on` (idx . snd))

----------------------------------------------------------------------------
-- Names supply                                                           --
----------------------------------------------------------------------------

-- | 'uniqueName' checks a name supply to generate a unique name by
-- adding a number suffix (which is incremental) to a name which has already
-- been used.
uniqueName :: String -> Names -> (String, Names)
uniqueName nm ns =
    case Map.lookup nm ns of
      Nothing -> (nm, Map.insert nm 1 ns)
      Just ix -> (nm ++ show ix, Map.insert nm (ix + 1) ns)


----------------------------------------------------------------------------
-- Name Referencing                                                       --
----------------------------------------------------------------------------

-- | Create an extern referencing Operand
externf :: Type -> Name -> Operand
externf ty = ConstantOperand . C.GlobalReference ty

-- | Create a new Local Operand (prefixed with % in LLVM)
localVar :: Type -> String -> Operand
localVar t s = LocalReference t $ LLVMAST.Name $ fromString s


local :: Type -> LLVMAST.Name -> Operand
local ty nm = LocalReference ty nm

globalVar :: Type -> String -> C.Constant
globalVar t s = C.GlobalReference t $ LLVMAST.Name $ fromString s

----------------------------------------------------------------------------
-- Symbol Table                                                           --
----------------------------------------------------------------------------

-- | Store a local variable on the front of the symbol table.
assign :: String -> Operand -> TypeRepresentation -> Codegen ()
assign var op trep = do
    logCodegen $ "SYMTAB: " ++ var ++ " <- " ++ show op ++ ":" ++ show trep
    modify $ \s -> s { symtab = Map.insert var (op,trep) $ symtab s }


-- | Find and return the local operand by its given name from the symbol
-- table. Only the first find will be returned so new names can shadow
-- the same older names.
getVar :: String -> Codegen (Operand,TypeRepresentation)
getVar var = do
    let err = shouldnt $ "Local variable not in scope: " ++ show var
    lcls <- gets symtab
    return $ fromMaybe err $ Map.lookup var lcls


-- | Evaluate nested code generating code, and reset the symtab to its original
-- state afterwards. Other parts of the Codegen state are allowed to change.
-- This is needed when generating a branch, because symtabs in one branch won't
-- apply an another branch.
preservingSymtab :: Codegen a -> Codegen a
preservingSymtab code = do
    oldSymtab <- gets symtab
    result <- code
    modify $ \s -> s { symtab = oldSymtab }
    return result



-- | Look inside an operand and determine it's type.
operandType :: Operand -> Type
operandType (LocalReference ty _) = ty
operandType (ConstantOperand cons) =
    case cons of
        C.Int bs _ -> int_c bs
        C.Float _ -> float_t
        C.Null ty -> ty
        C.GlobalReference ty _ -> ty
        C.GetElementPtr _ (C.GlobalReference ty _) _ -> ty
        C.IntToPtr _ ty -> ty
        C.PtrToInt _ ty -> ty
        C.Undef ty -> ty
        _ -> shouldnt $ "Not a recognised constant operand: " ++ show cons
operandType _ = void_t


----------------------------------------------------------------------------
-- Instructions                                                           --
----------------------------------------------------------------------------

-- | Append a named instruction into the instruction stack of the current
-- BasicBlock. This action also produces a Operand value of the given type (this
-- will be the result type of performing that instruction).
namedInstr :: Type -> String -> Instruction -> Codegen Operand
namedInstr ty nm ins = do
    -- lpvm allows variables in different forks(blocks) have the same name,
    -- but llvm doesn't. So the block id is attached to the variable name to
    -- make it unique.
    blockId <- idx <$> current
    let ref = Name $ fromString $ specialName2 (show blockId) nm
    addInstr $ ref := ins
    return $ local ty ref


-- | Append an unnamed instruction to the instruction stack of the current
-- BasicBlock. The temp name is generated using a fresh word counter.
instr :: Type -> Instruction -> Codegen Operand
instr ty ins = do
    ref <- UnName <$> fresh
    addInstr $ ref := ins
    return $ local ty ref


-- | Append a void instruction to the instruction stack of the current
-- BasicBlock.
voidInstr :: Instruction -> Codegen ()
voidInstr inst = addInstr $ Do inst


-- | Append an instruction to the instruction stack of the current BasicBlock.
addInstr :: Named Instruction -> Codegen ()
addInstr namedIns = do
       blk <- current
       let i = stack blk
       modifyBlock $ blk { stack = i ++ [namedIns] }
       logCodegen $ "add instruction " ++ show namedIns


-- | 'terminator' provides the last instruction of a basic block.
terminator :: Named Terminator -> Codegen (Named Terminator)
terminator trm = do
  blk <- current
  modifyBlock $ blk { term = Just trm }
  return trm


-- * Integer arithmetic operations (Binary)

iadd :: Operand -> Operand -> Instruction
iadd a b = Add False False a b []

isub :: Operand -> Operand -> Instruction
isub a b = Sub False False a b []

imul :: Operand -> Operand -> Instruction
imul a b = Mul False False a b []

idiv :: Operand -> Operand -> Instruction
idiv a b = UDiv True a b []

sdiv :: Operand -> Operand -> Instruction
sdiv a b = SDiv True a b []

urem :: Operand -> Operand -> Instruction
urem a b = URem a b []

srem :: Operand -> Operand -> Instruction
srem a b = SRem a b []

-- * Floating point arithmetic operations (Binary)

fadd :: Operand -> Operand -> Instruction
fadd a b = FAdd noFastMathFlags a b []

fsub :: Operand -> Operand -> Instruction
fsub a b = FSub noFastMathFlags a b []

fmul :: Operand -> Operand -> Instruction
fmul a b = FMul noFastMathFlags a b []

fdiv :: Operand -> Operand -> Instruction
fdiv a b = FDiv noFastMathFlags a b []

frem :: Operand -> Operand -> Instruction
frem a b = FRem noFastMathFlags a b []

-- * Bitwise Binary Operations
shl :: Operand -> Operand -> Instruction
shl a b = Shl False False a b []

lshr :: Operand -> Operand -> Instruction
lshr a b = LShr False a b []

ashr :: Operand -> Operand -> Instruction
ashr a b = AShr False a b []

lOr :: Operand -> Operand -> Instruction
lOr a b = Or a b []

lAnd :: Operand -> Operand -> Instruction
lAnd a b = And a b []

lXor :: Operand -> Operand -> Instruction
lXor a b = Xor a b []


-- * Comparisions

fcmp :: FP.FloatingPointPredicate -> Operand -> Operand -> Instruction
fcmp p a b = FCmp p a b []

icmp :: IP.IntegerPredicate -> Operand -> Operand -> Instruction
icmp p a b = ICmp p a b []

-- * Unary

uitofp :: Operand -> Type -> Instruction
uitofp a ty = UIToFP a ty []

sitofp :: Operand -> Type -> Instruction
sitofp a ty = SIToFP a ty []

fptoui :: Operand -> Type -> Instruction
fptoui a ty = FPToUI a ty []

fptosi :: Operand -> Type -> Instruction
fptosi a ty = FPToSI a ty []

-- | Create a constant operand (function parameters).
cons :: C.Constant -> Operand
cons = ConstantOperand

-- * Memory effecting instructions

-- | The 'call' instruction represents a simple function call to wybe code
callWybe :: Operand -> [Operand] -> Instruction
callWybe fn args = Call (Just Tail) CC.Fast [] (Right fn) (toArgs args) [] []

-- | A foreign call instruction, using C calling conventions
callC :: Operand -> [Operand] -> Instruction
callC fn args = Call (Just Tail) CC.C [] (Right fn) (toArgs args) [] []


toArgs :: [Operand] -> [(Operand, [A.ParameterAttribute])]
toArgs xs = map (\x -> (x, [])) xs


-- | The ‘alloca‘ function wraps LLVM's alloca instruction. The 'alloca'
-- instruction is pushed on the instruction stack (unnamed) and referenced with
-- a *type operand.  The Alloca LLVM instruction allocates memory on the stack
-- frame of the currently executing function, to be automatically released when
-- this function returns to its caller.
alloca :: Type -> Instruction
alloca ty = Alloca ty Nothing 0 []

-- | The 'store' instruction is used to write to write to memory. yields void.
store :: Operand -> Operand -> Codegen ()
store ptr val = voidInstr $ Store False ptr val Nothing 0 []

-- | The 'load' function wraps LLVM's load instruction with defaults.
load :: Operand -> Instruction
load ptr = Load False ptr Nothing 0 []


bitcast :: Operand -> LLVMAST.Type -> Codegen Operand
bitcast op ty = instr ty $ BitCast op ty []

cbitcast :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
cbitcast op ty = return $ C.BitCast op ty

inttoptr :: Operand -> LLVMAST.Type -> Codegen Operand
inttoptr op ty = instr ty $ IntToPtr op ty []

cinttoptr :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
cinttoptr op ty = return $ C.IntToPtr op ty

ptrtoint :: Operand -> LLVMAST.Type -> Codegen Operand
ptrtoint op ty = instr ty $ PtrToInt op ty []

cptrtoint :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
cptrtoint op ty = return $ C.PtrToInt op ty

-- constBitcast :: Operand -> LLVMAST.Type -> Operand
-- constBitcast (ConstantOperand c) ty =  cons $ C.BitCast c ty

constInttoptr :: C.Constant -> LLVMAST.Type -> Operand
constInttoptr c ty = cons $ C.IntToPtr c ty

-- constPtrtoint :: Operand -> LLVMAST.Type -> Operand
-- constPtrtoint (ConstantOperand c) ty = cons $ C.PtrToInt c ty

trunc :: Operand -> LLVMAST.Type -> Codegen Operand
trunc op ty = instr ty $ Trunc op ty []

ctrunc :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
ctrunc op ty = return $ C.Trunc op ty

zext :: Operand -> LLVMAST.Type -> Codegen Operand
zext op ty = instr ty $ ZExt op ty []

czext :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
czext op ty = return $ C.ZExt op ty

sext :: Operand -> LLVMAST.Type -> Codegen Operand
sext op ty = instr ty $ SExt op ty []

csext :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
csext op ty = return $ C.SExt op ty


-- Helpers for allocating, storing, loading
doAlloca :: Type -> Codegen Operand
doAlloca (PointerType ty _) = instr (ptr_t ty) $ Alloca ty Nothing 0 []
doAlloca ty                 = instr (ptr_t ty) $ Alloca ty Nothing 0 []

doLoad :: Type -> Operand -> Codegen Operand
doLoad ty ptr = instr ty $ Load False ptr Nothing 0 []


-- * Structure operations
insertvalue :: Operand -> Operand -> Word32 -> Instruction
insertvalue st op i = InsertValue st op [i] []

extractvalue :: Operand -> Word32 -> Instruction
extractvalue st i = ExtractValue st [i] []


-- * GetElementPtr helper
getElementPtrInstr :: Operand -> [Integer] -> LLVMAST.Instruction
getElementPtrInstr op idxs = 
  LLVMAST.GetElementPtr False op (cons . C.Int (fromIntegral wordSize) <$> idxs) []


-- * Control Flow operations

br :: Name -> Codegen (Named Terminator)
br val = terminator $ Do $ Br val []

cbr :: Operand -> Name -> Name -> Codegen (Named Terminator)
cbr cond tr fl = terminator $ Do $ CondBr cond tr fl []

ret :: Maybe Operand -> Codegen (Named Terminator)
ret val = terminator $ Do $ Ret val []

retNothing :: Codegen (Named Terminator)
retNothing = terminator $ Do $ Ret Nothing []

phi :: Type -> [(Operand, Name)] -> Codegen Operand
phi ty incoming = instr ty $ Phi ty incoming []


logCodegen :: String -> Codegen ()
logCodegen s = lift $ logMsg Codegen s
