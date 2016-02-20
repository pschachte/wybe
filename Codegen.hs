-- File    : Codegen.hs
-- RCS     : $Id$
-- Author  : Ashutosh Rishi Ranjan
-- Purpose : Generate and emit LLVM from basic blocks of a module

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Codegen (
  Codegen(..), CodegenState(..), BlockState(..),
  emptyModule, evalCodegen, addExtern, addGlobalConstant,
  execCodegen,
  -- * Blocks
  createBlocks, setBlock, addBlock, entryBlockName,
  call, externf, ret, globalDefine, external, phi, br, cbr,
  getBlock, retNothing,
  -- * Symbol storage
  alloca, store, local, assign, load, getVar, getVarMaybe, localVar,
  operandType, doAlloca, doLoad,
  -- * Types
  int_t, phantom_t, float_t, char_t, ptr_t, void_t, string_t, array_t,
  struct_t,
  -- * Custom Types
  int_c, float_c,
  -- * Instructions
  instr, namedInstr,
  iadd, isub, imul, idiv, fadd, fsub, fmul, fdiv, sdiv,
  cons, uitofp, fptoui, icmp, fcmp, lOr, lAnd, lXor,
  -- * Structure instructions
  insertvalue, extractvalue

  -- * Testing

  ) where

import           Data.Function
import           Data.List
import qualified Data.Map                                as Map
import           Data.String
import           Data.Word

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.State

import           LLVM.General.AST
import qualified LLVM.General.AST                        as LLVMAST
import           LLVM.General.AST.Global
import qualified LLVM.General.AST.Global                 as G

import           LLVM.General.AST.AddrSpace
import qualified LLVM.General.AST.Attribute              as A
import qualified LLVM.General.AST.CallingConvention      as CC
import qualified LLVM.General.AST.Constant               as C
import qualified LLVM.General.AST.FloatingPointPredicate as FP
import qualified LLVM.General.AST.IntegerPredicate       as IP

import           AST                                     (Prim, PrimProto, Compiler)
import           LLVM.General.Context
import           LLVM.General.Module


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
float_t = FloatingPointType 64 IEEE

char_t :: Type
char_t = IntegerType 8

array_t :: Word64 -> Type -> Type
array_t = ArrayType

struct_t :: [LLVMAST.Type] -> LLVMAST.Type
struct_t types = LLVMAST.StructureType False types

-- Custom Types
int_c :: Word32 -> Type
int_c = IntegerType

float_c :: Word32 -> Type
float_c b = FloatingPointType b IEEE


----------------------------------------------------------------------------
-- Codegen State                                                          --
----------------------------------------------------------------------------
-- | 'SymbolTable' is a simple mapping of scope variable names and their
-- representation as an LLVM.General.AST.Operand.Operand.
type SymbolTable = [(String, Operand)]

-- | A Map of all the assigned names to assist in supllying new unique names.
type Names = Map.Map String Int


-- | 'CodegenState' will hold a global Definition level code.
data CodegenState
    = CodegenState {
        currentBlock :: Name     -- ^ Name of the active block to append to
      , blocks       :: Map.Map Name BlockState -- ^ Blocks for function
      , symtab       :: SymbolTable -- ^ Local symbol table of a function
      , blockCount   :: Int      -- ^ Incrementing count of basic blocks
      , count        :: Word     -- ^ Count for temporary operands
      , names        :: Names    -- ^ Name supply
      , externs      :: [Prim]   -- ^ Primitives which need to be declared
      , globalVars   :: [Global] -- ^ Needed global variables/constants
      , modProtos    :: [PrimProto] -- ^ Module procedures prototypes
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

execCodegen :: [PrimProto] -> Codegen a -> Compiler CodegenState
execCodegen modProtos codegen =
    execStateT codegen (emptyCodegen modProtos)

evalCodegen :: [PrimProto] -> Codegen t -> Compiler t
evalCodegen modProtos codegen =
    evalStateT codegen (emptyCodegen modProtos)

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
    do gs <- gets globalVars
       n <- fresh
       let ref = UnName n
       let gvar = globalVariableDefaults { name = ref
                                         , isConstant = True
                                         , G.type' = ty
                                         , initializer = Just con }
       modify $ \s -> s { globalVars = gvar : gs }
       return ref

-- | Create an empty LLVMAST.Module which would be converted into
-- LLVM IR once the moduleDefinitions field is filled.
emptyModule :: String -> LLVMAST.Module
emptyModule label = defaultModule { moduleName = label }


-- | Create a global Function Definition to store in the LLVMAST.Module.
-- A Definition body is a list of BasicBlocks. A LPVM procedure roughly
-- correspond to this global function definition.
globalDefine :: Type -> String -> [(Type, Name)] -> [BasicBlock] -> Definition
globalDefine rettype label argtypes body
             = GlobalDefinition $ functionDefaults {
                 name = Name label
               , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes],
                               False)
               , returnType = rettype
               , basicBlocks = body
               }

-- | 'external' creates a global declaration of an external function
external :: Type -> String -> [(Type, Name)] -> Definition
external rettype label argtypes
    = GlobalDefinition $ functionDefaults {
        name = Name label
      , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes], False)
      , returnType = rettype
      , basicBlocks = []
      }


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
emptyCodegen :: [PrimProto] -> CodegenState
emptyCodegen modProtos
    = CodegenState (Name entryBlockName)
      Map.empty [] 1 0 Map.empty [] [] modProtos

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
  modify $ \s -> s { blocks = Map.insert (Name qname) new blks
                   , blockCount = ix + 1
                   , names = supply
                   }
  return (Name qname)

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
    Just x -> return x
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
    maketerm Nothing = error $ "Block has no terminator: " ++ (show l)

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
externf ty = ConstantOperand . (C.GlobalReference ty)

-- | Create a new Local Operand (prefixed with % in LLVM)
localVar :: Type -> String -> Operand
localVar t s =  (LocalReference t ) $ LLVMAST.Name s

local :: Type -> LLVMAST.Name -> Operand
local ty nm = LocalReference ty nm

----------------------------------------------------------------------------
-- Symbol Table                                                           --
----------------------------------------------------------------------------

-- | Store a local variable on the front of the symbol table.
assign :: String -> Operand -> Codegen ()
assign var x = do
  lcls <- gets symtab
  modify $ \s -> s { symtab = (var, x) : lcls }

-- | Find and return the local operand by its given name from the symbol
-- table. Only the first find will be returned so new names can shadow
-- the same older names.
getVar :: String -> Codegen Operand
getVar var = do
  lcls <- gets symtab
  case lookup var lcls of
    Just x -> return x
    Nothing -> error $ "Local variable not in scope: " ++ show var

getVarMaybe :: String -> Codegen (Maybe Operand)
getVarMaybe var = do
  lcls <- gets symtab
  return $ lookup var lcls 


-- | Look inside an operand and determine it's type.
operandType :: Operand -> Type
operandType (LocalReference ty _) = ty
operandType (ConstantOperand cons) =
    case cons of
        C.Int 8 _ -> char_t
        C.Int _ _ -> int_t
        C.Float _ -> int_t
        C.Null ty -> ty
        C.GlobalReference ty _ -> ty
        C.GetElementPtr _ (C.GlobalReference ty _) _ -> ty
        _ -> error "Not a recognised constant operand."
operandType _ = void_t


----------------------------------------------------------------------------
-- Instructions                                                           --
----------------------------------------------------------------------------

-- | The `namedInstr` function appends a named instruction into the instruction
-- stack of the current BasicBlock. This action also produces a Operand value
-- of the given type (this will be the result type of performing that
-- instruction).
namedInstr :: Type -> String -> Instruction -> Codegen Operand
namedInstr ty nm ins =
    do let ref = Name nm
       blk <- current
       let i = stack blk
       modifyBlock $ blk { stack = i ++ [ref := ins] }
       return $ local ty ref

-- | The `instr` function appends an unnamed instruction intp the instruction
-- stack of the current BasicBlock. The temp name is generated using a fresh
-- word counter.
instr :: Type -> Instruction -> Codegen Operand
instr ty ins =
    do n <- fresh
       let ref = UnName n
       blk <- current
       let i = stack blk
       modifyBlock $ blk { stack = i ++ [ref := ins] }
       return $ local ty ref


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

-- * Floating point arithmetic operations (Binary)

fadd :: Operand -> Operand -> Instruction
fadd a b = FAdd NoFastMathFlags a b []

fsub :: Operand -> Operand -> Instruction
fsub a b = FSub NoFastMathFlags a b []

fmul :: Operand -> Operand -> Instruction
fmul a b = FMul NoFastMathFlags a b []

fdiv :: Operand -> Operand -> Instruction
fdiv a b = FDiv NoFastMathFlags a b []

-- * Comparisions

fcmp :: FP.FloatingPointPredicate -> Operand -> Operand -> Instruction
fcmp p a b = FCmp p a b []

icmp :: IP.IntegerPredicate -> Operand -> Operand -> Instruction
icmp p a b = ICmp p a b []

-- * Bitwise operations
lOr :: Operand -> Operand -> Instruction
lOr a b = Or a b []

lAnd :: Operand -> Operand -> Instruction
lAnd a b = And a b []

lXor :: Operand -> Operand -> Instruction
lXor a b = Xor a b []

-- * Unary

uitofp :: Operand -> Instruction
uitofp a = UIToFP a float_t []

fptoui :: Operand -> Instruction
fptoui a = FPToUI a int_t []

-- | Create a constant operand (function parameters).
cons :: C.Constant -> Operand
cons = ConstantOperand

-- * Memory effecting instructions

-- | The 'call' instruction represents a simple function call.
-- TODO: Look into and make a TCO version of the function
-- TODO: Look into calling conventions (is fast cc alright?)
call :: Operand -> [Operand] -> Instruction
call fn args = Call (Just Tail) CC.C [] (Right fn) (toArgs args) [] []

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
store :: Operand -> Operand -> Codegen Operand
store ptr val = instr phantom_t $ Store False ptr val Nothing 0 []

-- | The 'load' function wraps LLVM's load instruction with defaults.
load :: Operand -> Instruction
load ptr = Load False ptr Nothing 0 []


-- Helpers for allocating, storing, loading
doAlloca :: Type -> Codegen Operand
doAlloca ty = instr (ptr_t ty) $ Alloca ty Nothing 0 []

doLoad :: Type -> Operand -> Codegen Operand
doLoad ty ptr = instr ty $ Load False ptr Nothing 0 []


-- * Structure operations
insertvalue :: Operand -> Operand -> Word32 -> Instruction
insertvalue st op i = InsertValue st op [i] []

extractvalue :: Operand -> Word32 -> Instruction
extractvalue st i = ExtractValue st [i] []


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
