-- File    : Codegen.hs
-- RCS     : $Id$
-- Author  : Ashutosh Rishi Ranjan
-- Purpose : Generate and emit LLVM from basic blocks of a module

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Codegen where

import           Control.Applicative
import           Control.Monad.State
import qualified Data.Map                  as Map
import           Data.Word
import           LLVM.General.AST
import qualified LLVM.General.AST          as LLVMAST
import qualified LLVM.General.AST.Constant as C
import           LLVM.General.AST.Global


-- A LLVM function consists of a sequence of basic blocks containing a
-- sequence of instructions and assignment to local values. During
-- compilation basic blocks will roughly correspond to labels in the
-- native assembly output.

-- Some simple type synonyms
type SymbolTable = [(String, Operand)]
type Names = Map.Map String Int


-- Test type
int :: Type
int = IntegerType 32

----------------------------------------------------------------------------
-- Codegen State                                                          --
----------------------------------------------------------------------------


-- | 'CodegenState' will generate the toplevel module code
data CodegenState
    = CodegenState {
        currentBlock :: Name                    -- ^ Name of the active block to append to
      , blocks       :: Map.Map Name BlockState -- ^ Blocks for function
      , symtab       :: SymbolTable             -- ^ Local symbol table of a function
      , blockCount   :: Int                     -- ^ Incrementing count of basic blocks
      , count        :: Word                    -- ^ Count for temporary operands
      , names        :: Names                   -- ^ Name supply
      } deriving Show

-- | 'BlockState' will generate the code for basic blocks inside of
-- function definitions
data BlockState
    = BlockState {
        idx   :: Int -- ^ Block
      , stack :: [Named Instruction]
      , term  :: Maybe (Named Terminator)
      } deriving Show


-- | The 'Codegen' state monad will hold the state of the code generator
-- That is, a map of block names to their 'BlockState' representation
newtype Codegen a = Codegen { runCodegen :: State CodegenState a }
    deriving (Functor, Applicative, Monad, MonadState CodegenState)


-- | Gets a new count suffix for a temporary local operands
fresh :: Codegen Word
fresh = do
  ix <- gets count
  modify $ \s -> s { count = 1 + ix }
  return (ix + 1)


----------------------------------------------------------------------------
-- LLVM State Monad                                                       --
----------------------------------------------------------------------------

-- | The 'LLVM' state monad holds code for the LLVM module and will be
-- evaluated to emit llvm-general module contatining the AST
newtype LLVM a = LLVM { unLLVM :: State LLVMAST.Module a }
    deriving (Functor, Applicative, Monad, MonadState LLVMAST.Module)

runLLVM :: LLVMAST.Module -> LLVM a -> LLVMAST.Module
runLLVM = flip (execState . unLLVM)

emptyModule :: String -> LLVMAST.Module
emptyModule label = defaultModule { moduleName = label }

-- | Add a definition to the AST.Module (LLVMAST.Module qualified),
-- to the field moduleDefinitions
addDefn :: Definition -> LLVM ()
addDefn d = do
  defs <- gets moduleDefinitions
  modify $ \s -> s { moduleDefinitions = defs ++ [d] }



-- | 'define' records local function definitions in the module
define :: Type -> String -> [(Type, Name)] -> [BasicBlock] -> LLVM ()
define rettype label argtypes body
    = addDefn $ GlobalDefinition $ functionDefaults {
        name = Name label
      , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes], False)
      , returnType = rettype
      , basicBlocks = body
      }

-- | 'external' records extern definitions
external :: Type -> String -> [(Type, Name)] -> [BasicBlock] -> LLVM ()
external rettype label argtypes body
    = addDefn $ GlobalDefinition $ functionDefaults {
        name = Name label
      , parameters = ([Parameter ty nm [] | (ty, nm) <- argtypes], False)
      , returnType = rettype
      , basicBlocks = body
      }


----------------------------------------------------------------------------
-- Blocks                                                                 --
----------------------------------------------------------------------------

entry :: Codegen Name
entry = gets currentBlock

-- | Initializes an empty new block
emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing

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

setBlock :: Name -> Codegen Name
setBlock bname =
    do modify $ \s -> s { currentBlock = bname }
       return bname

-- | Get the current block.
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

-- | Local references (prefixed with % in LLVM)
local :: Name -> Operand
local = LocalReference int

-- | Refer to toplevel functions (prefixed with @ in LLVM)
externf :: Name -> Operand
externf = ConstantOperand . C.GlobalReference int


----------------------------------------------------------------------------
-- Symbol Table                                                           --
----------------------------------------------------------------------------

assign :: String -> Operand -> Codegen ()
assign var x = do
  lcls <- gets symtab
  modify $ \s -> s { symtab = (var, x) : lcls }

getVar :: String -> Codegen Operand
getVar var = do
  lcls <- gets symtab
  case lookup var lcls of
    Just x -> return x
    Nothing -> error $ "Local variable not in scope: " ++ show var

----------------------------------------------------------------------------
-- Instructions                                                           --
----------------------------------------------------------------------------

-- | 'instr' pushes a new LLVMAST.Instruction to the current basic block
-- instruction stack. This action produces the left hand side value
-- of the instruction (of the type Operand).
instr :: Instruction -> Codegen Operand
instr ins = do
  n <- fresh
  let ref = UnName n
  blk <- current
  let i = stack blk
  modifyBlock $ blk { stack = i ++ [ref := ins] }
  return $ local ref


-- | 'terminator' provides the last instruction of a basic block.
terminator :: Named Terminator -> Codegen (Named Terminator)
terminator trm = do
  blk <- current
  modifyBlock $ blk { term = Just trm }
  return trm


-- Some basic instructions

-- * Integer arithmetic operations

iadd :: Operand -> Operand -> Codegen Operand
iadd a b = instr $ Add False False a b []

isub :: Operand -> Operand -> Codegen Operand
isub a b = instr $ Sub False False a b []

imul :: Operand -> Operand -> Codegen Operand
imul a b = instr $ Mul False False a b []

-- TODO: Look into all the arithmetic instructions and what they actually do.

-- * Effect instructions

-- | The 'call' instruction represents a simple function call.
-- TODO: Look into and make a TCO version of the function
-- TODO: Look into calling conventions (is fast cc alright?)
call :: Operand -> [Operand] -> Codegen Operand
call fn args = instr $ Call False CC.C [] (Right fn) (toArgs args) [] []

-- | The ‘alloca‘ instruction allocates memory on the stack frame of the
-- currently executing function, to be automatically released when this
-- function returns to its caller. The object is always allocated in the
-- generic address space (address space zero).
alloca :: Type -> Codegen Operand
alloca ty = instr $ Alloca ty Nothing 0 []

-- | The 'store' instruction is used to write to write to memory.
store :: Operand -> Operand -> Codegen Operand
store ptr val = instr $ Store False ptr val Nothing 0 []


load :: Operand -> Codegen
load ptr = instr $ Load False ptr Nothing 0 []


-- * Control Flow operations

-- TODO: These have to be wrapped according to how LPVM functions

br :: Name -> Codegen (Named Terminator)
br val = terminator $ Do $ Br val []

cbr :: Operand -> Name -> Name -> Codegen (Named Terminator)
cbr cond tr fl = terminator $ Do $ CondBr cond tr fl []

ret :: Operand -> Codegen (Named Terminator)
ret val = terminator $ Do $ Ret (Just val) []
