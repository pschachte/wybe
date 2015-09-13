-- File    : Codegen.hs
-- RCS     : $Id$
-- Author  : Ashutosh Rishi Ranjan
-- Purpose : Generate and emit LLVM from basic blocks of a module

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Codegen where

import           Control.Applicative
import           Control.Monad.State
import qualified Data.Map                as Map
import           LLVM.General.AST
import qualified LLVM.General.AST        as LLVMAST
import           LLVM.General.AST.Global


-- A LLVM function consists of a sequence of basic blocks containing a
-- sequence of instructions and assignment to local values. During
-- compilation basic blocks will roughly correspond to labels in the
-- native assembly output.

-- Some simple type synonyms
type SymbolTable = [(String, Operand)]
type Names = Map.Map String Int


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
      , count        :: Word                    -- ^ Count for unnamed instruction names
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


