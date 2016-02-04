--  File     : BinaryFactory.hs
--  RCS      : $Id$
--  Author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Deriving AST Types to be Binary instances
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

{-# LANGUAGE DeriveGeneric #-}

module BinaryFactory
       where

import AST
import Control.Monad
import Data.Binary as B
import qualified LLVM.General.AST as LLVMAST
import Text.ParserCombinators.Parsec.Pos


-- * Self Deriving instances
instance Binary Visibility
instance (Binary t) => Binary (Placed t)
instance Binary ArgFlowType
instance Binary ResourceSpec
instance Binary FlowDirection
instance Binary PrimFlow
instance Binary TypeSpec
instance Binary Exp
instance Binary Stmt
instance Binary ParamInfo
instance Binary Prim
instance Binary PrimVarName
instance Binary PrimArg
-- Procedures
instance Binary ProcSpec
instance Binary ProcImpln
instance Binary PrimProto
instance Binary PrimParam
instance Binary ProcBody
instance Binary PrimFork
instance Binary SuperprocSpec
instance Binary ProcDef
instance Binary ProcProto
instance Binary Param
instance Binary ResourceFlowSpec
-- Module implementation
instance Binary ModuleImplementation
instance Binary ResourceImpln
instance Binary TypeDef
instance Binary ImportSpec
-- Module
instance Binary Module
instance Binary ModuleInterface

-- * Manual Serialisation


instance Binary SourcePos where
  put pos = do put $ sourceName pos
               put $ sourceLine pos
               put $ sourceColumn pos

  get = liftM3 newPos get get get                                   


instance Binary LLVMAST.Definition where
  put = put . show
  get = do def <- get
           return (read def :: LLVMAST.Definition)

instance Binary LLVMAST.Module where
  put = put . show
  get = do def <- get
           return (read def :: LLVMAST.Module)


