--  File     : AST.hs
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010-2012 Peter Schachte.  All rights reserved.

module AST (-- Types just for parsing
  Item(..), Visibility(..), TypeProto(..), TypeSpec(..), FnProto(..), 
  ProcProto(..), Param(..), ProcArg(..), Stmt(..), 
  LoopStmt(..), Exp(..), Generator(..),
  -- Source Position Types
  Placed(..), place, content, maybePlace,
  -- AST types
  Module(..), ModSpec, ProcDef(..), Ident, VarName, ProcName,
  TypeDef(..), ResourceDef(..), FlowDirection(..),  argFlowDirection,
  Prim(..), PrimArg(..)
  ) where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos
import System.FilePath

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [FnProto] (Maybe SourcePos)
     | ResourceDecl Visibility Ident TypeSpec (Maybe SourcePos)
     | FuncDecl Visibility FnProto TypeSpec (Placed Exp) (Maybe SourcePos)
     | ProcDecl Visibility ProcProto [Placed Stmt] (Maybe SourcePos)
     | StmtDecl Stmt (Maybe SourcePos)

data Visibility = Public | Private
                  deriving (Eq, Show)

data TypeProto = TypeProto Ident [Ident]

data FnProto = FnProto Ident [Param]


----------------------------------------------------------------
--                    Handling Source Positions
----------------------------------------------------------------

data Placed t
    = Placed t SourcePos
    | Unplaced t

place :: Placed t -> Maybe SourcePos
place (Placed _ pos) = Just pos
place (Unplaced _) = Nothing

content :: Placed t -> t
content (Placed content _) = content
content (Unplaced content) = content

maybePlace :: t -> Maybe SourcePos -> Placed t
maybePlace t (Just pos) = Placed t pos
maybePlace t Nothing    = Unplaced t

----------------------------------------------------------------
--                            AST Types
----------------------------------------------------------------

data Module = Module {
  modImports :: Set ModSpec,
  pubTypes :: Set Ident,
  pubResources :: Set Ident,
  pubProcs :: Set Ident,
  modTypes :: Map Ident TypeDef,
  modResources :: Map Ident ResourceDef,
  modProcs :: Map Ident [ProcDef]
  }

type Ident = String

type VarName = String

type ProcName = String

type ModSpec = [Ident]

data TypeDef = TypeDef Int (Maybe SourcePos)

data ResourceDef = CompoundResource [Ident] (Maybe SourcePos)
                 | SimpleResource TypeSpec (Maybe SourcePos)

data ProcDef = ProcDef ProcID ProcProto [Placed Prim] (Maybe SourcePos)

type ProcID = Int

data TypeSpec = TypeSpec Ident [TypeSpec] | Unspecified

data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving Show

data ProcProto = ProcProto ProcName [Param]

data Param = Param VarName TypeSpec FlowDirection

data FlowDirection = ParamIn | ParamOut | ParamInOut
      deriving (Show,Eq)

data ProcArg = ProcArg (Placed Exp) FlowDirection

data Stmt
     = ProcCall Ident [ProcArg]
     | Cond (Placed Exp) [Placed Stmt] [Placed Stmt]
     | Loop [Placed LoopStmt]
     | Nop

data LoopStmt
     = For Generator
     | BreakIf (Placed Exp)
     | NextIf (Placed Exp)
     | NormalStmt (Placed Stmt)

data Exp
      = IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Var VarName
      | Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | Fncall String [Placed Exp]

data Generator 
      = In VarName (Placed Exp)
      | InRange VarName (Placed Exp) ProcName (Placed Exp) 
        (Maybe (ProcName,Placed Exp))

data Prim
     = PrimCall ProcName (Maybe ProcID) [PrimArg]
     | PrimCond VarName [[Placed Prim]]
     | PrimLoop [Placed Prim]
     | PrimBreakIf VarName
     | PrimNextIf VarName

data PrimArg 
     = ArgVar VarName FlowDirection
     | ArgInt Integer
     | ArgFloat Double
     | ArgString String
     | ArgChar Char

argFlowDirection :: PrimArg -> FlowDirection
argFlowDirection (ArgVar _ flow) = flow
argFlowDirection (ArgInt _) = ParamIn
argFlowDirection (ArgFloat _) = ParamIn
argFlowDirection (ArgString _) = ParamIn
argFlowDirection (ArgChar _) = ParamIn
