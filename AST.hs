--  File     : AST.hs
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010-2012 Peter Schachte.  All rights reserved.

module AST (-- Types just for parsing
  Item(..), Visibility(..), TypeProto(..), TypeSpec(..), FnProto(..), 
  ProcProto(..), Param(..), ProcArg(..), FlowDirection(..),  Stmt(..), 
  LoopStmt(..), Exp(..), Generator(..),
  -- Source Position Types
  Placed(..), place, content, maybePlace,
  -- AST types
  Module(..), ModSpec, ProcDef(..), Ident, VarName,
  TypeDef(..), ResourceDef(..),
  ) where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [FnProto] (Maybe SourcePos)
     | ResourceDecl Visibility Ident TypeSpec (Maybe SourcePos)
     | FuncDecl Visibility FnProto TypeSpec (Placed Exp) (Maybe SourcePos)
     | ProcDecl Visibility ProcProto [Placed Stmt] (Maybe SourcePos)
     | StmtDecl Stmt (Maybe SourcePos)
    deriving Show

data Visibility = Public | Private
                  deriving (Eq, Show)

data TypeProto = TypeProto String [String]
      deriving Show

data FnProto = FnProto String [Param]
      deriving Show



----------------------------------------------------------------
--                    Handling Source Positions
----------------------------------------------------------------

data Placed t
    = Placed t SourcePos
    | Unplaced t
      deriving Show

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
  }  deriving Show

type Ident = String

type VarName = String

type ModSpec = [Ident]

data TypeDef = TypeDef Int (Maybe SourcePos)
                   deriving Show

data ResourceDef = CompoundResource [Ident] (Maybe SourcePos)
                 | SimpleResource TypeSpec (Maybe SourcePos)
                   deriving Show

data ProcDef = ProcDef Int ProcProto [Placed Stmt] (Maybe SourcePos)
                   deriving Show

data TypeSpec = TypeSpec Ident [TypeSpec] | Unspecified
                deriving Show

data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving Show

data ProcProto = ProcProto String [Param]
      deriving Show

data Param = Param VarName TypeSpec FlowDirection
      deriving Show

data FlowDirection = ParamIn | ParamOut | ParamInOut
      deriving (Show,Eq)

data ProcArg = ProcArg (Placed Exp) FlowDirection
      deriving Show

data Stmt
     = ProcCall String [ProcArg]
     | Cond (Placed Exp) [Placed Stmt] [Placed Stmt]
     | Loop [Placed LoopStmt]
     | Nop
    deriving Show

data LoopStmt
     = For Generator
     | BreakIf (Placed Exp)
     | NextIf (Placed Exp)
     | NormalStmt (Placed Stmt)
    deriving Show

data Exp
      = IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Var String
      | Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | Fncall String [Placed Exp]
      deriving Show

data Generator 
      = In String (Placed Exp)
      | InRange String (Placed Exp) (Placed Exp) (Maybe (Placed Exp))
    deriving Show

data Prim
     = PrimCall String (Maybe Int) [PrimArg]
     | PrimCond VarName [Placed Prim] [Placed Prim]
     | PrimLoop [Placed Prim]
     | PrimFor PrimGen
     | PrimBreakIf VarName
     | PrimNextIf VarName

data PrimGen
      = PrimIn VarName VarName
      | PrimRange VarName VarName VarName (Maybe VarName)
    deriving Show

data PrimArg 
     = ArgVar VarName FlowDirection
     | ArgInt Integer
     | ArgFloat Double
     | ArgString String
     | ArgChar Char

