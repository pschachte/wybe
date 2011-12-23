--  File     : AST.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module AST (-- Types just for parsing
  Item(..), Visibility(..), TypeProto(..), Type(..), FnProto(..), 
  ProcProto(..), Param(..), FlowDirection(..),  Stmt(..), 
  LoopStmt(..), Exp(..), Generator(..),
  -- AST types
  Module(..), initModule, ModSpec, ProcDef(..), Ident
  ) where

import Data.Map as Map
import Data.Set as Set

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [FnProto]
     | FuncDecl Visibility FnProto Type Exp
     | ProcDecl Visibility ProcProto Stmts
     | StmtDecl Stmt
    deriving Show

data Visibility = Public | Private
                  deriving (Eq, Show)

type Idents = [String]

data TypeProto = TypeProto String [String]
      deriving Show

data FnProto = FnProto String [Param]
      deriving Show



----------------------------------------------------------------
--                            AST Types
----------------------------------------------------------------

data Module = Module {
  modName :: Ident,
  modImports :: Set ModSpec,
  pubTypes :: Set TypeName,
  pubResources :: Set ResourceName,
  pubProcs :: Set ProcFuncName,
  modTypes :: Map TypeName Int,
  modResources :: Map ResourceName ResourceDef,
  modProcs :: Map Ident ProcDef
  }  deriving Show

initModule = Module "" Set.empty Set.empty Set.empty Set.empty
             Map.empty Map.empty Map.empty 

type Ident = String
type TypeName = Ident
type ResourceName = Ident
type ProcFuncName = Ident

type ModSpec = [Ident]

data ResourceDef = CompoundResource [ResourceName]
                 | SimpleResource TypeSpec
                   deriving Show

data ProcDef = ProcDef ProcProto [Stmt]
                   deriving Show

data Constructor = Constructor Ident [Param]
                   deriving Show

data TypeSpec = TypeName Ident [TypeSpec]
                deriving Show

data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving Show

data ProcProto = ProcProto String [Param]
      deriving Show

data Param = Param String Type FlowDirection
      deriving Show

data Type = Type String [Type]
          | Unspecified
      deriving Show

data FlowDirection = ParamIn | ParamOut | ParamInOut
      deriving (Show,Eq)

type Stmts = [Stmt]

data Stmt
     = Assign String Exp
     | ProcCall String [Exp]
     | Cond Exp Stmts Stmts
     | Loop [LoopStmt]
     | Nop
    deriving Show

data LoopStmt
     = For Generator
     | BreakIf Exp
     | NextIf Exp
     | NormalStmt Stmt
    deriving Show

data Exp
      = Where Stmts Exp
      | CondExp Exp Exp Exp
      | IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Fncall String [Exp]
      | Var String
      deriving Show

data Generator 
      = In String Exp
      | InRange String Exp Exp (Maybe Exp)
    deriving Show


toAST :: [Item] -> Module
toAST items = foldl toASTItem initModule items

toASTItem :: Module -> Item -> Module
toASTItem mod (TypeDecl vis (TypeProto name params) ctrs) =
  let mod' = mod { modTypes = Map.insert name (length params) (modTypes mod) }
  in  if vis == Public
      then mod' { pubTypes = Set.insert name (pubTypes mod') }
      else mod'
--toASTItem (FuncDecl vis (FnProto name params) resulttype result) mod =
  
