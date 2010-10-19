--  File     : AST.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module AST where

import Data.Map as Map
import Data.Set as Set

type FileContent = [Module]

data Module = Module {
  modName :: Ident,
  modImports :: Set ModSpec,
  pubTypes :: Set TypeName,
  pubResources :: Set ResourceName,
  pubProcs :: Set ProcFuncName,
  modTypes :: Map TypeName TypeDefn,
  modResources :: Map ResourceName ResourceDef,
  modProcs :: Map ProcFuncName ItemDefn
  }  deriving Show

initModule = Module "" Set.empty Set.empty Set.empty Set.empty
             Map.empty Map.empty Map.empty 


type Ident = String
type TypeName = Ident
type ResourceName = Ident
type ProcFuncName = Ident

type ModSpec = [Ident]

data Visibility = Public | Private
                  deriving Show

data ItemDefn =
    FuncDef [Param] FnBody
  | ProcDef [Param] ProcBody
    deriving Show

type TypeDefn = [Constructor]

data ResourceDef = CompoundResource [ResourceName]
                 | SimpleResource TypeSpec
                   deriving Show

data Constructor = Constructor Ident [Param]
                   deriving Show

data Param = Formal Ident TypeSpec
             deriving Show

data TypeSpec = TypeName Ident [TypeSpec]
                deriving Show

data FnBody = Function [Stmt] Expr
              deriving Show

data ProcBody = Procedure [Stmt]
                deriving Show

data Stmt = Assignment Lvalue Expr
          | ProcCall Ident [ArgSpec]
            deriving Show

type ArgSpec = Expr -- Will need to extend to handle named/optional params

type Lvalue = Variable -- Will need to handle record access, etc.  SETF-like?

data Expr = Variable Variable
          | Constant Constant
          | FuncCall Ident [ArgSpec]
            deriving Show

type Variable = Ident

data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving Show
