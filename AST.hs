--  File     : AST.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module AST (-- Types just for parsing
  Item(..), Visibility(..), TypeProto(..), TypeSpec(..), FnProto(..), 
  ProcProto(..), Param(..), FlowDirection(..),  Stmt(..), 
  LoopStmt(..), Exp(..), Generator(..),
  -- AST types
  Module(..), initModule, ModSpec, ProcDef(..), Ident,
  -- AST functions
  toAST
  ) where

import Data.Map as Map
import Data.Set as Set

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [FnProto]
     | ResourceDecl Visibility Ident TypeSpec
     | FuncDecl Visibility FnProto TypeSpec Exp
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
  modImports :: Set ModSpec,
  pubTypes :: Set Ident,
  pubResources :: Set Ident,
  pubProcs :: Set Ident,
  modTypes :: Map Ident Int,
  modResources :: Map Ident ResourceDef,
  modProcs :: Map Ident ProcDef
  }  deriving Show

initModule = Module Set.empty Set.empty Set.empty Set.empty
             Map.empty Map.empty Map.empty 

modAddImport :: ModSpec -> Module -> Module
modAddImport imp mod 
  = mod { modImports = Set.insert imp $ modImports mod }

modAddPubType :: Ident -> Module -> Module
modAddPubType typ mod 
  = mod { pubTypes = Set.insert typ $ pubTypes mod }

modAddPubResource :: Ident -> Module -> Module
modAddPubResource name mod 
  = mod { pubResources = Set.insert name $ pubResources mod }

modAddPubProc :: Ident -> Module -> Module
modAddPubProc proc mod 
  = mod { pubProcs = Set.insert proc $ pubProcs mod }

modAddType :: Ident -> Int -> Module -> Module
modAddType name arity mod 
  = mod { modTypes = Map.insert name arity $ modTypes mod }

modAddResource :: Ident -> ResourceDef -> Module -> Module
modAddResource name def mod 
  = mod { modResources = Map.insert name def $ modResources mod }

modAddProc :: Ident -> ProcDef -> Module -> Module
modAddProc name def mod 
  = mod { modProcs = Map.insert name def $ modProcs mod }

publicise :: (Ident -> Module -> Module) -> 
             Visibility -> Ident -> Module -> Module
publicise insert vis id mod = applyIf (insert id) (vis == Public) mod


type Ident = String

type ModSpec = [Ident]

data ResourceDef = CompoundResource [Ident]
                 | SimpleResource TypeSpec
                   deriving Show

data ProcDef = ProcDef ProcProto [Stmt]
                   deriving Show

data Constructor = Constructor Ident [Param]
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

data Param = Param Ident TypeSpec FlowDirection
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
  publicise modAddPubType vis name
  $ modAddType name (length params) mod
toASTItem mod (ResourceDecl vis name typ) =
  publicise modAddPubResource vis name 
  $ modAddResource name (SimpleResource typ) mod
toASTItem mod (FuncDecl vis (FnProto name params) resulttype result) =
  toASTItem mod (ProcDecl vis
                 (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
                 [Assign "$" result])
toASTItem mod (ProcDecl vis proto@(ProcProto name params) stmts) =
  publicise modAddPubProc vis name
  $ modAddProc name (ProcDef proto stmts) mod
toASTItem mod (StmtDecl stmt) =
  case Map.lookup "" $ modProcs mod of
    Nothing -> 
      modAddProc "" (ProcDef (ProcProto "" []) [stmt]) mod
    Just (ProcDef proto stmts) ->
      modAddProc "" (ProcDef proto $ stmts ++ [stmt]) mod
      

----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
