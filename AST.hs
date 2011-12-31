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
  -- Source Position Types
  Placed(..), place, content, maybePlace,
  -- AST types
  Module(..), initModule, ModSpec, ProcDef(..), Ident,
  -- AST functions
  toAST
  ) where

import Data.Map as Map
import Data.Set as Set
import Text.ParserCombinators.Parsec.Pos

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [FnProto] (Maybe SourcePos)
     | ResourceDecl Visibility Ident TypeSpec (Maybe SourcePos)
     | FuncDecl Visibility FnProto TypeSpec Exp (Maybe SourcePos)
     | ProcDecl Visibility ProcProto [Placed Stmt] (Maybe SourcePos)
     | StmtDecl Stmt (Maybe SourcePos)
    deriving Show

data Visibility = Public | Private
                  deriving (Eq, Show)

type Idents = [String]

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

modAddType :: Ident -> TypeDef -> Module -> Module
modAddType name def mod
  = mod { modTypes = Map.insert name def $ modTypes mod }

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

data TypeDef = TypeDef Int (Maybe SourcePos)
                   deriving Show

data ResourceDef = CompoundResource [Ident] (Maybe SourcePos)
                 | SimpleResource TypeSpec (Maybe SourcePos)
                   deriving Show

data ProcDef = ProcDef ProcProto [Placed Stmt] (Maybe SourcePos)
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

data Stmt
     = Assign String Exp
     | ProcCall String [Exp]
     | Cond Exp [Placed Stmt] [Placed Stmt]
     | Loop [Placed LoopStmt]
     | Nop
    deriving Show

data LoopStmt
     = For Generator
     | BreakIf Exp
     | NextIf Exp
     | NormalStmt Stmt
    deriving Show

data Exp
      = Where [Placed Stmt] Exp
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
toASTItem mod (TypeDecl vis (TypeProto name params) ctrs pos) =
  publicise modAddPubType vis name
  $ modAddType name (TypeDef (length params) pos) mod
toASTItem mod (ResourceDecl vis name typ pos) =
  publicise modAddPubResource vis name 
  $ modAddResource name (SimpleResource typ pos) mod
toASTItem mod (FuncDecl vis (FnProto name params) resulttype result pos) =
  toASTItem mod (ProcDecl vis
                 (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
                 [maybePlace (Assign "$" result) pos]
                 pos)
toASTItem mod (ProcDecl vis proto@(ProcProto name params) stmts pos) =
  publicise modAddPubProc vis name
  $ modAddProc name (ProcDef proto stmts pos) mod
toASTItem mod (StmtDecl stmt pos) =
  case Map.lookup "" $ modProcs mod of
    Nothing -> 
      modAddProc "" (ProcDef (ProcProto "" []) [maybePlace stmt pos] Nothing) 
      mod
    Just (ProcDef proto stmts pos') ->
      modAddProc "" (ProcDef proto (stmts ++ [maybePlace stmt pos]) pos') mod
      

----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
