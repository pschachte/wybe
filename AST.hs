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
  modProcs :: Map Ident [ProcDef],
  procCount :: Int
  }  deriving Show

initModule = Module Set.empty Set.empty Set.empty Set.empty
             Map.empty Map.empty Map.empty 0

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

modAddProc :: Ident -> ProcProto -> [Placed Stmt] -> (Maybe SourcePos)
              -> Module -> Module
modAddProc name proto stmts pos mod
  = let newid = 1 + procCount mod
        procs = modProcs mod
        defs  = ProcDef newid proto stmts pos:
                            findWithDefault [] name procs
                in  mod { modProcs  = Map.insert name defs procs,
                          procCount = newid }

modReplaceProc :: Ident -> Int -> ProcProto -> [Placed Stmt]
                  -> (Maybe SourcePos) -> Module -> Module
modReplaceProc name id proto stmts pos mod
  = let procs   = modProcs mod
        olddefs = findWithDefault [] name procs
        (_,rest)  = List.partition (\(ProcDef oldid _ _ _) -> id==oldid) olddefs
    in  mod { modProcs  = Map.insert name (ProcDef id proto stmts pos:rest) 
                          procs }

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

data Param = Param Ident TypeSpec FlowDirection
      deriving Show

data FlowDirection = ParamIn | ParamOut | ParamInOut
      deriving (Show,Eq)

data Stmt
     = Assign String (Placed Exp)
     | ProcCall String [Placed Exp]
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
      = Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Fncall String [(Placed Exp)]
      | Var String
      deriving Show

data Generator 
      = In String (Placed Exp)
      | InRange String (Placed Exp) (Placed Exp) (Maybe (Placed Exp))
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
                 [maybePlace (Assign "$" result) (place result)]
                 pos)
toASTItem mod (ProcDecl vis proto@(ProcProto name params) stmts pos) =
  publicise modAddPubProc vis name $ modAddProc name proto stmts pos mod
toASTItem mod (StmtDecl stmt pos) =
  case Map.lookup "" $ modProcs mod of
    Nothing -> 
      modAddProc "" (ProcProto "" []) [maybePlace stmt pos] Nothing mod
    Just [ProcDef id proto stmts pos'] ->
      modReplaceProc "" id proto (stmts ++ [maybePlace stmt pos]) pos' mod


----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
