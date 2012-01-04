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
  -- AST functions
  toAST
  ) where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos
import Control.Monad.State

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
      = Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Fncall String [Placed Exp]
      | Var String
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


-- While expanding items to an AST, payload is a counter for introduced
-- variables, the module being created, and a list of error messages
data ExpanderState = Expander {
  varCount :: Int, 
  procCount :: Int,
  modul :: Module, 
  errs :: [String]
  } deriving Show

type Expander = State ExpanderState

initExpander :: ExpanderState
initExpander = Expander 0 0 (Module Set.empty Set.empty Set.empty Set.empty
                             Map.empty Map.empty Map.empty) []

getModule :: Expander Module
getModule = do
  state <- get
  return $ modul state

modAddImport :: ModSpec -> Module -> Module
modAddImport imp mod 
  = mod { modImports = Set.insert imp $ modImports mod }

modAddProc :: Ident -> (Int, ProcProto, [Placed Stmt], (Maybe SourcePos))
              -> Module -> Module
modAddProc name (newid, proto, stmts, pos) mod
  = let procs = modProcs mod
        defs  = ProcDef newid proto stmts pos:
                            findWithDefault [] name procs
                in  mod { modProcs  = Map.insert name defs procs }

modReplaceProc :: Ident -> (Int, ProcProto, [Placed Stmt], (Maybe SourcePos)) 
                  -> Module -> Module
modReplaceProc name (id, proto, stmts, pos) mod
  = let procs   = modProcs mod
        olddefs = findWithDefault [] name procs
        (_,rest)  = List.partition (\(ProcDef oldid _ _ _) -> id==oldid) olddefs
    in  mod { modProcs  = Map.insert name (ProcDef id proto stmts pos:rest) 
                          procs }

publicise :: (Ident -> Module -> Module) -> 
             Visibility -> Ident -> Module -> Module
publicise insert vis name mod = applyIf (insert name) (vis == Public) mod


errMsg :: String -> Expander ()
errMsg msg = do
  state <- get
  put state { errs = (errs state) ++ [msg] }

freshVar :: Expander String
freshVar = do
  state <- get
  let ctr = varCount state
  put state { varCount = ctr + 1 }
  return $ "$tmp" ++ (show ctr)

nextProcId :: Expander Int
nextProcId = do
  state <- get
  let ctr = 1 + procCount state
  put state { procCount = ctr }
  return ctr

addItem :: (Ident -> t -> Module -> Module) ->
           (Ident -> Module -> Module) ->
           Ident -> t -> Visibility -> Expander ()
addItem inserter publisher name def visibility = do
  state <- get
  put state { modul = publicise publisher visibility name $
                      inserter name def $ modul state }

addType :: Ident -> TypeDef -> Visibility -> Expander ()
addType = 
  addItem (\name def mod -> 
            mod { modTypes = Map.insert name def $ modTypes mod })
          (\name mod -> mod { pubTypes = Set.insert name $ pubTypes mod })

lookupType :: Ident -> Expander (Maybe TypeDef)
lookupType name = do
  mod <- getModule
  return $ Map.lookup name (modTypes mod)

publicType :: Ident -> Expander Bool
publicType name = do
  mod <- getModule
  return $ Set.member name (pubTypes mod)

addResource :: Ident -> ResourceDef -> Visibility -> Expander ()
addResource = 
  addItem (\name def mod -> 
            mod { modResources = Map.insert name def $ modResources mod })
          (\name mod ->
            mod { pubResources = Set.insert name $ pubResources mod })

lookupResource :: Ident -> Expander (Maybe ResourceDef)
lookupResource name = do
  mod <- getModule
  return $ Map.lookup name (modResources mod)

publicResource :: Ident -> Expander Bool
publicResource name = do
  mod <- getModule
  return $ Set.member name (pubResources mod)

addProc :: Ident -> ProcProto -> [Placed Stmt] -> (Maybe SourcePos)
           -> Visibility -> Expander ()
addProc name proto stmts pos vis = do
  newid <- nextProcId
  addItem modAddProc
          (\name mod -> mod { pubProcs = Set.insert name $ pubProcs mod })
          name (newid, proto, stmts, pos) vis

replaceProc :: Ident -> Int -> ProcProto -> [Placed Stmt] -> (Maybe SourcePos)
               -> Visibility -> Expander ()
replaceProc name oldid proto stmts pos vis =
  addItem modReplaceProc 
          (\name mod -> mod { pubProcs = Set.insert name $ pubProcs mod })
          name (oldid, proto, stmts, pos) vis

lookupProc :: Ident -> Expander (Maybe [ProcDef])
lookupProc name = do
  mod <- getModule
  return $ Map.lookup name (modProcs mod)

publicProc :: Ident -> Expander Bool
publicProc name = do
  mod <- getModule
  return $ Set.member name (pubProcs mod)


toAST :: [Item] -> (Module,[String])
toAST items = (modul result, errs result) where
  (_,result) = runState (toASTItems items) initExpander

toASTItems :: [Item] -> Expander ()
toASTItems [] = return ()
toASTItems (item:items) = do
  toASTItem item
  toASTItems items

toASTItem :: Item -> Expander ()
toASTItem (TypeDecl vis (TypeProto name params) ctrs pos) =
  addType name (TypeDef (length params) pos) vis
toASTItem (ResourceDecl vis name typ pos) =
  addResource name (SimpleResource typ pos) vis
toASTItem (FuncDecl vis (FnProto name params) resulttype result pos) =
  toASTItem (ProcDecl vis
             (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
             [Unplaced (ProcCall "=" [ProcArg (Unplaced $ Var "$") 
                                      ParamOut, 
                                      ProcArg result ParamIn])]
             pos)
toASTItem (ProcDecl vis proto@(ProcProto name params) stmts pos) =
  addProc name proto stmts pos vis
toASTItem (StmtDecl stmt pos) = do
  oldproc <- lookupProc ""
  case oldproc of
    Nothing -> 
      addProc "" (ProcProto "" []) [maybePlace stmt pos] Nothing Private
    Just [ProcDef id proto stmts pos'] ->
      replaceProc "" id proto (stmts ++ [maybePlace stmt pos]) pos' Private


--expandExp :: Exp -> ExpState [Stmt]


----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
