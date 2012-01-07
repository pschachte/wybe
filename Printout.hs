--  File     : Printout.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sun Jan  8 02:02:41 2012
--  Purpose  : Pretty printer for AST types
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Printout (
  ) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos
import System.FilePath

instance Show Item where
  show (TypeDecl vis name ctrs pos) =
    show vis ++ " type " ++ show name ++ " = " 
    ++ intercalate " | " (List.map show ctrs)
    ++ showMaybeSourcePos pos
  show (ResourceDecl vis name typ pos) =
    show vis ++ " resource " ++ show name ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
  show (FuncDecl vis proto typ exp pos) =
    show vis ++ " func " ++ show proto ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
    ++ " = " ++ show exp
  show (ProcDecl vis proto stmts pos) =
    show vis ++ " proc " ++ show proto
    ++ showMaybeSourcePos pos
    ++ show stmts
  show (StmtDecl stmt pos) =
    show stmt ++ showMaybeSourcePos pos

instance Show TypeProto where
  show (TypeProto name []) = name
  show (TypeProto name args) = name ++ "(" ++ intercalate "," args ++ ")"


instance Show FnProto where
  show (FnProto name []) = name
  show (FnProto name params) = 
    name ++ "(" ++ intercalate "," (List.map show params) ++ ")"

instance Show t => Show (Placed t) where
  show pl = show (content pl) ++ showMaybeSourcePos (place pl)
    
showMaybeSourcePos :: Maybe SourcePos -> String
showMaybeSourcePos (Just pos) = 
  " {" ++ takeBaseName (sourceName pos) ++ ":" 
  ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos) ++ "}"
showMaybeSourcePos Nothing = " {?}"

instance Show Module where
  show mod =
    "Module" ++ 
    "\n  imports         : " ++ showModSpecSet (modImports mod) ++ 
    "\n  public types    : " ++ showIdSet (pubTypes mod) ++
    "\n  public resources: " ++ showIdSet (pubResources mod) ++
    "\n  public procs    : " ++ showIdSet (pubProcs mod) ++
    "\n  types:          : " ++ showMap (modTypes mod) ++
    "\n  resources       : " ++ showMap (modResources mod) ++
    "\n  procs           : " ++ showMap (modProcs mod) ++ "\n"

showModSpecSet :: Set ModSpec -> String
showModSpecSet set = intercalate ", " 
                     $ List.map (intercalate ".") 
                     $ Set.elems set

showIdSet :: Set Ident -> String
showIdSet set = intercalate ", " $ Set.elems set

showMap :: Show v => Map Ident v -> String
showMap m = intercalate "\n                    " 
            $ List.map (\(k,v) -> k ++ ": " ++ show v) $ Map.assocs m

instance Show TypeDef where
  show (TypeDef arity pos) = 
    "arity " ++ show arity ++ " " ++ showMaybeSourcePos pos

instance Show ResourceDef where
  show (CompoundResource ids pos) =
    intercalate ", " ids ++ showMaybeSourcePos pos
  show (SimpleResource typ pos) =
    show typ ++ showMaybeSourcePos pos

instance Show ProcDef where
  show (ProcDef i proto def pos) =
    "proc " ++ show i ++ ": " ++ show proto ++ showMaybeSourcePos pos 
    ++ showBlock 4 def

instance Show TypeSpec where
  show Unspecified = "?"
  show (TypeSpec ident []) = ident
  show (TypeSpec ident args) = 
    ident ++ "(" ++ (intercalate "," $ List.map show args) ++ ")"

instance Show ProcProto where
  show (ProcProto name params) = 
    name ++ "(" ++ (intercalate ", " $ List.map show params) ++ ")"

instance Show Param where
  show (Param name typ dir) =
    flowPrefix dir ++ name ++ ":" ++ show typ

instance Show ProcArg where
  show (ProcArg exp dir) =
    flowPrefix dir ++ show (content exp) ++ showMaybeSourcePos (place exp)

flowPrefix :: FlowDirection -> String
flowPrefix ParamIn    = ""
flowPrefix ParamOut   = "?"
flowPrefix ParamInOut = "!"

startLine :: Int -> String
startLine ind = "\n" ++ replicate ind ' '

showBlock :: Int -> [Placed Stmt] -> String
showBlock ind stmts = concat $ List.map (showStmt ind) stmts

showStmt :: Int -> Placed Stmt -> String
showStmt ind stmt = showStmt' ind (content stmt) (place stmt)

showStmt' :: Int -> Stmt -> Maybe SourcePos -> String
showStmt' ind (ProcCall name args) pos =
  startLine ind ++ name ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  ++ showMaybeSourcePos pos
showStmt' ind (Cond exp thn els) pos =
  startLine ind ++ "if " ++ show (content exp) ++ " then" 
  ++ showMaybeSourcePos pos
  ++ showBlock (ind+4) thn
  ++ startLine ind ++ "else"
  ++ showBlock (ind+4) els
  ++ startLine ind ++ "end"
showStmt' ind (Loop lstmts) pos =
  startLine ind ++ "do " ++ showMaybeSourcePos pos
  ++ concat (List.map (showLStmt (ind+4)) lstmts)
  ++ startLine ind ++ "end"

instance Show Stmt where
  show (ProcCall name args) =
    name ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (Cond exp thn els) =
    "if" ++ show (content exp) ++ " then"
    ++ show thn
    ++ " else "
    ++ show els
    ++ " end"
  show (Loop lstmts) =
    "do " ++ concat (List.map show lstmts) ++ " end"


showLStmt :: Int -> Placed LoopStmt -> String
showLStmt ind lstmt = showLStmt' ind (content lstmt) (place lstmt)

showLStmt' :: Int -> LoopStmt -> Maybe SourcePos -> String
showLStmt' ind (For gen) pos =
  startLine ind ++ "for " ++ show gen ++ showMaybeSourcePos pos
showLStmt' ind (BreakIf cond) pos =
  startLine ind ++ "until " ++ show cond ++ showMaybeSourcePos pos
showLStmt' ind (NextIf cond) pos =
  startLine ind ++ "unless " ++ show cond ++ showMaybeSourcePos pos
showLStmt' ind (NormalStmt stmt) pos =
  showStmt ind stmt


instance Show LoopStmt where
  show (For gen) = "for " ++ show gen
  show (BreakIf cond) = "until " ++ show cond
  show (NextIf cond) = "unless " ++ show cond
  show (NormalStmt stmt) = show stmt
  


instance Show Exp where
  show (IntValue i) = show i
  show (FloatValue f) = show f
  show (StringValue s) = show s
  show (CharValue c) = show c
  show (Var name) = name
  show (Where stmts exp) = show exp ++ " where " ++ show stmts
  show (CondExp cond thn els) = 
    "if " ++ show cond ++ " then " ++ show thn ++ " else " ++ show els
  show (Fncall fn args) = 
    fn ++ "(" ++ intercalate ", " (List.map show args) ++ ")"

instance Show Generator where
  show (In var exp) = var ++ " in " ++ show exp
  show (InRange var start step Nothing) =
    var ++ " from " ++ show start ++ " by " ++ show step
  show (InRange var start step (Just end)) =
    show (InRange var start step Nothing) ++ " to " ++ show end
