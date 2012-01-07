--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Normalise (normalise) where

import AST
import Printout
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos
import Control.Monad.State

----------------------------------------------------------------
--                    Monad used for normalising
--
-- While expanding items to an AST, monad holds the following data:
----------------------------------------------------------------

data ExpanderState = Expander {
  varCount :: Int,      -- a counter for introduced variables (per proc)
  procCount :: Int,     -- a counter for gensym-ed proc names
  modul :: Module,      -- the module being produced
  errs :: [String]      -- error messages
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


normalise :: [Item] -> (Module,[String])
normalise items = (modul result, errs result) where
  (_,result) = runState (normaliseItems items) initExpander

normaliseItems :: [Item] -> Expander ()
normaliseItems [] = return ()
normaliseItems (item:items) = do
  normaliseItem item
  normaliseItems items

normaliseItem :: Item -> Expander ()
normaliseItem (TypeDecl vis (TypeProto name params) ctrs pos) =
  addType name (TypeDef (length params) pos) vis
normaliseItem (ResourceDecl vis name typ pos) =
  addResource name (SimpleResource typ pos) vis
normaliseItem (FuncDecl vis (FnProto name params) resulttype result pos) =
  normaliseItem (ProcDecl vis
             (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
             [Unplaced (ProcCall "=" [ProcArg (Unplaced $ Var "$") 
                                      ParamOut, 
                                      ProcArg result ParamIn])]
             pos)
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) =
  addProc name proto stmts pos vis
normaliseItem (StmtDecl stmt pos) = do
  oldproc <- lookupProc ""
  case oldproc of
    Nothing -> 
      addProc "" (ProcProto "" []) [maybePlace stmt pos] Nothing Private
    Just [ProcDef id proto stmts pos'] ->
      replaceProc "" id proto (stmts ++ [maybePlace stmt pos]) pos' Private


-- expandExp :: Exp -> Expander [Prim]
-- expandExp 

----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
