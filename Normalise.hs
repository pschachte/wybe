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

initVars :: Expander ()
initVars = do
  state <- get
  put state { varCount = 0 }

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
             [assign "$" result]
             pos)
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) = do
  stmts' <- normaliseStmts stmts
  addProc name proto stmts' pos vis
normaliseItem (StmtDecl stmt pos) = do
  oldproc <- lookupProc ""
  case oldproc of
    Nothing -> 
      addProc "" (ProcProto "" []) [maybePlace stmt pos] Nothing Private
    Just [ProcDef id proto stmts pos'] ->
      replaceProc "" id proto (stmts ++ [maybePlace stmt pos]) pos' Private


normaliseStmts :: [Placed Stmt] -> Expander [Placed Stmt]
normaliseStmts [] = return []
normaliseStmts (stmt:stmts) = do
  front <- case stmt of
    Placed stmt' pos -> normaliseStmt stmt' $ Just pos
    Unplaced stmt'   -> normaliseStmt stmt' Nothing
  back <- normaliseStmts stmts
  return $ front ++ back

normaliseStmt :: Stmt -> Maybe SourcePos -> Expander [Placed Stmt]
normaliseStmt (ProcCall name args) pos = do
  (args',stmts) <- normaliseArgs args
  return $ stmts ++ [maybePlace (ProcCall name args') pos]
normaliseStmt (Cond exp thn els) pos = do
  (exp',stmts) <- normaliseExp exp
  thn' <- normaliseStmts thn
  els' <- normaliseStmts els
  return $ stmts ++ [maybePlace (Cond exp' thn' els') pos]
normaliseStmt (Loop loop) pos = do
  loop' <- normaliseLoopStmts loop
  return $ [maybePlace (Loop loop') pos]
normaliseStmt Nop pos = do
  return $ [maybePlace Nop pos]

normaliseLoopStmts :: [Placed LoopStmt] -> Expander [Placed LoopStmt]
normaliseLoopStmts [] = return []
normaliseLoopStmts (stmt:stmts) = do
  front <- case stmt of
    Placed stmt' pos -> normaliseLoopStmt stmt' $ Just pos
    Unplaced stmt'   -> normaliseLoopStmt stmt' Nothing
  back <- normaliseLoopStmts stmts
  return $ front ++ back

normaliseLoopStmt :: LoopStmt -> Maybe SourcePos -> Expander [Placed LoopStmt]
normaliseLoopStmt (For gen) pos = do
  return $ [maybePlace (For gen) pos]
normaliseLoopStmt (BreakIf exp) pos = do
  (exp',stmts) <- normaliseExp exp
  return $ (List.map (\s -> maybePlace (NormalStmt s) (place s)) stmts) ++ 
    [maybePlace (BreakIf exp') pos]
normaliseLoopStmt (NextIf exp) pos = do
  (exp',stmts) <- normaliseExp exp
  return $ (List.map (\s -> maybePlace (NormalStmt s) (place s)) stmts) ++
    [maybePlace (NextIf exp') pos]
normaliseLoopStmt (NormalStmt stmt) pos = do
  stmts <- normaliseStmt (content stmt) pos
  return $ (List.map (\s -> maybePlace (NormalStmt s) (place s)) stmts)


normaliseArgs :: [ProcArg] -> Expander ([ProcArg],[Placed Stmt])
normaliseArgs [] = return ([],[])
normaliseArgs (ProcArg pexp dir:args) = do
  let pos = place pexp
  (exp',stmts) <- normaliseExp pexp
  let arg' = ProcArg exp' dir
  (args',stmts') <- normaliseArgs args
  return (arg':args', stmts ++ stmts')

normaliseExp :: Placed Exp -> Expander (Placed Exp,[Placed Stmt])
normaliseExp exp = normaliseExp' (content exp) (place exp)

normaliseExp' :: Exp -> Maybe SourcePos -> Expander (Placed Exp,[Placed Stmt])
normaliseExp' exp@(IntValue i) pos = return (maybePlace exp pos, [])
normaliseExp' exp@(FloatValue i) pos = return (maybePlace exp pos, [])
normaliseExp' exp@(StringValue i) pos = return (maybePlace exp pos, [])
normaliseExp' exp@(CharValue i) pos = return (maybePlace exp pos, [])
normaliseExp' exp@(Var name) pos = return (maybePlace exp pos, [])
normaliseExp' (Where stmts exp) _ = do
  stmts1 <- normaliseStmts stmts
  (exp',stmts2) <- normaliseExp exp
  return (exp', stmts1++stmts2)
normaliseExp' (CondExp cond thn els) pos = do
  (cond',stmtscond) <- normaliseExp cond
  (thn',stmtsthn) <-normaliseExp thn
  (els',stmtsels) <-normaliseExp els
  result <- freshVar
  return (Unplaced $ Var result, 
          stmtscond++[maybePlace (Cond cond'
                                  (stmtsthn++[assign result thn'])
                                  (stmtsels++[assign result els']))
                      pos])
normaliseExp' (Fncall name exps) pos = do
  (exps',stmts) <- normaliseExps exps
  result <- freshVar
  return (Unplaced $ Var result, 
          stmts++[maybePlace 
                  (ProcCall name 
                   (exps'++[ProcArg (Unplaced $ Var result) ParamOut])) 
                  pos])

assign :: String -> Placed Exp -> Placed Stmt
assign var val = 
  Unplaced (ProcCall "=" [ProcArg (Unplaced $ Var var) ParamOut, 
                          ProcArg val ParamIn])

normaliseExps :: [Placed Exp] -> Expander ([ProcArg],[Placed Stmt])
normaliseExps [] = return ([],[])
normaliseExps (exp:exps) = do
  (args',stmts2) <- normaliseExps exps
  (exp',stmts1) <- normaliseExp exp
  return  (ProcArg exp' ParamIn:args', stmts1 ++ stmts2)

{- LValues:

!a.tl.hd = f(g(x)) 
   ==>
=(!hd(tl(a)), f(g(x))) 
   ==>
tl(!a, t1)    # replace a with a shallow copy, put address of tail into t1
hd(!*t1, t2)  # replace *t1 with a shallow copy, put address of head into t2
g(x,?t3)      # evalue g(x) into fresh t3
f(t3, ?t4)    # evaluate f(t3) into fresh t4
=(!*t2, t4)   # store value into destination

-}

----------------------------------------------------------------
--                         Generally Useful
----------------------------------------------------------------

applyIf :: (a -> a) -> Bool -> a -> a
applyIf f test val = if test then f val else val
