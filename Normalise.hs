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

modAddProc :: Ident -> (Int, ProcProto, [Placed Prim], (Maybe SourcePos))
              -> Module -> Module
modAddProc name (newid, proto, stmts, pos) mod
  = let procs = modProcs mod
        defs  = ProcDef newid proto stmts pos:
                            findWithDefault [] name procs
                in  mod { modProcs  = Map.insert name defs procs }

modReplaceProc :: Ident -> (Int, ProcProto, [Placed Prim], (Maybe SourcePos)) 
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


makeMessage :: String -> Maybe SourcePos -> String
makeMessage msg Nothing = msg
makeMessage msg (Just pos) =
  (sourceName pos) ++ ":" ++ 
  show (sourceLine pos) ++ ":" ++ 
  show (sourceColumn pos) ++ ": " ++ 
  msg

errMsg :: String -> Maybe SourcePos -> Expander ()
errMsg msg pos = do
  state <- get
  put state { errs = (errs state) ++ [makeMessage msg pos] }

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

addProc :: Ident -> ProcProto -> [Placed Prim] -> (Maybe SourcePos)
           -> Visibility -> Expander ()
addProc name proto stmts pos vis = do
  newid <- nextProcId
  addItem modAddProc
          (\name mod -> mod { pubProcs = Set.insert name $ pubProcs mod })
          name (newid, proto, stmts, pos) vis

replaceProc :: Ident -> Int -> ProcProto -> [Placed Prim] -> (Maybe SourcePos)
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
normaliseItem (TypeDecl vis (TypeProto name params) ctrs pos) = do
  addType name (TypeDef (length params) pos) vis
  if vis == Public then
      mapM_ (addCtr $ TypeSpec name $ 
             List.map (\var -> TypeSpec var []) params) ctrs
    else
    return ()
normaliseItem (NonAlgType vis (TypeProto name params) items pos) =
  addType name (TypeDef (length params) pos) vis
normaliseItem (ResourceDecl vis name typ pos) =
  addResource name (SimpleResource typ pos) vis
normaliseItem (FuncDecl vis (FnProto name params) resulttype result pos) =
  normaliseItem $
  ProcDecl 
  vis
  (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
  [Unplaced $
   ProcCall "=" [ProcArg (Unplaced $ Var "$") ParamOut, 
                 ProcArg result ParamIn]]
  pos
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) = do
  stmts' <- normaliseStmts stmts
  addProc name proto stmts' pos vis
normaliseItem (StmtDecl stmt pos) = do
  stmts <- normaliseStmt stmt pos
  oldproc <- lookupProc ""
  case oldproc of
    Nothing -> 
      addProc "" (ProcProto "" []) stmts Nothing Private
    Just [ProcDef id proto stmts' pos'] ->
      replaceProc "" id proto (stmts' ++ stmts) pos' Private


addCtr :: TypeSpec -> FnProto -> Expander ()
addCtr resultType (FnProto ctorName params) =
  normaliseItem (FuncDecl Public (FnProto ctorName params) resultType 
                 (List.foldr
                  (\(Param var _ _) struct ->
                    (Unplaced $ Fncall 
                     ("update$"++var) 
                     [Unplaced $ Var var,struct]))
                  (Unplaced $ Fncall "$alloc" [Unplaced $ Var ctorName])
                  $ List.reverse params) 
                 Nothing)


normaliseStmts :: [Placed Stmt] -> Expander [Placed Prim]
normaliseStmts [] = return []
normaliseStmts (stmt:stmts) = do
  front <- case stmt of
    Placed stmt' pos -> normaliseStmt stmt' $ Just pos
    Unplaced stmt'   -> normaliseStmt stmt' Nothing
  back <- normaliseStmts stmts
  return $ front ++ back

normaliseStmt :: Stmt -> Maybe SourcePos -> Expander [Placed Prim]
normaliseStmt (ProcCall name args) pos = do
  (args',stmts) <- normaliseArgs args
  return $ stmts ++ [maybePlace (PrimCall name Nothing args') pos]
normaliseStmt (ForeignCall lang name args) pos = do
  (args',stmts) <- normaliseArgs args
  return $ stmts ++ [maybePlace (PrimForeign lang name Nothing args') pos]
normaliseStmt (Cond exp thn els) pos = do
  (exp',condstmts) <- normaliseExp exp ParamIn
  thn' <- normaliseStmts thn
  els' <- normaliseStmts els
  stmts <- makeCond exp' [thn',els'] pos
  return $ condstmts ++ stmts
normaliseStmt (Loop loop) pos = do
  (init,body,update) <- normaliseLoopStmts loop
  return $ init ++ [maybePlace (PrimLoop $ body++update) pos]
normaliseStmt Nop pos = do
  return $ []

normaliseLoopStmts :: [Placed LoopStmt] -> 
                      Expander ([Placed Prim],[Placed Prim],[Placed Prim])
normaliseLoopStmts [] = return ([],[],[])
normaliseLoopStmts (stmt:stmts) = do
  (backinit,backbody,backupdate) <- normaliseLoopStmts stmts
  (frontinit,frontbody,frontupdate) <- case stmt of
    Placed stmt' pos -> normaliseLoopStmt stmt' $ Just pos
    Unplaced stmt'   -> normaliseLoopStmt stmt' Nothing
  return $ (frontinit ++ backinit, 
            frontbody ++ backbody,
            frontupdate ++ backupdate)

normaliseLoopStmt :: LoopStmt -> Maybe SourcePos -> 
                     Expander ([Placed Prim],[Placed Prim],[Placed Prim])
normaliseLoopStmt (For gen) pos = normaliseGenerator gen pos
normaliseLoopStmt (BreakIf exp) pos = do
  (exp',stmts) <- normaliseExp exp ParamIn
  cond <- freshVar
  return $ ([],stmts ++ [assign cond exp',maybePlace (PrimBreakIf cond) pos],[])
normaliseLoopStmt (NextIf exp) pos = do
  (exp',stmts) <- normaliseExp exp ParamIn
  cond <- freshVar
  return ([],stmts ++ [assign cond exp',maybePlace (PrimNextIf cond) pos],[])
normaliseLoopStmt (NormalStmt stmt) pos = do
  stmts <- normaliseStmt (content stmt) pos
  return ([],stmts,[])


normaliseGenerator :: Generator -> Maybe SourcePos ->
                      Expander ([Placed Prim],[Placed Prim],[Placed Prim])
normaliseGenerator (In var exp) pos = do
  (arg,init) <- normaliseExp exp ParamIn
  stateVar <- freshVar
  testVar <- freshVar
  let update = procCall "next" [ArgVar stateVar ParamInOut,
                                ArgVar var ParamInOut,
                                ArgVar testVar ParamOut]
  return (init++[assign stateVar arg,update],
          [update],[Unplaced $ PrimBreakIf testVar])
normaliseGenerator (InRange var exp updateOp inc limit) pos = do
  (arg,init1) <- normaliseExp exp ParamIn
  (incArg,init2) <- normaliseExp inc ParamIn
  let update = [procCall updateOp 
                [ArgVar var ParamIn,incArg,ArgVar var ParamOut]]
  (init,test) <- case limit of
    Nothing -> return (init1++init2,[])
    Just (comp,limit') -> do
      testVar <- freshVar
      (limitArg,init3) <- normaliseExp limit' ParamIn
      return (init1++init2++init3,
              [procCall comp [ArgVar var ParamIn,limitArg,
                              ArgVar testVar ParamOut],
               Unplaced $ PrimBreakIf testVar])
  return (init++[assign var arg],test,update)


normaliseArgs :: [ProcArg] -> Expander ([PrimArg],[Placed Prim])
normaliseArgs [] = return ([],[])
normaliseArgs (ProcArg pexp dir:args) = do
  let pos = place pexp
  (arg,stmts) <- normaliseExp pexp dir
  (args',stmts') <- normaliseArgs args
  return (arg:args', stmts ++ stmts')

normaliseExp :: Placed Exp -> FlowDirection -> Expander (PrimArg,[Placed Prim])
normaliseExp exp dir = normaliseExp' (content exp) (place exp) dir

normaliseExp' :: Exp -> Maybe SourcePos -> FlowDirection ->
                 Expander (PrimArg,[Placed Prim])
normaliseExp' (IntValue a) pos dir = do
  mustBeIn dir pos
  return (ArgInt a, [])
normaliseExp' (FloatValue a) pos dir = do
  mustBeIn dir pos
  return (ArgFloat a, [])
normaliseExp' (StringValue a) pos dir = do
  mustBeIn dir pos
  return (ArgString a, [])
normaliseExp' (CharValue a) pos dir = do
  mustBeIn dir pos
  return (ArgChar a, [])
normaliseExp' (Var name) pos dir = do
  return (ArgVar name dir, [])
normaliseExp' (Where stmts exp) pos dir = do
  mustBeIn dir pos
  stmts1 <- normaliseStmts stmts
  (exp',stmts2) <- normaliseExp exp ParamIn
  return (exp', stmts1++stmts2)
normaliseExp' (CondExp cond thn els) pos dir = do
  mustBeIn dir pos
  (cond',stmtscond) <- normaliseExp cond ParamIn
  (thn',stmtsthn) <-normaliseExp thn ParamIn
  (els',stmtsels) <-normaliseExp els ParamIn
  result <- freshVar
  prims <- makeCond cond' 
           [stmtsthn++[assign result thn'], stmtsels++[assign result els']]
           pos
  return (ArgVar result ParamIn, stmtscond++prims)
normaliseExp' (Fncall name exps) pos dir = do
  mustBeIn dir pos
  (exps',stmts) <- normaliseExps exps
  result <- freshVar
  return (ArgVar result ParamIn, 
          stmts++[maybePlace
                  (PrimCall name Nothing 
                   (exps'++[ArgVar result ParamOut])) 
                  pos])
normaliseExp' (ForeignFn lang name exps) pos dir = do
  mustBeIn dir pos
  (exps',stmts) <- normaliseExps exps
  result <- freshVar
  return (ArgVar result ParamIn, 
          stmts++[maybePlace
                  (PrimForeign lang name Nothing 
                   (exps'++[ArgVar result ParamOut])) 
                  pos])

mustBeIn :: FlowDirection -> Maybe SourcePos -> Expander ()
mustBeIn ParamIn _ = return ()
mustBeIn ParamOut pos = do
  errMsg "Flow error:  invalid output argument" pos
mustBeIn ParamInOut pos = do
  errMsg "Flow error:  invalid input/output argument" pos


assign :: VarName -> PrimArg -> Placed Prim
assign var val = procCall "=" [ArgVar var ParamOut, val]

procCall :: ProcName -> [PrimArg] -> Placed Prim
procCall proc args = Unplaced $ PrimCall proc Nothing args

makeCond :: PrimArg -> [[Placed Prim]] -> Maybe SourcePos -> 
            Expander [Placed Prim]
makeCond cond branches pos = do
  case cond of
    ArgVar name ParamIn -> do
      result <- freshVar
      return [maybePlace (PrimCond name branches) pos]
    ArgInt n ->
      if n >= 0 && n <= fromIntegral (length branches) then
        return $ branches !! (fromInteger n)
      else
        return $ head branches
    _ -> do
      errMsg "Can't use a non-integer type as a Boolean" pos
      return $ head branches -- XXX has the right type, but probably not good


normaliseExps :: [Placed Exp] -> Expander ([PrimArg],[Placed Prim])
normaliseExps [] = return ([],[])
normaliseExps (exp:exps) = do
  (args',stmts2) <- normaliseExps exps
  (exp',stmts1) <- normaliseExp exp ParamIn
  return  (exp':args', stmts1 ++ stmts2)

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
