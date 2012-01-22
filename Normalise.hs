--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Normalise (normalise) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos

normalise :: Compiler ()
normalise = do
    items <- getState parseTree
    mapM_ normaliseItem items

normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) items pos) = do
    compileSubmodule items name (Just params) pos vis normalise
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
normaliseItem (CtorDecl vis proto pos) = do
    modname <- getModuleName
    Just modparams <- getModuleParams
    addCtor modname modparams proto
normaliseItem (StmtDecl stmt pos) = do
  stmts <- normaliseStmt stmt pos
  oldproc <- lookupProc ""
  case oldproc of
    Nothing -> 
      addProc "" (ProcProto "" []) stmts Nothing Private
    Just [ProcDef id proto stmts' pos'] ->
      replaceProc "" id proto (stmts' ++ stmts) pos' Private


addCtor :: Ident -> [Ident] -> FnProto -> Compiler ()
addCtor typeName typeParams (FnProto ctorName params) = do
    let typespec = TypeSpec typeName $ List.map (\n->TypeSpec n []) typeParams
    normaliseItem (FuncDecl Public (FnProto ctorName params)
                   typespec
                   (List.foldr
                    (\(Param var _ _) struct ->
                      (Unplaced $ Fncall 
                       ("update$"++var) 
                       [Unplaced $ Var var,struct]))
                    (Unplaced $ Fncall "$alloc" [Unplaced $ Var ctorName])
                    $ List.reverse params) 
                   Nothing)
    mapM_ (addGetterSetter typespec ctorName) params

addGetterSetter :: TypeSpec -> Ident -> Param -> Compiler ()
addGetterSetter rectype ctorName (Param field fieldtype _) = do
    addProc field 
      (ProcProto field [Param "$rec" rectype ParamIn,
                        Param "$field" fieldtype ParamOut])
      [Unplaced $ PrimForeign "" "access" Nothing [ArgVar ctorName ParamIn,
                                                   ArgVar "$rec" ParamIn,
                                                   ArgVar "$field" ParamOut]]
      Nothing Public
    addProc field 
      (ProcProto field [Param "$rec" rectype ParamInOut,
                        Param "$field" fieldtype ParamIn])
      [Unplaced $ PrimForeign "" "mutate" Nothing [ArgVar ctorName ParamIn,
                                                   ArgVar "$rec" ParamInOut,
                                                   ArgVar "$field" ParamIn]]
      Nothing Public

normaliseStmts :: [Placed Stmt] -> Compiler [Placed Prim]
normaliseStmts [] = return []
normaliseStmts (stmt:stmts) = do
  front <- case stmt of
    Placed stmt' pos -> normaliseStmt stmt' $ Just pos
    Unplaced stmt'   -> normaliseStmt stmt' Nothing
  back <- normaliseStmts stmts
  return $ front ++ back

normaliseStmt :: Stmt -> Maybe SourcePos -> Compiler [Placed Prim]
normaliseStmt (ProcCall name args) pos = do
  (args',stmts) <- normaliseArgs args
  return $ stmts ++ [maybePlace (PrimCall name Nothing args') pos]
normaliseStmt (ForeignCall lang name args) pos = do
  (args',stmts) <- normaliseArgs args
  return $ stmts ++ [maybePlace (PrimForeign lang name Nothing args') pos]
normaliseStmt (Cond exp thn els) pos = do
  (exp',condstmts) <- normalisePlacedExp exp ParamIn
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
                      Compiler ([Placed Prim],[Placed Prim],[Placed Prim])
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
                     Compiler ([Placed Prim],[Placed Prim],[Placed Prim])
normaliseLoopStmt (For gen) pos = normaliseGenerator gen pos
normaliseLoopStmt (BreakIf exp) pos = do
  (exp',stmts) <- normalisePlacedExp exp ParamIn
  cond <- freshVar
  return $ ([],stmts ++ [assign cond exp',maybePlace (PrimBreakIf cond) pos],[])
normaliseLoopStmt (NextIf exp) pos = do
  (exp',stmts) <- normalisePlacedExp exp ParamIn
  cond <- freshVar
  return ([],stmts ++ [assign cond exp',maybePlace (PrimNextIf cond) pos],[])
normaliseLoopStmt (NormalStmt stmt) pos = do
  stmts <- normaliseStmt (content stmt) pos
  return ([],stmts,[])


normaliseGenerator :: Generator -> Maybe SourcePos ->
                      Compiler ([Placed Prim],[Placed Prim],[Placed Prim])
normaliseGenerator (In var exp) pos = do
  (arg,init) <- normalisePlacedExp exp ParamIn
  stateVar <- freshVar
  testVar <- freshVar
  let update = procCall "next" [ArgVar stateVar ParamInOut,
                                ArgVar var ParamInOut,
                                ArgVar testVar ParamOut]
  return (init++[assign stateVar arg,update],
          [update],[Unplaced $ PrimBreakIf testVar])
normaliseGenerator (InRange var exp updateOp inc limit) pos = do
  (arg,init1) <- normalisePlacedExp exp ParamIn
  (incArg,init2) <- normalisePlacedExp inc ParamIn
  let update = [procCall updateOp 
                [ArgVar var ParamIn,incArg,ArgVar var ParamOut]]
  (init,test) <- case limit of
    Nothing -> return (init1++init2,[])
    Just (comp,limit') -> do
      testVar <- freshVar
      (limitArg,init3) <- normalisePlacedExp limit' ParamIn
      return (init1++init2++init3,
              [procCall comp [ArgVar var ParamIn,limitArg,
                              ArgVar testVar ParamOut],
               Unplaced $ PrimBreakIf testVar])
  return (init++[assign var arg],test,update)


normaliseArgs :: [ProcArg] -> Compiler ([PrimArg],[Placed Prim])
normaliseArgs [] = return ([],[])
normaliseArgs (ProcArg pexp dir:args) = do
  let pos = place pexp
  (arg,stmts) <- normalisePlacedExp pexp dir
  (args',stmts') <- normaliseArgs args
  return (arg:args', stmts ++ stmts')

normalisePlacedExp :: Placed Exp -> FlowDirection -> Compiler (PrimArg,[Placed Prim])
normalisePlacedExp exp dir = normaliseExp (content exp) (place exp) dir


normaliseExp :: Exp -> Maybe SourcePos -> FlowDirection ->
                 Compiler (PrimArg,[Placed Prim])
normaliseExp (IntValue a) pos dir = do
  mustBeIn dir pos
  return (ArgInt a, [])
normaliseExp (FloatValue a) pos dir = do
  mustBeIn dir pos
  return (ArgFloat a, [])
normaliseExp (StringValue a) pos dir = do
  mustBeIn dir pos
  return (ArgString a, [])
normaliseExp (CharValue a) pos dir = do
  mustBeIn dir pos
  return (ArgChar a, [])
normaliseExp (Var name) pos dir = do
  return (ArgVar name dir, [])
normaliseExp (Where stmts exp) pos dir = do
  mustBeIn dir pos
  stmts1 <- normaliseStmts stmts
  (exp',stmts2) <- normalisePlacedExp exp ParamIn
  return (exp', stmts1++stmts2)
normaliseExp (CondExp cond thn els) pos dir = do
  mustBeIn dir pos
  (cond',stmtscond) <- normalisePlacedExp cond ParamIn
  (thn',stmtsthn) <-normalisePlacedExp thn ParamIn
  (els',stmtsels) <-normalisePlacedExp els ParamIn
  result <- freshVar
  prims <- makeCond cond' 
           [stmtsthn++[assign result thn'], stmtsels++[assign result els']]
           pos
  return (ArgVar result ParamIn, stmtscond++prims)
normaliseExp (Fncall name exps) pos dir = do
  mustBeIn dir pos
  (exps',stmts) <- normalisePlacedExps exps
  result <- freshVar
  return (ArgVar result ParamIn, 
          stmts++[maybePlace
                  (PrimCall name Nothing 
                   (exps'++[ArgVar result ParamOut])) 
                  pos])
normaliseExp (ForeignFn lang name exps) pos dir = do
  mustBeIn dir pos
  (exps',stmts) <- normalisePlacedExps exps
  result <- freshVar
  return (ArgVar result ParamIn, 
          stmts++[maybePlace
                  (PrimForeign lang name Nothing 
                   (exps'++[ArgVar result ParamOut])) 
                  pos])

mustBeIn :: FlowDirection -> Maybe SourcePos -> Compiler ()
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
            Compiler [Placed Prim]
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


normalisePlacedExps :: [Placed Exp] -> Compiler ([PrimArg],[Placed Prim])
normalisePlacedExps [] = return ([],[])
normalisePlacedExps (exp:exps) = do
  (args',stmts2) <- normalisePlacedExps exps
  (exp',stmts1) <- normalisePlacedExp exp ParamIn
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

