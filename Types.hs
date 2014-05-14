--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (typeCheckModSCC) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Data.Maybe
import Data.Graph

import Debug.Trace

-- |The reason a variable is given a certain type
data TypeReason = ReasonParam ProcName Int OptPos
                                      -- Formal param type/flow inconsistent
                | ReasonArg ProcName Int OptPos
                                      -- Actual param type/flow inconsistent
                | ReasonAmbig ProcName ProcName OptPos
                                      -- Proc call is ambiguous
                | ReasonUndef ProcName ProcName OptPos
                                      -- Call to unknown proc
                | ReasonArity ProcName ProcName OptPos Int Int
                                      -- Call to proc with wrong arity
                deriving (Eq)

instance Show TypeReason where
    show (ReasonParam name num pos) =
        makeMessage pos $
            "Type/flow error in definition of " ++ name ++
            ", parameter " ++ show num
    show (ReasonArg name num pos) =
        makeMessage pos $
            "Type/flow error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonAmbig callFrom callTo pos) =
        makeMessage pos $
            "Ambiguous call to overloaded " ++ callTo ++ " from " ++ callFrom
    show (ReasonUndef callFrom callTo pos) =
        makeMessage pos $
            "Call to unknown " ++ callTo ++ " from " ++ callFrom
    show (ReasonArity callFrom callTo pos callArity procArity) =
        makeMessage pos $
            "Call from " ++ callFrom ++ " to " ++ callTo ++ " with " ++
            show callArity ++ " arguments, expected " ++ show procArity

data Typing = ValidTyping (Map VarName TypeSpec)
            | InvalidTyping TypeReason   -- call type conflicts w/callee
            deriving (Show,Eq)

initTyping :: Typing
initTyping = ValidTyping Map.empty


validTyping :: Typing -> Bool
validTyping (ValidTyping _) = True
validTyping _ = False


addOneType :: TypeReason -> PrimVarName -> TypeSpec -> Typing -> Typing
addOneType reason (PrimVarName name _) typ valid@(ValidTyping types) =
    case Map.lookup name types of
        Nothing -> ValidTyping $ Map.insert name typ types
        Just oldTyp ->
            if typ == oldTyp 
            then valid
            else if typ `properSubtypeOf` oldTyp
                 then ValidTyping $ Map.insert name typ types
                 else InvalidTyping reason
addOneType _ _ _ invalid = invalid


-- |Returns the first argument restricted to the variables appearing 
--  in the second.
projectTyping :: Typing -> Typing -> Typing
projectTyping (ValidTyping typing) (ValidTyping interest) =
    ValidTyping $
    Map.filterWithKey (\k _ -> isJust $ Map.lookup k interest) typing
projectTyping typing _ = typing


-- Simple subtype relation for now; every type is a subtype of the 
-- unspecified type.
properSubtypeOf :: TypeSpec -> TypeSpec -> Bool
properSubtypeOf _ Unspecified = True
properSubtypeOf _ _ = False


subtypeOf :: TypeSpec -> TypeSpec -> Bool
subtypeOf sub super = sub == super || sub `properSubtypeOf` super


-- |Type check a strongly connected component in the module dependency graph.
--  This code assumes that all lower sccs have already been checked.
typeCheckModSCC :: [ModSpec] -> Compiler ()
typeCheckModSCC [modspec] = do  -- immediate fixpoint when no mutual dependency
    typeCheckMod [modspec] modspec
    return ()
typeCheckModSCC scc = do        -- must find fixpoint
    changed <- mapM (typeCheckMod scc) scc
    when (or changed) $ typeCheckModSCC scc


-- |Type check a single module named in the second argument; the 
--  first argument is a list of all the modules in this module 
-- dependency SCC.
-- XXX must check submodules, too.
typeCheckMod :: [ModSpec] -> ModSpec -> Compiler Bool
typeCheckMod modSCC thisMod = do
    -- liftIO $ putStrLn $ "Type checking module " ++ showModSpec thisMod
    reenterModule thisMod
    procs <- getModule (Map.toList . modProcs . fromJust . modImplementation)
    let ordered =
            stronglyConnComp
            [(name,name,
              nub $ concatMap (localBodyProcs thisMod . procBody) procs)
             | (name,procs) <- procs]
    (changed,reasons) <-
        foldM (\(chg,rs) scc -> do
                 (chg1,rs1) <- typecheckProcSCC thisMod modSCC scc
                 return (chg1 || chg, rs1++rs))
        (False,[])
        ordered
    finishModule
    unless changed
        (mapM_ (\r -> message Error (show r) Nothing) reasons)
    return changed


localBodyProcs :: ModSpec -> ProcBody -> [Ident]
localBodyProcs thisMod (ProcBody prims fork) =
    localCalledProcs thisMod (List.map content prims) ++
    localForkProcs thisMod fork


-- |The list of procs in the current module called in the specified 
--  list of prims.  
localCalledProcs :: ModSpec -> [Prim] -> [Ident]
localCalledProcs _ [] = []
localCalledProcs thisMod (PrimCall [] name _ _:rest) =
    name:localCalledProcs thisMod rest
localCalledProcs thisMod (PrimCall m name _ _:rest)
  | m == thisMod = name:localCalledProcs thisMod rest
localCalledProcs thisMod (_:rest) = localCalledProcs thisMod rest


localForkProcs :: ModSpec -> PrimFork -> [Ident]
localForkProcs _ NoFork = []
localForkProcs thisMod (PrimFork _ bodies) =
    concatMap (localBodyProcs thisMod) bodies


-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred 
--  types are more specific than the old ones and some proc(s) in the 
--  SCC depend on procs in the list of mods.  In this case, we will 
--  have to rerun the typecheck after typechecking the other modules 
--  on that list. 
typecheckProcSCC :: ModSpec -> [ModSpec] -> SCC ProcName ->
                    Compiler (Bool,[TypeReason])
typecheckProcSCC m mods (AcyclicSCC name) = do
    -- A single pass is always enough for non-cyclic SCCs
    -- liftIO $ putStrLn $ "Type checking non-recursive proc " ++ name
    (_,allAgain,reasons) <- typecheckProcDefs m mods name
    return (allAgain,reasons)
typecheckProcSCC m mods (CyclicSCC list) = do
    -- liftIO $ putStrLn $ "Type checking recursive procs " ++ 
    --   intercalate ", " list
    -- liftIO $ putStrLn $ "type checking " ++ show list ++ "..."
    (modAgain,allAgain,reasons) <-
        foldM (\(modAgain,allAgain,rs) name -> do
                    (modAgain',allAgain',reasons) 
                        <- typecheckProcDefs m mods name
                    return (modAgain || modAgain', 
                            allAgain || allAgain',
                           reasons++rs))
        (False, False, []) list
    if modAgain
      then typecheckProcSCC m mods $ CyclicSCC list
      else return (allAgain,reasons)


-- |Type check a list of procedure definitions and update the 
--  definitions stored in the Compiler monad.  Returns a pair of 
--  Bools, the first saying whether any defnition has been udpated, 
--  and the second saying whether any public defnition has been 
--  updated.
typecheckProcDefs :: ModSpec -> [ModSpec] -> ProcName -> 
                     Compiler (Bool,Bool,[TypeReason])
typecheckProcDefs m mods name = do
    
    defs <- getModule (Map.findWithDefault (error "missing proc definition")
                       name . modProcs . fromJust . modImplementation)
    (revdefs,modAgain,allAgain,reasons) <- 
        foldM (\(ds,modAgain,allAgain,rs) def -> do
                    (d,mA,aA,rs') <- typecheckProcDef m mods def
                    return (d:ds,modAgain || mA,allAgain || aA,rs'++rs))
        ([],False,False,[]) defs
    when modAgain $
      updateModImplementation
      (\imp -> imp { modProcs = Map.insert name (reverse revdefs) 
                                $ modProcs imp })
    return (modAgain,allAgain,reasons)
    

-- |Type check a single procedure definition.
typecheckProcDef :: ModSpec -> [ModSpec] -> ProcDef ->
                    Compiler (ProcDef,Bool,Bool,[TypeReason])
typecheckProcDef m mods pd@(ProcDef name proto@(PrimProto pn params) 
                         def pos tmpCnt vis) 
  = do
    let typing = List.foldr (addDeclaredType name pos)
                 initTyping $ zip params [1..]
    if validTyping typing
      then do
        -- liftIO $ putStrLn $ "** Type checking " ++ name ++
        --   ": " ++ show typing
        (typing',def') <- typecheckBody m mods name pos typing def
        -- liftIO $ putStrLn $ "*resulting types " ++ name ++
        --   ": " ++ show typing'
        let params' = updateParamTypes typing' params
        let pd' = ProcDef name (PrimProto pn params') def' pos tmpCnt vis
        let modAgain = pd' /= pd
        -- when modAgain
        --      (liftIO $ putStrLn $ "** check again " ++ name ++
        --              "\n-----------------OLD:" ++ showProcDef 4 pd ++
        --              "\n-----------------NEW:" ++ showProcDef 4 pd' ++ "\n")
        return (pd',modAgain,modAgain && vis == Public,
                   case typing' of
                     ValidTyping _ -> []
                     InvalidTyping r -> [r])
      else
        shouldnt $ "Inconsistent param typing for proc " ++ name


addDeclaredType :: ProcName -> OptPos -> (PrimParam,Int) -> Typing -> Typing
addDeclaredType procname pos (PrimParam name typ _ _,argNum) typs =
     addOneType (ReasonParam procname argNum pos) name typ typs


updateParamTypes :: Typing -> [PrimParam] -> [PrimParam]
updateParamTypes (ValidTyping dict) params =
    List.map (\p@(PrimParam name@(PrimVarName n _) typ fl afl) ->
               case Map.lookup n dict of
                   Nothing -> p
                   Just newTyp -> (PrimParam name newTyp fl afl)) params
updateParamTypes _ params = params


-- |Type check the body of a single proc definition by type checking 
--  each clause in turn using the declared parameter typing plus the 
--  typing of all parameters inferred from previous clauses.  We can 
--  stop once we've found a contradiction.
typecheckBody :: ModSpec -> [ModSpec] -> ProcName -> OptPos -> Typing ->
                 ProcBody -> Compiler (Typing,ProcBody)
typecheckBody m mods name pos paramTypes body@(ProcBody prims fork) = do
    bodyTypes <- typecheckPrims m mods name paramTypes prims
    case bodyTypes of
      [] -> do
        -- liftIO $ putStrLn $ "   no valid type"
        return (InvalidTyping $ ReasonAmbig name "nothing" pos,body)
      [(typing,prims')] -> do
        -- liftIO $ putStrLn $ "   final typing: " ++ show typing
        -- liftIO $ putStrLn $ "   final body: " ++ show prims'
        let typing' = projectTyping typing paramTypes
        when (typing' /= typing)
                   (error "Typing not projected onto parameters!")
        -- XXX must typecheck fork
        return (typing', ProcBody prims' fork)
      ((_,b1):(_,b2):_) -> do
        case diffCall b1 b2 of
          Nothing -> shouldnt "ambiguity with no difference"
          Just (callee,callPos) ->
              return (InvalidTyping $ ReasonAmbig name callee callPos,body)


diffCall :: [Placed Prim] -> [Placed Prim] -> Maybe (ProcName,OptPos)
diffCall [] _ = Nothing
diffCall _ [] = Nothing
diffCall (c1:c1s) (c2:c2s)
    | c1 == c2  = diffCall c1s c2s
    | otherwise = callDifference (place c1) (content c1) (content c2)

callDifference :: OptPos -> Prim -> Prim -> Maybe (ProcName,OptPos)
callDifference pos (PrimCall _ name _ _) _ = Just (name,pos)
callDifference _ _ _ = shouldnt "impossible ambiguity"


-- |Type all prims in a clause starting with one possible parameter 
--  typing and producing all possible typings and the corresponding 
--  clause body.  The clause is returned in reverse.
typecheckPrims :: ModSpec -> [ModSpec] -> ProcName -> Typing ->
                  [Placed Prim] -> Compiler [(Typing,[Placed Prim])]
typecheckPrims m mods caller types prims = do
    clauseTypes <- foldM (typecheckPlacedPrim m mods caller) [(types,[])] prims
    return $ List.map (\(clTyping,cl) ->
                        (projectTyping clTyping types, reverse cl))
      clauseTypes

-- |Type check a single placed primitive operation given a list of 
--  possible starting typings and corresponding clauses up to this prim.
typecheckPlacedPrim :: ModSpec -> [ModSpec] -> ProcName -> 
                       [(Typing,[Placed Prim])] ->
                       Placed Prim -> Compiler [(Typing,[Placed Prim])]
typecheckPlacedPrim m mods caller possibilities pprim = do
    -- liftIO $ putStrLn $ "Type checking prim " ++ show pprim
    possposs <- mapM (typecheckPrim m mods caller
                      (content pprim) (place pprim)) 
                possibilities
    -- liftIO $ putStrLn $ "Done checking prim " ++ show pprim
    return $ concat possposs
    

-- |Type check a single primitive operation, producing a list of 
--  possible typings and corresponding clauses.
typecheckPrim :: ModSpec -> [ModSpec] -> ProcName -> Prim -> OptPos ->
                 (Typing,[Placed Prim]) ->
                 Compiler [(Typing,[Placed Prim])]
typecheckPrim m mods caller prim pos (typing,body) = do
    possibilities <- typecheckSingle m mods caller prim pos typing
    return $ List.map (\(typing',prim') -> 
                        (typing',maybePlace prim' pos:body)) possibilities


-- |Type check one primitive operation, producing a list of 
--  possible typings and corresponding resolved primitives.
typecheckSingle :: ModSpec -> [ModSpec] -> ProcName -> Prim -> OptPos -> 
                   Typing -> Compiler [(Typing,Prim)]
typecheckSingle m mods caller call@(PrimCall cm name id args) pos typing = do
    -- liftIO $ putStrLn $ "Type checking call " ++ show call
    -- liftIO $ putStrLn $ "   with types " ++ show typing
    procs <- case id of
        Nothing   -> callTargets cm name
        Just spec -> return [spec]
    -- liftIO $ putStrLn $ "   " ++ show (length procs) ++ " potential procs"
    if List.null procs 
    then
      return [(InvalidTyping $ ReasonUndef caller name pos,
               PrimCall cm name id args)]
    else do
      pairsList <- mapM (\p -> do
                           params <- getParams p
                           -- liftIO $ putStrLn $ "   checking call to " ++
                           --        show p ++ " args " ++
                           --        show args ++ " against params " ++
                           --        show params
                           if length params == length args
                           then do
                             let (typing',revArgs) =
                                     List.foldr (typecheckArg pos $
                                                 procSpecName p) 
                                     (typing,[]) $ zip3 [1..] params args
                             return [(typing',
                                      PrimCall cm name (Just p) revArgs)]
                           else
                               return [(InvalidTyping $ 
                                        ReasonArity caller name pos
                                        (length args) (length params),
                                        call)])
                   procs
      let pairs = concat pairsList
      -- liftIO $ putStrLn $ "candidates: " ++ show pairs
      let validPairs = List.filter (validTyping . fst) pairs
      -- liftIO $ putStrLn $ "   " ++ show (length validPairs) ++ " matching procs"
      if List.null validPairs 
      then do
          return $ [(fst $ List.head pairs,call)]
          -- return [(typing,PrimCall cm name id args)]
      else
          return validPairs
typecheckSingle _ _ _ (PrimForeign lang name id args) pos typing = do
    -- XXX? must get type and flow from foreign calls?
    return [(typing,PrimForeign lang name id args)]
typecheckSingle _ _ _ PrimNop pos typing = return [(typing,PrimNop)]


argType :: Typing -> PrimArg -> TypeSpec
argType (ValidTyping dict) (ArgVar (PrimVarName var _) typ _ _) = 
    fromMaybe typ (Map.lookup var dict)
argType _ (ArgVar _ typ _ _) = typ
argType _ (ArgInt _ _)     = (TypeSpec ["wybe"] "int" [])
argType _ (ArgFloat _ _)   = (TypeSpec ["wybe"] "float" [])
argType _ (ArgString _ _)  = (TypeSpec ["wybe"] "string" [])
argType _ (ArgChar _ _)    = (TypeSpec ["wybe"] "char" [])


typecheckArg :: OptPos -> ProcName -> (Int,PrimParam,PrimArg) ->
                (Typing,[PrimArg]) -> (Typing,[PrimArg])
typecheckArg pos pname (argNum,param,arg) (typing,args) =
    let actualFlow = argFlowDirection arg
        formalFlow = primParamFlow param
        reason = ReasonArg pname argNum pos
    in  if not $ validTyping typing
        then (typing,args)
        else if formalFlow /= actualFlow
             then -- trace ("wrong flow: " ++ show arg ++ " against " ++ show param) 
                      (InvalidTyping reason,args)
             else -- trace ("OK flow: " ++ show arg ++ " against " ++ show param)
                  typecheckArg' arg (primParamType param) typing args reason


typecheckArg' :: PrimArg -> TypeSpec -> Typing -> [PrimArg] -> TypeReason ->
                 (Typing,[PrimArg])
typecheckArg' (ArgVar var _ flow ftype) paramType typing args reason =
    (addOneType reason var paramType typing, 
     ArgVar var paramType flow ftype:args)
-- XXX type specs below should include "wybe" module
typecheckArg' (ArgInt val callType) paramType typing args reason =
    typecheckArg'' callType paramType (TypeSpec [] "int" [])
                   typing args reason $ ArgInt val
typecheckArg' (ArgFloat val callType) paramType typing args reason =
    typecheckArg'' callType paramType (TypeSpec [] "float" [])
                   typing args reason $ ArgFloat val
typecheckArg' (ArgString val callType) paramType typing args reason =
    typecheckArg'' callType paramType (TypeSpec [] "string" [])
                   typing args reason $ ArgString val
typecheckArg' (ArgChar val callType) paramType typing args reason =
    typecheckArg'' callType paramType (TypeSpec [] "char" [])
                   typing args reason $ ArgChar val
                        

typecheckArg'' :: TypeSpec -> TypeSpec -> TypeSpec -> Typing -> [PrimArg] ->
                  TypeReason -> (TypeSpec -> PrimArg) -> (Typing,[PrimArg])
typecheckArg'' callType paramType constType typing args reason mkArg =
    let realType =
            if constType `subtypeOf` callType then constType else callType
    in -- trace ("check call type " ++ show callType ++ " against param type " ++ show paramType ++ " for const type " ++ show constType)
           (if paramType `subtypeOf` realType
            then typing
            else InvalidTyping reason,
            mkArg paramType:args)
