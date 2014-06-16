--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (typeCheckMod, checkFullyTyped) where

import AST
-- import Resources
import Util
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Data.Maybe
import Data.Graph

import Debug.Trace


-- |Type check a single module named in the second argument; the 
--  first argument is a list of all the modules in this module 
-- dependency SCC.
typeCheckMod :: ModSpec -> Compiler ()
typeCheckMod thisMod = do
    -- liftIO $ putStrLn $ "**** Type checking module " ++ showModSpec thisMod
    reenterModule thisMod
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(name, name, nub $ concatMap (localBodyProcs thisMod . procImpln) procDefs)
             | (name,procDefs) <- procs]
    errs <- mapM (typecheckProcSCC thisMod) ordered
    mapM_ (flip message Error Nothing) $ concat $ reverse errs
    finishModule
    -- liftIO $ putStrLn $ "**** Exiting module " ++ showModSpec thisMod
    return ()


----------------------------------------------------------------
--                           Supporting types
----------------------------------------------------------------


-- |The reason a variable is given a certain type
data TypeReason = ReasonParam ProcName Int OptPos
                                      -- Formal param type/flow inconsistent
                | ReasonUndef ProcName ProcName OptPos
                                      -- Call to unknown proc
                | ReasonUninit ProcName VarName OptPos
                                      -- Use of uninitialised variable
                | ReasonArgType ProcName Int OptPos
                                      -- Actual param type inconsistent
                | ReasonArgFlow ProcName Int OptPos
                                      -- Actual param flow inconsistent
                | ReasonOverload [ProcSpec] OptPos
                                      -- Multiple procs with same types/flows
                | ReasonAmbig ProcName OptPos [(VarName,[TypeSpec])]
                                      -- Proc defn has ambiguous types
                | ReasonArity ProcName ProcName OptPos Int Int
                                      -- Call to proc with wrong arity
                | ReasonUndeclared ProcName OptPos
                                      -- Public proc with some undeclared argument types
                deriving (Eq, Ord)

instance Show TypeReason where
    show (ReasonParam name num pos) =
        makeMessage pos $
            "Type/flow error in definition of " ++ name ++
            ", parameter " ++ show num
    show (ReasonArgType name num pos) =
        makeMessage pos $
            "Type error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonArgFlow name num pos) =
        makeMessage pos $
            "Flow error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonOverload pspecs pos) =
        makeMessage pos $
            "Ambiguous overloading: call could refer to:" ++
            List.concatMap (("\n    "++) . show) (reverse pspecs)
    show (ReasonAmbig procName pos varAmbigs) =
        makeMessage pos $
            "Type ambiguity in defn of " ++ procName ++ ":" ++
            concat ["\n    Variable '" ++ v ++ "' could be: " ++
                    intercalate ", " (List.map show typs)
                   | (v,typs) <- varAmbigs]
    show (ReasonUndef callFrom callTo pos) =
        makeMessage pos $
            "Call to unknown '" ++ callTo ++ "' from " ++ callFrom
    show (ReasonUninit callFrom var pos) =
        makeMessage pos $
            "Unknown variable/constant '" ++ var ++ "'"
    show (ReasonArity callFrom callTo pos callArity procArity) =
        makeMessage pos $
            (if callFrom == "" 
             then "Toplevel call" 
             else "Call from " ++ callFrom) ++
            " to " ++ callTo ++ " with " ++
            (if callArity == procArity
             then "unsupported argument flow"
             else show callArity ++ " arguments, expected " ++ show procArity)
    show (ReasonUndeclared name pos) =
        makeMessage pos $
        "Public definition of '" ++ name ++ "' with some undeclared types."

data Typing = ValidTyping (Map VarName TypeSpec)
            | InvalidTyping TypeReason   -- call type conflicts w/callee
            deriving (Show,Eq,Ord)

typingDict :: Typing -> Map VarName TypeSpec
typingDict (ValidTyping dict) = dict
typingDict (InvalidTyping _) = error "no typingDict for InvalidTyping"


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
                 else if oldTyp `properSubtypeOf` typ
                      then valid -- we already have a stronger type, keep it
                      else --trace ("addOneType " ++ name ++ ":" ++ show typ ++ 
                           --       " vs. " ++ show oldTyp ++ " FAILED") $
                           InvalidTyping reason
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


localBodyProcs :: ModSpec -> ProcImpln -> [Ident]
localBodyProcs thisMod (ProcDefSrc body) =
    foldProcCalls (localCalls thisMod) (++) [] body


localCalls :: ModSpec -> ModSpec -> Ident -> (Maybe Int) -> [Placed Exp] -> [Ident]
localCalls thisMod m name _ _
  | m == [] || m == thisMod = [name]
localCalls _ _ _ _ _ = []



----------------------------------------------------------------
--                         Type checking procs
----------------------------------------------------------------

-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred 
--  types are more specific than the old ones and some proc(s) in the 
--  SCC depend on procs in the list of mods.  In this case, we will 
--  have to rerun the typecheck after typechecking the other modules 
--  on that list. 
typecheckProcSCC :: ModSpec -> SCC ProcName -> Compiler ([TypeReason])
typecheckProcSCC m (AcyclicSCC name) = do
    -- A single pass is always enough for non-cyclic SCCs
    -- liftIO $ putStrLn $ "Type checking non-recursive proc " ++ name
    (_,reasons) <- typecheckProcDecls m name
    return (reasons)
typecheckProcSCC m mods (CyclicSCC list) = do
    -- liftIO $ putStrLn $ "**** Type checking recursive procs " ++ 
    --   intercalate ", " list
    (sccAgain,reasons) <-
        foldM (\(sccAgain,rs) name -> do
                    (sccAgain',reasons) <- typecheckProcDecls m name
                    return (sccAgain || sccAgain', reasons++rs))
        (False, []) list
    if sccAgain
    then typecheckProcSCC m $ CyclicSCC list
    else do
      -- liftIO $ putStrLn $ "**** Completed checking of " ++
      --        intercalate ", " list ++
      --        " with " ++ show (length reasons) ++ " errors"
      return (reasons)


-- |Type check a list of procedure definitions and update the 
--  definitions stored in the Compiler monad.  Returns a pair of 
--  Bools, the first saying whether any defnition has been udpated, 
--  and the second saying whether any public defnition has been 
--  updated.
typecheckProcDecls :: ModSpec -> [ModSpec] -> ProcName -> 
                     Compiler (Bool,[TypeReason])
typecheckProcDecls m mods name = do
    defs <- getModuleImplementationField 
            (Map.findWithDefault (error "missing proc definition")
             name . modProcs)
    (revdefs,sccAgain,reasons) <- 
        foldM (\(ds,sccAgain,rs) def -> do
                    (d,again,rs') <- typecheckProcDecl m def
                    return (d:ds,sccAgain || again,rs'++rs))
        ([],False,[]) defs
    updateModImplementation
      (\imp -> imp { modProcs = Map.insert name (reverse revdefs) 
                                $ modProcs imp })
    unless (sccAgain || not (List.null reasons)) $ do
        mapM_ checkProcDefFullytyped revdefs
    return (sccAgain,reasons)
    

-- |Type check a single procedure definition.
typecheckProcDecl :: ModSpec -> ProcDef -> Compiler (ProcDef,Bool,[TypeReason])
typecheckProcDecl m pd = do
    let name = procName pd
    let proto = procProto pd
    let params = procProtoParams proto
    let (ProcDefSrc def) = procImpln pd
    let pos = procPos pd
    let vis = procVis pd
    if vis == Public && any ((==Unspecified). paramType) params
      then return (pd,False,[ReasonUndeclared name pos])
      else do
        let typing = List.foldr (addDeclaredType name pos (length params))
                     initTyping $ zip params [1..]
        if validTyping typing
          then do
            -- liftIO $ putStrLn $ "** Type checking " ++ name ++
            --   ": " ++ show typing
            (typing',def') <- typecheckProcDef m name pos typing def
            -- liftIO $ putStrLn $ "*resulting types " ++ name ++
            --   ": " ++ show typing'
            let params' = updateParamTypes typing' params
            let proto' = proto { primProtoParams = params' }
            let pd' = pd { procProto = proto', procImpln = ProcDefSrc def' }
            let pd'' = pd'
            let sccAgain = pd'' /= pd
            -- pd'' <- if sccAgain then return pd' else resourceCheck pd'
            -- liftIO $ putStrLn $ "===== Definition is " ++ 
            --        (if sccAgain then "" else "un") ++ "changed"
            -- when sccAgain
            --      (liftIO $ putStrLn $ "** check again " ++ name ++
            --              "\n-----------------OLD:" ++ showProcDef 4 pd ++
            --              "\n-----------------NEW:" ++ showProcDef 4 pd' ++ "\n")
            return (pd'',sccAgain,
                    case typing' of
                        ValidTyping _ -> []
                        InvalidTyping r -> [r])
          else
            shouldnt $ "Inconsistent param typing for proc " ++ name


addDeclaredType :: ProcName -> OptPos -> Int -> (Param,Int) -> Typing -> Typing
addDeclaredType procname pos arity (Param name typ _ _,argNum) typs =
     addOneType (ReasonParam procname arity pos) name typ typs


updateParamTypes :: Typing -> [PrimParam] -> [PrimParam]
updateParamTypes (ValidTyping dict) params =
    List.map (\p@(PrimParam name@(PrimVarName n _) typ fl afl nd) ->
               case Map.lookup n dict of
                   Nothing -> p
                   Just newTyp -> (PrimParam name newTyp fl afl nd)) params
updateParamTypes _ params = params


-- |Type check the body of a single proc definition by type checking 
--  each clause in turn using the declared parameter typing plus the 
--  typing of all parameters inferred from previous clauses.  We can 
--  stop once we've found a contradiction.
typecheckProcDef :: ModSpec -> ProcName -> OptPos -> Typing ->
                     [Placed Stmt] -> Compiler (Typing,[Placed Stmt])
typecheckProcDef m mods name pos paramTypes body = do
    -- liftIO $ putStrLn $ "\ntype checking: " ++ name
    typings <- typecheckBody m mods name paramTypes body
    -- liftIO $ putStrLn $ "typings:  " ++
    --   intercalate "\n          " (List.map show typings) ++ "\n"
    case typings of
      [] -> do
        -- liftIO $ putStrLn $ "   no valid type"
          -- XXX This is the wrong reason
        return (InvalidTyping $ ReasonAmbig name pos [],body)
      [typing] -> do
        -- liftIO $ putStrLn $ "   final typing: " ++ show typing
        let typing' = projectTyping typing paramTypes
        case typing of
            InvalidTyping _ -> do
                -- liftIO $ putStrLn $ "invalid: no body typing" ++ showBlock 4 body
                return (typing', body)
            ValidTyping dict -> do
                -- liftIO $ putStrLn $ "apply body typing" ++ showBlock 4 body
                body' <- applyBodyTyping dict body
                -- liftIO $ putStrLn $ "After body typing:" ++ showBlock 4 body'
                return (typing',body')
      typings -> do
          -- liftIO $ putStrLn $ name ++ " has " ++ show (length typings) ++ 
          --   " typings, of which " ++
          --   show (length (List.filter validTyping typings)) ++
          --   " are valid"
          let typingSets = List.map (Map.map Set.singleton . typingDict) typings
          let merged = Map.filter ((>1).Set.size) $
                       Map.unionsWith Set.union typingSets
          let ambigs = List.map (\(v,ts) -> (v,Set.toAscList ts)) $ assocs merged
          return (InvalidTyping $ ReasonAmbig name pos ambigs, body)


-- |Like a monadic foldl over a list, where each application produces 
--  a list of values, and for each element of the folded list, the 
--  function is applied to every result from the previous element, 
--  finally producing the list of all the results.
typecheckSequence :: (Typing -> t -> Compiler [Typing]) -> [Typing] -> [t] -> 
                    Compiler [Typing]
typecheckSequence f typings [] = return typings
typecheckSequence f typings (t:ts) = do
    -- liftIO $ putStrLn $ "Type checking " ++ show (1 + length ts) ++ " things with " ++ show (length typings) ++ " typings, " ++ show (length $ List.filter validTyping typings) ++ " of them valid"
    typings' <- mapM (flip f t) typings
    let typings'' = pruneTypings $ concat typings'
    if List.null typings'
      then return []
      else if List.null typings'' || not (validTyping $ List.head typings'')
              -- No point going further if it's already invalid
           then return [List.head $ concat typings']
           else typecheckSequence f typings'' ts


pruneTypings :: [Typing] -> [Typing]
pruneTypings [] = []
pruneTypings typings =
    let pruned = nub $ List.filter validTyping typings
    in  if List.null pruned
        then typings
        else pruned


typecheckBody :: ModSpec -> [ModSpec] -> ProcName -> Typing -> ProcBody -> 
                 Compiler [Typing]
typecheckBody m mods name typing body@(ProcBody prims fork) = do
    -- liftIO $ putStrLn $ "Entering typecheckSequence from typecheckBody"
    typings' <- typecheckSequence (typecheckPlacedPrim m mods name)
                [typing] prims
    -- liftIO $ putStrLn $ "Body types: " ++ show typings'
    if List.null typings' || not (validTyping $ List.head typings')
    then return typings'
    else typecheckFork m mods name typings' fork


typecheckFork :: ModSpec -> [ModSpec] -> ProcName -> [Typing] -> PrimFork ->
                  Compiler [Typing]
typecheckFork m mods name typings NoFork = do
    return typings
typecheckFork m mods name typings (PrimFork _ _ bodies) = do
    -- liftIO $ putStrLn $ "Entering typecheckSequence from typecheckFork"
    typecheckSequence (typecheckBody m mods name) typings bodies


-- |Type check a single placed primitive operation given a list of 
--  possible starting typings and corresponding clauses up to this prim.
typecheckPlacedPrim :: ModSpec -> [ModSpec] -> ProcName -> Typing ->
                       Placed Prim -> Compiler [Typing]
typecheckPlacedPrim m mods caller typing pprim = do
    typecheckPrim m mods caller (content pprim) (place pprim) typing
    

-- |Type check a single primitive operation, producing a list of 
--  possible typings.
typecheckPrim :: ModSpec -> [ModSpec] -> ProcName -> Prim -> OptPos -> Typing ->
                 Compiler [Typing]
typecheckPrim m mods caller call@(PrimCall cm name id args0) pos typing = do
    -- liftIO $ putStrLn $ "Type checking call " ++ show call ++ 
    --   showMaybeSourcePos pos
    -- liftIO $ putStrLn $ "   with types " ++ show typing
    procs <- case id of
        Nothing   -> callTargets cm name
        Just spec -> return [spec]
    -- liftIO $ putStrLn $ "   potential procs: " ++
    --        List.intercalate ", " (List.map show procs)
    let args = args0
    if List.null procs 
      then if 1 == length args
           then return [InvalidTyping $ ReasonUninit caller name pos]
           else return [InvalidTyping $ ReasonUndef caller name pos]
      else do
        typList <- mapM (\p -> do
                              params0 <- getParams p
                              let params = List.filter (not . resourceParam)
                                           params0
                              -- liftIO $ putStr $ 
                              --   "\n   checking flow of call to " ++
                              --   show p ++ " args " ++
                              --   show args ++ " against params " ++
                              --   show params ++ "..."
                              case reconcileArgFlows params args of
                                  Just args' -> do
                                      -- liftIO $ putStrLn $ 
                                      --   "MATCHES: args = " ++ show args'
                                      return $ 
                                         [List.foldr (typecheckArg pos params $
                                                      procSpecName p)
                                          typing $ zip3 [1..] params args']
                                  Nothing -> do
                                      -- liftIO $ putStrLn "fails"
                                      return [InvalidTyping $ 
                                              ReasonArity caller name pos
                                              (listArity argFlowType 
                                               argFlow args)
                                              (listArity primParamFlowType 
                                               primParamFlow params)])
                   procs
        let typList' = concat typList
        let typList'' = List.filter validTyping typList'
        let dups = snd $ List.foldr
                   (\elt (s,l) ->
                        if Set.member elt s 
                        then (s,if List.elem elt l then l else elt:l)
                        else (Set.insert elt s,l))
                   (Set.empty,[]) typList''
        -- liftIO $ putStrLn $ "Resulting types: " ++ show typList''
        if List.null dups
        then if List.null typList''
             then do
                -- liftIO $ putStrLn $ "Type error detected: " ++
                --     unlines (List.map show typList')
                return typList'
             else return typList''
        else return [InvalidTyping $ ReasonOverload
                                   (List.map fst $
                                    List.filter 
                                      (List.any (flip List.elem dups) . snd) $
                                    zip procs typList)
                                   pos]
typecheckPrim _ _ _ (PrimForeign lang name id args) pos typing = do
    return [typing]
typecheckPrim _ _ _ PrimNop pos typing = return [typing]


argFlowType (ArgVar _ _ _ ft _) = ft
argFlowType _ = Ordinary

argFlow (ArgVar _ _ flow _ _) = flow
argFlow _ = FlowIn


-- |Match up params to args based only on flow, returning Nothing if 
--  they don't match, and Just a possibly updated arglist if they 
--  do.  The purpose is to handle passing an in-out argument pair 
--  where only an output is expected.  This is permitted, and the 
--  input half is just ignored.  This means the following 
--  combinations of parameter/argument flow are OK:
--      FlowIn  / FlowIn
--      FlowOut / FlowOut
--      FlowOut / FlowIn (Half) FlowOut (Half)
--  We also filter out any arguments where the corresponding param is
--  marked as unneeded.

reconcileArgFlows :: [PrimParam] -> [PrimArg] -> Maybe [PrimArg]
reconcileArgFlows [] [] = Just []
reconcileArgFlows _ [] = Nothing
reconcileArgFlows [] _ = Nothing
reconcileArgFlows (PrimParam _ _ pflow _ needed:params) 
  (arg@(ArgVar _ _ aflow _ _):args)
  | pflow == aflow = 
      let tail = reconcileArgFlows params args
      in fmap (arg:) tail
      -- in  if needed then fmap (arg:) tail else tail
reconcileArgFlows (PrimParam _ _ FlowOut _ needed:params) 
  (ArgVar _ _ FlowIn HalfUpdate _:arg@(ArgVar _ _ FlowOut HalfUpdate _):args)
  = let tail = reconcileArgFlows params args
    in  fmap (arg:) tail
    -- in  if needed then fmap (arg:) tail else tail
reconcileArgFlows (PrimParam _ _ FlowOut _ _:_) _ = Nothing
reconcileArgFlows (PrimParam _ _ FlowIn _ _:params)
                      (ArgVar _ _ FlowOut _ _:args) = Nothing
reconcileArgFlows (PrimParam _ _ FlowIn _ needed:params) (arg:args)
  = let tail = reconcileArgFlows params args    -- constant arg
    in fmap (arg:) tail
    -- in  if needed then fmap (arg:) tail else tail


typecheckArg :: OptPos -> [PrimParam] -> ProcName ->
                (Int,PrimParam,PrimArg) -> Typing -> Typing
typecheckArg pos params pname (argNum,param,arg) typing =
    let actualFlow = argFlowDirection arg
        formalFlow = primParamFlow param
        argNum' = listArity primParamFlowType primParamFlow $
                  take argNum params
        reasonType = ReasonArgType pname argNum' pos
        reasonFlow = ReasonArgFlow pname argNum' pos
    in  if not $ validTyping typing
        then typing
        else if formalFlow /= actualFlow
             then -- trace ("wrong flow: " ++ show arg ++ " against " ++ show param) 
                      InvalidTyping reasonFlow
             else -- trace ("OK flow: " ++ show arg ++ " against " ++ show param)
                  typecheckArg' arg (primParamType param) typing reasonType


typecheckArg' :: PrimArg -> TypeSpec -> Typing -> TypeReason -> Typing
typecheckArg' (ArgVar var decType flow ftype _) paramType typing reason =
-- XXX should out flow typing be contravariant?
    if --trace (if paramType `subtypeOf` decType || paramType == Unspecified
       --       then "" 
       --       else
       --           "CHECK VAR " ++ show var ++ ":" ++ show decType ++ " vs. " ++
       --           show paramType ++ " FAILED") $
       paramType `subtypeOf` decType then
        addOneType reason var paramType typing
    else if paramType == Unspecified -- may be type checking recursion
         then typing
         else InvalidTyping reason
-- XXX type specs below should include "wybe" module
typecheckArg' (ArgInt val callType) paramType typing reason =
    typecheckArg'' callType paramType (TypeSpec [] "int" [])
                   typing reason
typecheckArg' (ArgFloat val callType) paramType typing reason =
    typecheckArg'' callType paramType (TypeSpec [] "float" [])
                   typing reason
typecheckArg' (ArgString val callType) paramType typing reason =
    typecheckArg'' callType paramType (TypeSpec [] "string" [])
                   typing reason
typecheckArg' (ArgChar val callType) paramType typing reason =
    typecheckArg'' callType paramType (TypeSpec [] "char" [])
                   typing reason
                        

typecheckArg'' :: TypeSpec -> TypeSpec -> TypeSpec -> Typing -> TypeReason ->
                  Typing
typecheckArg'' callType paramType constType typing reason =
    let realType =
            if constType `subtypeOf` callType then constType else callType
    in -- trace ("check call type " ++ show callType ++ " against param type " ++ show paramType ++ " for const type " ++ show constType) $
       if paramType `subtypeOf` realType
       then typing
       else -- trace ("type error with constant: " ++ show realType ++ " vs. " ++ show paramType)
            InvalidTyping reason


diffBody :: ProcBody -> ProcBody -> Maybe (ProcName,OptPos)
diffBody (ProcBody prims1 fork1) (ProcBody prims2 fork2) =
    firstJust [diffFork fork1 fork2, diffCall prims1 prims2]


diffFork :: PrimFork -> PrimFork -> Maybe (ProcName,OptPos)
diffFork NoFork _ = Nothing
diffFork _ NoFork = Nothing
diffFork (PrimFork _ _ bodies1) (PrimFork _ _ bodies2) =
    firstJust $ List.map (uncurry diffBody) $ zip bodies1 bodies2


diffCall :: [Placed Prim] -> [Placed Prim] -> Maybe (ProcName,OptPos)
diffCall [] _ = Nothing
diffCall _ [] = Nothing
diffCall (c1:c1s) (c2:c2s)
    | c1 == c2  = diffCall c1s c2s
    | otherwise = callDifference (place c1) (content c1) (content c2)

callDifference :: OptPos -> Prim -> Prim -> Maybe (ProcName,OptPos)
callDifference pos (PrimCall _ name _ _) _ = Just (name,pos)
callDifference _ _ _ = shouldnt "impossible ambiguity"


firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (j@(Just _):_) = j
firstJust (Nothing:rest) = firstJust rest


listArity :: (t -> ArgFlowType) -> (t -> PrimFlow) -> [t] -> Int
listArity toFType toDirection lst =
    sum $ [if toFType e == HalfUpdate && toDirection e == FlowOut then 0 else 1 
          | e <- lst]


applyBodyTyping :: Map VarName TypeSpec -> ProcBody -> Compiler ProcBody
applyBodyTyping dict (ProcBody prims fork) = do
    prims' <- mapM (applyPlacedPrimTyping dict) prims
    fork' <- case fork of
        NoFork -> return NoFork
        (PrimFork v last bodies) -> do
            bodies' <- mapM (applyBodyTyping dict) bodies
            return $ PrimFork v last bodies'
    return $ ProcBody prims' fork'


applyPlacedPrimTyping :: Map VarName TypeSpec -> Placed Prim -> 
                         Compiler (Placed Prim)
applyPlacedPrimTyping dict pprim = do
    prim <- applyPrimTyping dict $ content pprim
    return $ maybePlace prim $ place pprim


applyPrimTyping :: Map VarName TypeSpec -> Prim -> Compiler Prim
applyPrimTyping dict call@(PrimCall cm name id args) = do
    -- liftIO $ putStrLn $ "typing call " ++ show call
    let args' = List.map (applyArgTyping dict) $
                List.filter (not . resourceArg) args
    procs <- case id of
        Nothing   -> callTargets cm name
        Just spec -> return [spec]
    -- liftIO $ putStrLn $ "   " ++ show (length procs) ++ " potential procs: "
    --        ++ intercalate ", " (List.map show procs)
    matches <- fmap catMaybes $
               mapM (\p -> do
                          params <- fmap (List.filter (not . resourceParam)) $
                                    getParams p
                          -- liftIO $ putStrLn $ "   checking call to " ++
                          --        show p ++ " args " ++
                          --        show args' ++ " against params " ++
                          --        show params
                          return $
                            fmap (\as -> (as,p)) $
                            checkMaybe (\as -> all (uncurry subtypeOf)
                                               (zip (List.map argType as)
                                                (List.map 
                                                 primParamType params))) $
                            reconcileArgFlows params args')
               procs
    checkError "not exactly one matching proc" (1 /= length matches)
    let (args'',proc) = List.head matches
    -- liftIO $ putStrLn $ "typed call = " ++ show (PrimCall (procSpecMod proc) (procSpecName proc) (Just proc) args'')
    return $ PrimCall (procSpecMod proc) (procSpecName proc) (Just proc) args''
applyPrimTyping dict call@(PrimForeign lang name id args) = do
    -- liftIO $ putStrLn $ "typing call " ++ show call
    let args' = List.map (applyArgTyping dict) args
    -- liftIO $ putStrLn $ "typed call = " ++ show (PrimForeign lang name id args')
    return $ PrimForeign lang name id args'
applyPrimTyping dict (PrimNop) = return PrimNop





applyArgTyping :: Map VarName TypeSpec -> PrimArg -> PrimArg
applyArgTyping dict (ArgVar var@(PrimVarName nm _) typ flow ftype final) =
    ArgVar var (fromMaybe typ $ Map.lookup nm dict) flow ftype final
-- XXX the module for these types should be ["wybe"]
applyArgTyping dict (ArgInt val _) = ArgInt val (TypeSpec [] "int" [])
applyArgTyping dict (ArgFloat val _) = ArgFloat val (TypeSpec [] "float" [])
applyArgTyping dict (ArgChar val _) = ArgChar val (TypeSpec [] "char" [])
applyArgTyping dict (ArgString val _) = ArgString val (TypeSpec [] "string" [])


----------------------------------------------------------------
--                    Check that everything is typed
----------------------------------------------------------------

-- |Sanity check: make sure all args and params of all procs in the 
-- current module are fully typed.  If not, report an internal error. 
checkFullyTyped :: Compiler ()
checkFullyTyped = do
    procs <- getModuleImplementationField (concat . Map.elems . modProcs)
    mapM_ checkProcDefFullytyped procs


-- |Make sure all args and params in the specified proc def are typed.
checkProcDefFullytyped :: ProcDef -> Compiler ()
checkProcDefFullytyped def = do
    let name = procName def
    let pos = procPos def
    mapM_ (checkParamTyped name pos) $
      zip [1..] $ primProtoParams $ procProto def
    checkBodyTyped name pos $ procBody def
    

checkParamTyped :: ProcName -> OptPos -> (Int,PrimParam) -> Compiler ()
checkParamTyped name pos (num,param) = do
    when (Unspecified == primParamType param) $
      reportUntyped name pos (" parameter " ++ show num)
      
checkBodyTyped :: ProcName -> OptPos -> ProcBody -> Compiler ()
checkBodyTyped name pos (ProcBody prims fork) = do
    mapM_ (placedApplyM $ checkPrimTyped name pos) $ prims
    case fork of
        NoFork -> return ()
        PrimFork _ _ bodies -> mapM_ (checkBodyTyped name pos) bodies


checkPrimTyped :: ProcName -> OptPos -> Prim -> OptPos -> Compiler ()
checkPrimTyped name pos (PrimCall _ pname _ args) ppos = do
    mapM_ (checkArgTyped name pos pname ppos) args
checkPrimTyped name pos (PrimForeign _ pname _ args) ppos = do
    mapM_ (checkArgTyped name pos pname ppos) args
checkPrimTyped name pos PrimNop ppos = return ()


checkArgTyped :: ProcName -> OptPos -> ProcName -> OptPos -> PrimArg ->
                 Compiler ()
checkArgTyped callerName callerPos calleeName callPos arg = do
    when (Unspecified == argType arg) $
      reportUntyped callerName callerPos $
      "call to " ++ calleeName ++ ", " ++ argDescription arg


reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg = do
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++ 
      showMaybeSourcePos pos ++ ", " ++ msg ++ " left untyped"
