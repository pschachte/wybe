--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (validateModExportTypes, typeCheckMod, checkFullyTyped) where

import           AST
import           Control.Monad.State
import           Data.Graph
import           Data.List           as List
import           Data.Map            as Map
import           Data.Maybe          as Maybe
import           Data.Set            as Set
import           Data.Tuple.Select
import           Options             (LogSelection (Types))
-- import           Resources
import           Util
import           Snippets

-- import           Debug.Trace


----------------------------------------------------------------
--           Validating Proc Parameter Type Declarations
----------------------------------------------------------------


-- |Check declared types of exported procs for the specified module.
-- This doesn't check that the types are correct vis-a-vis the
-- definition, just that the declared types are valid types, and it
-- updates the types to their fully-module-qualified versions.
validateModExportTypes :: ModSpec -> Compiler ()
validateModExportTypes thisMod = do
    logTypes $ "**** Validating parameter types in module " ++
           showModSpec thisMod
    reenterModule thisMod
    iface <- getModuleInterface
    procs <- getModuleImplementationField (Map.toAscList . modProcs)
    procs' <- mapM (uncurry validateProcDefsTypes) procs
    updateModImplementation (\imp -> imp { modProcs = Map.fromAscList procs'})
    loggedFinishModule thisMod


loggedFinishModule :: ModSpec -> Compiler ()
loggedFinishModule thisMod = do
    _ <- finishModule
    logTypes $ "**** Exiting module " ++ showModSpec thisMod
    return ()


validateProcDefsTypes :: Ident -> [ProcDef] -> Compiler (Ident,[ProcDef])
validateProcDefsTypes name defs = do
    defs' <- mapM (validateProcDefTypes name) defs
    return (name, defs')


validateProcDefTypes :: Ident -> ProcDef -> Compiler ProcDef
validateProcDefTypes name def = do
    let public = procVis def == Public
    let pos = procPos def
    let proto = procProto def
    let params = procProtoParams proto
    logTypes $ "Validating def of " ++ name
    params' <- mapM (validateParamType name pos public) params
    return $ def { procProto = proto { procProtoParams = params' }}


validateParamType :: Ident -> OptPos -> Bool -> Param -> Compiler Param
validateParamType pname ppos public param = do
    let ty = paramType param
    checkDeclIfPublic pname ppos public ty
    ty' <- fromMaybe AnyType <$> lookupType ty ppos
    let param' = param { paramType = ty' }
    return param'


checkDeclIfPublic :: Ident -> OptPos -> Bool -> TypeSpec -> Compiler ()
checkDeclIfPublic pname ppos public ty =
    when (public && ty == AnyType) $
         message Error ("Public proc '" ++ pname ++
                        "' with undeclared parameter or return type") ppos


-- |Type check a single module named in the second argument; the
--  first argument is a list of all the modules in this module
-- dependency SCC.
typeCheckMod :: ModSpec -> Compiler ()
typeCheckMod thisMod = do
    logTypes $ "**** Type checking module " ++ showModSpec thisMod
    reenterModule thisMod
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(name, name,
              nub $ concatMap (localBodyProcs thisMod . procImpln) procDefs)
             | (name,procDefs) <- procs]
    logTypes $ "**** Strongly connected components:\n" ++
      intercalate "\n"
       (List.map (\scc -> "    " ++ intercalate ", "
                         (case scc of
                             AcyclicSCC name -> [name]
                             CyclicSCC list -> list)) ordered)
    errs <- mapM (typecheckProcSCC thisMod) ordered
    mapM_ (\e -> message Error (show e) Nothing) $ concat $ reverse errs
    loggedFinishModule thisMod


----------------------------------------------------------------
--                       Supporting Type Errors
----------------------------------------------------------------

-- |Either something or some type errors
data MaybeErr t = OK t | Err [TypeError]
    deriving (Eq,Show)


-- |Return a list of the errors in the supplied MaybeErr
errList :: MaybeErr t -> [TypeError]
errList (OK _) = []
errList (Err lst) = lst


-- |Return a list of the payloads of all the OK elements of the input list
catOKs :: [MaybeErr t] -> [t]
catOKs lst = let toMaybe (OK a) =  Just a
                 toMaybe (Err _) = Nothing
             in  Maybe.mapMaybe toMaybe lst


-- |The reason a variable is given a certain type
data TypeError = ReasonParam ProcName Int OptPos
                   -- ^Formal param type/flow inconsistent
               | ReasonResource ProcName Ident OptPos
                   -- ^Declared resource inconsistent
               | ReasonUndef ProcName ProcName OptPos
                   -- ^Call to unknown proc
               | ReasonUninit ProcName VarName OptPos
                   -- ^Use of uninitialised variable
               | ReasonArgType ProcName Int OptPos
                   -- ^Actual param type inconsistent
               | ReasonCond OptPos
                   -- ^Conditional expression not bool
               | ReasonArgFlow ProcName Int OptPos
                   -- ^Input param with undefined argument variable
               | ReasonUndefinedFlow ProcName OptPos
                   -- ^Call argument flow does not match any definition
               | ReasonOverload [ProcSpec] OptPos
                   -- ^Multiple procs with same types/flows
               | ReasonAmbig ProcName OptPos [(VarName,[TypeRef])]
                   -- ^Proc defn has ambiguous types
               |  ReasonArity ProcName ProcName OptPos Int Int
                   -- ^Call to proc with wrong arity
               | ReasonUndeclared ProcName OptPos
                   -- ^Public proc with some undeclared types
               | ReasonEqual Exp Exp OptPos
                   -- ^Expression types should be equal
               | ReasonShouldnt
                   -- ^This error should never happen
               deriving (Eq, Ord)


instance Show TypeError where
    show (ReasonParam name num pos) =
        makeMessage pos $
            "Type/flow error in definition of " ++ name ++
            ", parameter " ++ show num
    show (ReasonResource name resName pos) =
            "Type/flow error in definition of " ++ name ++
            ", resource " ++ resName
    show (ReasonArgType name num pos) =
        makeMessage pos $
            "Type error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonCond pos) =
        makeMessage pos
            "Conditional or test expression with non-boolean result"
    show (ReasonArgFlow name num pos) =
        makeMessage pos $
            "Uninitialised argument in call to " ++ name
            ++ ", argument " ++ show num
    show (ReasonUndefinedFlow name pos) =
        makeMessage pos $
            "No matching mode in call to " ++ name
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
    show (ReasonEqual exp1 exp2 pos) =
        makeMessage pos $
        "Expressions must have compatible types:\n    "
        ++ show exp1 ++ "\n    "
        ++ show exp2
    show ReasonShouldnt =
        makeMessage Nothing "Mysterious typing error"


-- |Construct the appropriate TypeError for a call to an undefined proc/func.
undefStmtErr :: Ident -> Placed Stmt -> TypeError
undefStmtErr caller pstmt =
    let pos = place pstmt
    in case content pstmt of
        ProcCall _ callee _ _ _ -> ReasonUndef caller callee pos
        other -> shouldnt $ "undefStmtErr with non-call stmt " ++ show other
    

----------------------------------------------------------------
--                           Type Assignments
----------------------------------------------------------------

-- | A variable type assignment (symbol table), with a list of type errors.
-- 
data Typing = Typing {
                  typingDict::Map VarName TypeRef,
                  typingErrs::[TypeError]
                  }
            deriving (Show,Eq,Ord)

-- |The empty typing, assigning every var the type AnyType.
initTyping :: Typing
initTyping = Typing Map.empty []


-- |Does this typing have no type errors?
validTyping :: Typing -> Bool
validTyping (Typing _ errs) = List.null errs


-- |Follow a chain of TypeRefs to find the final IndirectType reference.
--  This code also sort-circuits all the keys along the path to the
--  ultimate reference, where possible, so future lookups will be faster.
ultimateRef :: VarName -> Typing -> (VarName,Typing)
ultimateRef var typing
    = let (var',dict') = ultimateRef' var $ typingDict typing
      in  (var', typing {typingDict = dict' })

ultimateRef' :: VarName -> Map VarName TypeRef
             -> (VarName,Map VarName TypeRef)
ultimateRef' var dict
    = case Map.lookup var dict of
          Just (IndirectType v) ->
            let (var',dict') = ultimateRef' v dict
            in (var', Map.insert var (IndirectType var') dict')
          _ -> (var,dict)


-- |Get the type associated with a variable; AnyType if no constraint has
--  been imposed on that variable.
varType :: VarName -> Typing -> TypeSpec
varType var Typing{typingDict=dict} = varType' var dict


-- |Get the type associated with a variable; AnyType if no constraint has
--  been imposed on that variable.
varType' :: VarName -> Map VarName TypeRef -> TypeSpec
varType' var dict
    = case Map.findWithDefault (DirectType AnyType) var dict of
          DirectType t -> t
          IndirectType v -> varType' v dict


-- |Constrain the type of the specified variable to be a subtype of the
--  specified type.  If this produces an invalid type, the specified type
--  error describes the error.
constrainVarType :: TypeError -> VarName -> TypeSpec -> Typing -> Typing
constrainVarType reason var ty typing
    = let (var',typing') = ultimateRef var typing
      in  case meetTypes ty $ varType var' typing' of
          InvalidType -> typeError reason typing'
          newType -> typing {typingDict =
                                  Map.insert var' (DirectType newType)
                                  $ typingDict typing' }


-- |Constrain the types of the two specified variables to be identical,
--  even following further constraints on the types of either of the vars.
unifyVarTypes :: VarName -> VarName -> OptPos -> Typing -> Typing
unifyVarTypes var1 var2 pos typing
    = let (v1,typing1) = ultimateRef var1 typing
          (v2,typing2) = ultimateRef var2 typing1
          vLow =  min v1 v2
          vHigh = max v1 v2
      in case meetTypes (varType vLow typing2) (varType vHigh typing2) of
          InvalidType -> typeError
                         (ReasonEqual (varGet var1) (varGet var2) pos)
                         typing2
          newType -> typing2 {typingDict =
                              Map.insert vLow (DirectType newType)
                              $ Map.insert vHigh (IndirectType vLow)
                              $ typingDict typing2 }


typeError :: TypeError -> Typing -> Typing
typeError err = typeErrors [err]


typeErrors :: [TypeError] -> Typing -> Typing
typeErrors newErrs (Typing dict errs) = Typing dict $ newErrs ++ errs


-- |Returns the first argument restricted to the variables appearing in the
--  second. This must handle cases where variable appearing in chains of
--  indirections (equivalence classes of variables) are projected away.
projectTyping :: Typing -> Typing -> Typing
projectTyping (Typing typing errs) (Typing interest _) =
    -- Typing (Map.filterWithKey (\k _ -> Map.member k interest) typing) errs
    Typing (projectTypingDict (Map.keys interest) typing Map.empty Map.empty)
    errs


-- |Return a map containing the types of the first input map projected onto
-- the supplied list of variables (which is in ascending alphabetical
-- order) and maintaining the equivalences of the original. The second map
-- argument holds the translation from the smallest equivalent variable
-- name in the input map to the same for the result.
--
-- This works by traversing the list of variable names, looking up each in
-- the input map.  I
projectTypingDict :: [VarName] -> Map VarName TypeRef -> Map VarName TypeRef
                  -> Map VarName VarName -> Map VarName TypeRef
projectTypingDict [] _ result _ = result
projectTypingDict (v:vs) dict result renaming
    = let (v',dict') = ultimateRef' v dict
          ty = varType' v' dict
      in  case Map.lookup v' renaming of
              Nothing -> projectTypingDict vs dict
                         (Map.insert v (DirectType ty) result)
                         (Map.insert v' v renaming)
              Just v'' -> projectTypingDict vs dict
                         (Map.insert v (IndirectType v'') result) renaming


----------------------------------------------------------------
--                           The Type Lattice
----------------------------------------------------------------

-- Simple strict subtype relation for now; every type is a subtype of the
-- unspecified type, and the invalid type is a subtype of every other type.
-- XXX Extend to support actual subtypes
properSubtypeOf :: TypeSpec -> TypeSpec -> Bool
properSubtypeOf _ AnyType = True
properSubtypeOf InvalidType _ = True
properSubtypeOf (TypeSpec mod1 name1 params1) (TypeSpec mod2 name2 params2) =
    name1 == name2
    && (mod1 == mod2 || List.null mod2)
    && length params1 == length params2
    && List.all (uncurry subtypeOf) (zip params1 params2)
properSubtypeOf _ _ = False


-- |Non-strict subtype relation
subtypeOf :: TypeSpec -> TypeSpec -> Bool
subtypeOf sub super = sub `properSubtypeOf` super || sub == super


-- |Return the greatest lower bound of two TypeSpecs.  
meetTypes :: TypeSpec -> TypeSpec -> TypeSpec
meetTypes ty1 ty2
    | ty1 `subtypeOf` ty2       = ty1
    | ty2 `properSubtypeOf` ty1 = ty2
    | otherwise                 = InvalidType


localBodyProcs :: ModSpec -> ProcImpln -> [Ident]
localBodyProcs thisMod (ProcDefSrc body) =
    foldProcCalls (localCalls thisMod) (++) [] body
localBodyProcs thisMod (ProcDefPrim _ _ _) =
    shouldnt "Type checking compiled code"

localCalls :: ModSpec -> ModSpec -> Ident -> Maybe Int -> Determinism
           -> [Placed Exp] -> [Ident]
localCalls thisMod m name _ _ _
  | List.null m || m == thisMod = [name]
localCalls _ _ _ _ _ _ = []


expType :: Typing -> Placed Exp -> Compiler TypeSpec
expType typing = placedApply (expType' typing)


expType' :: Typing -> Exp -> OptPos -> Compiler TypeSpec
expType' _ (IntValue _) _ = return $ TypeSpec ["wybe"] "int" []
expType' _ (FloatValue _) _ = return $ TypeSpec ["wybe"] "float" []
expType' _ (StringValue _) _ = return $ TypeSpec ["wybe"] "string" []
expType' _ (CharValue _) _ = return $ TypeSpec ["wybe"] "char" []
expType' typing (Var name _ _) _ = return $ varType name typing
expType' _ (Typed _ typ _) pos = fromMaybe AnyType <$> lookupType typ pos
expType' _ expr _ =
    shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- |Works out the declared flow direction of an actual parameter, paired
-- with whether or not the actual value is in fact available (is a constant
-- or a previously assigned variable), and with whether the call this arg
-- appears in should be delayed until this argument variable is assigned.
expMode :: Set VarName -> Placed Exp -> (FlowDirection,Bool,Maybe VarName)
expMode assigned pexp = expMode' assigned $ content pexp

expMode' :: Set VarName -> Exp -> (FlowDirection,Bool,Maybe VarName)
expMode' _ (IntValue _) = (ParamIn, True, Nothing)
expMode' _ (FloatValue _) = (ParamIn, True, Nothing)
expMode' _ (StringValue _) = (ParamIn, True, Nothing)
expMode' _ (CharValue _) = (ParamIn, True, Nothing)
expMode' assigned (Var name FlowUnknown _)
    = if name `elem` assigned
      then (ParamIn, True, Nothing)
      else (FlowUnknown, False, Just name)
expMode' assigned (Var name flow _) = (flow, name `elem` assigned, Nothing)
expMode' assigned (Typed expr _ _) = expMode' assigned expr
expMode' _ expr =
    shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- matchTypes :: Placed Exp -> Placed Exp -> OptPos -> Typing -> Compiler Typing
-- matchTypes parg1 parg2 pos typing = do
--     let arg1 = content parg1
--     let arg2 = content parg2
--     maybety1 <- expType typing parg1
--     maybety2 <- expType typing parg2
--     logTypes $ "Matching types " ++ show maybety1 ++ " and " ++ show maybety2
--     case (maybety1,maybety2) of
--       (Nothing,Nothing)  -> return typing
--       (Nothing,Just typ) -> return $ enforceType arg1 typ arg1 arg2 pos typing
--       (Just typ,Nothing) -> return $ enforceType arg2 typ arg1 arg2 pos typing
--       (Just typ1,Just typ2)  ->
--         return $ enforceType arg1 typ2 arg1 arg2 pos
--         $ enforceType arg2 typ1 arg1 arg2 pos typing
-- 
-- 
-- -- |Require the Exp to have the specified type
-- enforceType :: Exp -> TypeSpec -> Exp -> Exp -> OptPos -> Typing -> Typing
-- enforceType (Var name _ _) typespec arg1 arg2 pos typing =
--     constrainVarType (ReasonEqual arg1 arg2 pos) name typespec typing
-- enforceType (Typed (Var name _ _) typespec1 _) typespec arg1 arg2 pos typing =
--     let reason = ReasonEqual arg1 arg2 pos
--     in case meetTypes typespec1 typespec of
--       InvalidType -> typeError reason typing
--       ty          -> constrainVarType reason name ty typing
-- enforceType _ _ _ _ _ typing = typing -- no variable to record the type of


-- |Update the typing to assign the specified type to the specified expr
setExpType :: Placed Exp -> TypeSpec -> Int -> ProcName -> Typing -> Typing
setExpType pexp typ argnum procName typing
    = setExpType' (content pexp) (place pexp) typ argnum procName typing

setExpType' :: Exp -> OptPos -> TypeSpec -> Int -> ProcName -> Typing -> Typing
setExpType' (IntValue _) _ _ _ _ typing = typing
setExpType' (FloatValue _) _ _ _ _ typing = typing
setExpType' (StringValue _) _ _ _ _ typing = typing
setExpType' (CharValue _) _ _ _ _ typing = typing
setExpType' (Var var _ _) pos typ argnum procName typing
    = constrainVarType (ReasonArgType procName argnum pos) var typ typing
setExpType' (Typed expr _ _) pos typ argnum procName typing
    = setExpType' expr pos typ argnum procName typing
setExpType' otherExp _ _ _ _ _
    = shouldnt $ "Invalid expr left after flattening " ++ show otherExp

----------------------------------------------------------------
--                         Type Checking Procs
----------------------------------------------------------------

-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred
--  types are more specific than the old ones and some proc(s) in the
--  SCC depend on procs in the list of mods.  In this case, we will
--  have to rerun the typecheck after typechecking the other modules
--  on that list.
typecheckProcSCC :: ModSpec -> SCC ProcName -> Compiler [TypeError]
typecheckProcSCC m (AcyclicSCC name) = do
    -- A single pass is always enough for non-cyclic SCCs
    logTypes $ "Type checking non-recursive proc " ++ name
    (_,reasons) <- typecheckProcDecls m name
    return reasons
typecheckProcSCC m (CyclicSCC list) = do
    logTypes $ "**** Type checking recursive procs " ++
      intercalate ", " list
    (sccAgain,reasons) <-
        foldM (\(sccAgain,rs) name -> do
                    (sccAgain',reasons) <- typecheckProcDecls m name
                    return (sccAgain || sccAgain', reasons++rs))
        (False, []) list
    if sccAgain
    then typecheckProcSCC m $ CyclicSCC list
    else do
      logTypes $ "**** Completed checking of " ++
             intercalate ", " list ++
             " with " ++ show (length reasons) ++ " errors"
      return reasons


-- |Type check a list of procedure definitions and update the
--  definitions stored in the Compiler monad.  Returns a pair of
--  Bools, the first saying whether any defnition has been udpated,
--  and the second saying whether any public defnition has been
--  updated.
typecheckProcDecls :: ModSpec -> ProcName ->
                     Compiler (Bool,[TypeError])
typecheckProcDecls m name = do
    logTypes $ "** Type checking " ++ name
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
    logTypes $ "** New definition of " ++ name ++ ":"
    logTypes $ intercalate "\n" $ List.map (showProcDef 4) (reverse revdefs)
    -- XXX this shouldn't be necessary anymore, but keep it for now for safety
    unless (sccAgain || not (List.null reasons)) $
        mapM_ checkProcDefFullytyped revdefs
    return (sccAgain,reasons)


----------------------------------------------------------------
--                       Resolving types and modes
--
-- This code resolves types and modes, including resolving overloaded
-- calls, handling implied modes, and appropriately ordering calls from
-- nested function application (which was not resolved during flattening).
-- We search for a valid resolution deterministically if possible.
--
-- To do this we first collect a list of all the calls in the proc body.
-- We process this maintaining 3 data structures:
--    * a typing:  a map from variable name to type;
--    * a resolution:  a mapping from original call to the selected proc spec;
--    * residue:  a list of unprocessed (delayed) calls with the list of
--      resolutions for each.
--
-- For each call, we collect the list of all possible resolutions, and
-- filter this down to the ones that match the argument types given the
-- current typing. If this is unique, we add it to the resolution mapping
-- and update the typing. If there are no matches, we check if there is a
-- unique resolution taking implied modes into account, and if so we select
-- it. If there are no resolutions at all, even allowing for implied modes,
-- then we can report a type error. If there are multiple matches, we add
-- this call to the residue and move on to the the call.
--
-- This process is repeated using the residue of the previous pass as the
-- input to the next one, repeating as long as the residue gets strictly
-- smaller.  Once it stops getting smaller, we select the remaining call
-- with the fewest resolutions and try selecting each resolution and then
-- processing the remainder of the residue with that "guess".  If only one
-- of the guesses leads to a valid typing, that is the correct typing;
-- otherwise we report a type error.


-- -- |A ProcSpec resolving a call together with it param types
-- data ProcAndParams = ProcAndParams { procSpec :: ProcSpec,
--                                      paramTypes :: [TypeSpec]}
--     deriving (Eq,Show)

-- -- |The resolutions of many proc calls
-- type StmtResolution = Map Stmt ProcSpec
-- 
-- emptyStmtResolution = Map.empty


-- |An individual proc, its formal parameter types and modes, and determinism
data ProcInfo = ProcInfo {
  procInfoProc :: ProcSpec,
  procInfoArgs :: [TypeFlow],
  procInfoDetism:: Determinism
  } deriving (Eq,Show)


procInfoTypes :: ProcInfo -> [TypeSpec]
procInfoTypes call = typeFlowType <$> procInfoArgs call


-- |Check if ProcInfo is for a proc with a single Bool output as last arg,
--  and if so, return Just the ProcInfo for the equivalent test proc
boolFnToTest :: ProcInfo -> Maybe ProcInfo
boolFnToTest (ProcInfo _ _ SemiDet) = Nothing
boolFnToTest (ProcInfo proc args Det)
    | List.null args = Nothing
    | last args == TypeFlow boolType ParamOut =
        Just $ ProcInfo proc (init args) SemiDet
    | otherwise = Nothing
    

-- |Check if ProcInfo is for a test proc, and if so, return a ProcInfo for
--  the Det proc with a single Bool output as last arg
testToBoolFn :: ProcInfo -> Maybe ProcInfo
testToBoolFn (ProcInfo _ _ Det) = Nothing
testToBoolFn (ProcInfo proc args SemiDet)
    = Just $ ProcInfo proc (args ++ [TypeFlow boolType ParamOut]) Det
    


-- |A single call statement together with the determinism context in which
--  the call appears and a list of all the possible different parameter
--  list types (a list of types). This type is used to narrow down the
--  possible call typings.
data StmtTypings = StmtTypings {typingStmt::Placed Stmt,
                                typingDetism::Determinism,
                                typingArgsTypes::[ProcInfo]}
    deriving (Eq,Show)


-- |Type check a single procedure definition, including resolving overloaded
-- calls, handling implied modes, and appropriately ordering calls from
-- nested function application.  We search for a valid resolution
-- deterministically if possible.
typecheckProcDecl :: ModSpec -> ProcDef -> Compiler (ProcDef,Bool,[TypeError])
typecheckProcDecl m pdef = do
    let name = procName pdef
    let proto = procProto pdef
    let params = procProtoParams proto
    let resources = procProtoResources proto
    let (ProcDefSrc def) = procImpln pdef
    let detism = procDetism pdef
    let pos = procPos pdef
    let vis = procVis pdef
    if vis == Public && any ((==AnyType) . paramType) params
      then return (pdef,False,[ReasonUndeclared name pos])
      else do
        paramTyping <- foldM (addDeclaredType name pos (length params))
                  initTyping $ zip params [1..]
        resourceTyping <- foldM (addResourceType name pos) paramTyping resources
        if validTyping resourceTyping
          then do
            logTypes $ "** Type checking proc " ++ name ++ ": "
                       ++ show resourceTyping
            logTypes $ "   with resources: " ++ show resources
            let (calls,preTyping) =
                  runState (bodyCalls def detism) resourceTyping
            logTypes $ "   containing calls: " ++ showBody 4 (fst <$> calls)
            let procCalls = List.filter (isProcCall . content . fst) calls
            let unifs = List.concatMap foreignTypeEquivs
                        ((content . fst) <$> calls)
            unifTyping <- foldM (\t (e1,e2) -> unifyExprTypes pos e1 e2 t)
                          preTyping unifs
            calls' <- zipWith (\(call,detism) typs ->
                                   StmtTypings call detism typs) procCalls
                      <$> mapM (callProcInfos . fst) procCalls
            let badCalls = List.map typingStmt
                           $ List.filter (List.null . typingArgsTypes) calls'
            if List.null badCalls
              then do
                typing <- typecheckCalls m name pos calls' unifTyping [] False

                logTypes $ "Typing independent of mode = " ++ show typing
                -- (typing''',def') <- typecheckProcDef m name pos preTyping def
                -- logTypes $ "*resulting types " ++ name ++ ": " ++ show typing'''
                if validTyping typing
                  then do
                    logTypes "Now mode checking"
                    let inParams =
                          List.filter
                          ((`elem` [ParamIn,ParamInOut]) . paramFlow)
                          params
                    let inResources =
                          Set.map resourceFlowRes
                          $ Set.filter
                              ((`elem` [ParamIn,ParamInOut]) . resourceFlowFlow)
                              resources
                    let initialised
                            = (Set.fromList $ paramName <$> inParams)
                              `Set.union`
                              (Set.map resourceName inResources)
                    (def',_,modeErrs) <-
                      modecheckStmts m name pos typing [] initialised detism def
                    let typing' = typeErrors modeErrs typing
                    let params' = updateParamTypes typing' params
                    let proto' = proto { procProtoParams = params' }
                    let pdef' = pdef { procProto = proto',
                                       procImpln = ProcDefSrc def' }
                    let sccAgain = validTyping typing' && pdef' /= pdef
                    logTypes $ "===== "
                               ++ (if sccAgain then "" else "NO ")
                               ++ "Need to check again."
                    when sccAgain
                        (logTypes $ "\n-----------------OLD:"
                                    ++ showProcDef 4 pdef
                                    ++ "\n-----------------NEW:"
                                    ++ showProcDef 4 pdef' ++ "\n")
                    return (pdef',sccAgain,typingErrs typing')
                  else
                    return (pdef,False,typingErrs typing)
              else
                return (pdef,False,
                           List.map (\pcall ->
                                         case content pcall of
                                             ProcCall _ callee _ _ _ ->
                                                 ReasonUndef name callee
                                                 $ place pcall
                                             _ -> shouldnt "typecheckProcDecl")
                           badCalls)
          else
            return (pdef,False,typingErrs resourceTyping)


addDeclaredType :: ProcName -> OptPos -> Int -> Typing -> (Param,Int) ->
                   Compiler Typing
addDeclaredType procname pos arity typs (Param name typ flow _,argNum) = do
    typ' <- fromMaybe AnyType <$> lookupType typ pos
    logTypes $ "    type of '" ++ name ++ "' is " ++ show typ'
    return $ constrainVarType (ReasonParam procname arity pos) name typ' typs


addResourceType :: ProcName -> OptPos -> Typing -> ResourceFlowSpec ->
                   Compiler Typing
addResourceType procname pos typs rfspec = do
    let rspec = resourceFlowRes rfspec
    resIface <- lookupResource rspec pos
    let (rspecs,types) = unzip $ maybe [] (Map.toList . snd) resIface
    let names = List.map resourceName rspecs
    let typs' = List.foldr
                (\(n,t) typs ->
                     constrainVarType
                     (ReasonResource procname n pos) n t typs)
                typs $ zip names types
    return typs'


updateParamTypes :: Typing -> [Param] -> [Param]
updateParamTypes typing =
    List.map (\p@(Param name typ fl afl) ->
                  Param name (varType name typing) fl afl)


-- |Return a list of the proc and foreign calls recursively in a list of
--  statements, paired with all the possible resolutions.
bodyCalls :: [Placed Stmt] -> Determinism
          -> State Typing [(Placed Stmt, Determinism)]
bodyCalls [] _ = return []
bodyCalls (pstmt:pstmts) detism = do
    rest <- bodyCalls pstmts detism
    let stmt = content pstmt
    let pos  = place pstmt
    case stmt of
        ProcCall{} -> return $  (pstmt,detism):rest
        -- need to handle move instructions:
        ForeignCall{} -> return $ (pstmt,detism):rest
        TestBool _ -> return rest
        And stmts -> bodyCalls stmts detism
        Or stmts -> bodyCalls stmts detism
        Not stmt -> bodyCalls [stmt] detism
        Nop -> return rest
        Cond cond thn els -> do
          -- modify $ constrainVarType (ReasonCond pos)
          --          (expVar $ content expr) boolType
          cond' <- bodyCalls [cond] SemiDet
          thn' <- bodyCalls thn detism
          els' <- bodyCalls els detism
          return $ cond' ++ thn' ++ els' ++ rest
        Loop nested -> do
          nested' <- bodyCalls nested detism
          return $ nested' ++ rest
        For _ _ -> shouldnt "bodyCalls: flattening left For stmt"
        Break -> return rest
        Next ->  return rest


isProcCall :: Stmt -> Bool
isProcCall ProcCall{} = True
isProcCall _ = False


foreignTypeEquivs :: Stmt -> [(Placed Exp,Placed Exp)]
foreignTypeEquivs (ForeignCall "llvm" "move" _ [v1,v2]) = [(v1,v2)]
foreignTypeEquivs (ForeignCall "lpvm" "mutate" _ [v1,v2,_,_,_,_]) = [(v1,v2)]
foreignTypeEquivs _ = []


callProcInfos :: Placed Stmt -> Compiler [ProcInfo]
callProcInfos pstmt =
    case content pstmt of
        ProcCall m name procId _ _ -> do
          procs <- case procId of
              Nothing   -> callTargets m name
              Just pid -> return [ProcSpec m name pid]
          typflows <- mapM (fmap (List.map paramTypeFlow
                                  . List.filter nonResourceParam)
                            . getParams)
                      procs
          detisms <- mapM getDetism procs
          return $ zipWith3 ProcInfo procs typflows detisms

        stmt ->
          shouldnt $ "callProcInfos with non-call statement "
                     ++ showStmt 4 stmt


-- |Return the variable name of the supplied expr.  In this context,
--  the expr will always be a variable.
expVar :: Exp -> VarName
expVar expr = fromMaybe
              (shouldnt $ "expVar of non-variable expr " ++ show expr)
              $ expVar' expr


-- |Return the variable name of the supplied expr, if there is one.
expVar' :: Exp -> Maybe VarName
expVar' (Typed expr _ _) = expVar' expr
expVar' (Var name _ _) = Just name
expVar' _expr = Nothing


-- |Return the "primitive" expr of the specified expr.  This unwraps Typed
--  wrappers, giving the internal exp.
ultimateExp :: Exp -> Exp
ultimateExp (Typed expr _ _) = ultimateExp expr
ultimateExp expr = expr


-- |Type check a list of statement typings, resulting in a typing of all
--  variables.  Input is a list of statement typings plus a variable typing,
--  output is a final variable typing.  We thread through a residue
--  list of unresolved statement typings; when we reach the end of the
--  main list of statement typings, we reprocess the residue, providing
--  the last pass has resolved some statements.  Thus we make multiple
--  passes over the list of statement typings until it is empty.
--
--  If we complee a pass over the list without resolving any statements
--  and a residue remains, then we pick a statement with the fewest remaining
--  types and try all the types in turn.  If exactly one of these leads to
--  a valid typing, this is the correct one; otherwise it is a type error.
--
--  To handle a single call, we find the types of all arguments as determined
--  by the current typing, and match this list against each of the candidate
--  statement typings, filtering out invalid possibilities.  If a single
--  possibility remains, we commit to this.  If multiple possibilities remain,
--  we keep all of them as a residue and continue with other statements.  If
--  no possibilities remain, we determine that the statement typing is
--  inconsistent with the initial variable typing (a type error).
typecheckCalls :: ModSpec -> ProcName -> OptPos -> [StmtTypings]
    -> Typing -> [StmtTypings] -> Bool -> Compiler Typing
typecheckCalls m name pos [] typing [] _ = return typing
typecheckCalls m name pos [] typing residue True =
    typecheckCalls m name pos residue typing [] False
typecheckCalls m name pos [] typing residue False =
    -- XXX Propagation alone is not always enough to determine a unique type.
    -- Need code to try to find a mode by picking a residual call with the
    -- fewest possibilities and try all combinations to see if exactly one
    -- of them gives us a valid typing.  If not, it's a type error.
    return $ typeErrors (List.map overloadErr residue) typing
typecheckCalls m name pos (stmtTyping@(StmtTypings pstmt detism typs):calls)
        typing residue chg = do
    logTypes $ "Type checking call " ++ show pstmt
    logTypes $ "Calling context is " ++ show detism
    logTypes $ "Candidate types: " ++ show typs
    -- XXX Must handle reification of test as a bool
    let (callee,pexps) = case content pstmt of
                             ProcCall _ callee' _ _ pexps' -> (callee',pexps')
                             noncall -> shouldnt
                                        $ "typecheckCalls with non-call stmt"
                                          ++ show noncall
    actualTypes <- mapM (expType typing) pexps
    logTypes $ "Actual types: " ++ show actualTypes
    let matches = List.map
                  (matchTypeList name callee (place pstmt) actualTypes detism)
                  typs
    let validMatches = catOKs matches
    let validTypes = nub $ procInfoTypes <$> validMatches
    logTypes $ "Valid types = " ++ show validTypes
    logTypes $ "Converted types = " ++ show (boolFnToTest <$> typs)
    case validTypes of
        [] -> do
          logTypes "Type error: no valid types for call"
          return $ typeErrors (concatMap errList matches) typing
        [match] -> do
          let typing' = List.foldr
                        (\ (pexp,ty,argnum) -> setExpType pexp ty argnum name)
                        typing
                        $ zip3 pexps match [1..]
          logTypes $ "Resulting typing = " ++ show typing'
          typecheckCalls m name pos calls typing' residue True
        _ -> do
          let stmtTyping' = stmtTyping {typingArgsTypes = validMatches}
          typecheckCalls m name pos calls typing (stmtTyping':residue)
              $ chg || validMatches /= typs


-- |Match up the argument types of a call with the parameter types of the
-- callee, producing a list of the actual types.  If this list contains
-- InvalidType, then the call would be a type error.
matchTypeList :: Ident -> Ident -> OptPos -> [TypeSpec] -> Determinism
              -> ProcInfo -> MaybeErr ProcInfo
matchTypeList caller callee pos callArgTypes detismContext calleeInfo
    | sameLength callArgTypes args
    = matchTypeList' callee pos callArgTypes calleeInfo
    -- Handle case of SemiDet context call to bool function as a proc call
    | detismContext == SemiDet && isJust testInfo
      && sameLength callArgTypes (procInfoArgs calleeInfo')
    = matchTypeList' callee pos callArgTypes calleeInfo'
    -- Handle case of reified test call
    | isJust detCallInfo
      && sameLength callArgTypes (procInfoArgs calleeInfo'')
    = matchTypeList' callee pos callArgTypes calleeInfo''
    | otherwise = Err [ReasonArity caller callee pos
                       (length callArgTypes) (length args)]
    where args = procInfoArgs calleeInfo
          testInfo = boolFnToTest calleeInfo
          calleeInfo' = fromJust testInfo
          detCallInfo = testToBoolFn calleeInfo
          calleeInfo'' = fromJust detCallInfo

matchTypeList' :: Ident -> OptPos -> [TypeSpec] -> ProcInfo -> MaybeErr ProcInfo
matchTypeList' callee pos callArgTypes calleeInfo =
    if List.null mismatches
    then OK $ calleeInfo
         {procInfoArgs = List.zipWith TypeFlow matches calleeFlows}
    else Err [ReasonArgType callee n pos | n <- mismatches]
    where args = procInfoArgs calleeInfo
          calleeTypes = typeFlowType <$> args
          calleeFlows = typeFlowMode <$> args
          matches = List.zipWith meetTypes callArgTypes calleeTypes
          mismatches = List.map fst $ List.filter ((==InvalidType) . snd)
                       $ zip [1..] matches


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if all actual arguments are instantiated
-- if the corresponding parameter is an input.
matchModeList :: [(FlowDirection,Bool,Maybe VarName)]
              -> ProcInfo -> Bool
matchModeList modes ProcInfo{procInfoArgs=typModes}
    -- Check that no param is in where actual is out
    = (ParamIn,ParamOut) `notElem` argModes
    where argModes = zip (typeFlowMode <$> typModes) (sel1 <$> modes)


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if the call mode exactly matches the
-- proc mode, treating a FlowUnknown argument as ParamOut.
exactModeMatch :: [(FlowDirection,Bool,Maybe VarName)]
               -> ProcInfo -> Bool
exactModeMatch modes ProcInfo{procInfoArgs=typModes}
    = all (\(formal,actual) -> formal == actual
                               || formal == ParamOut && actual == FlowUnknown)
      $ zip (typeFlowMode <$> typModes) (sel1 <$> modes)


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if the call mode exactly matches the
-- proc mode, treating a FlowUnknown argument as ParamOut.
delayModeMatch :: [(FlowDirection,Bool,Maybe VarName)]
               -> ProcInfo -> Bool
delayModeMatch modes ProcInfo{procInfoArgs=typModes}
    = all (\(formal,actual) -> formal == actual
                               || actual == FlowUnknown
                               && (formal == ParamIn || formal == ParamOut))
      $ zip (typeFlowMode <$> typModes) (sel1 <$> modes)


overloadErr :: StmtTypings -> TypeError
overloadErr StmtTypings{typingStmt=call,typingArgsTypes=candidates} =
    -- XXX Need to give list of matching procs
    ReasonOverload (procInfoProc <$> candidates) $ place call


-- |Given type assignments to variables, resolve modes in a proc body,
--  building a revised, properly moded body, or indicate a mode error.
--  This must handle several cases:
--  * Flow direction for function calls are unspecified; they must be assigned,
--    and may need to be delayed if the use appears before the definition.
--  * Test statements must be handled, determining which stmts in a test
--    context are actually tests, and reporting an error for tests outside
--    a test context
--  * Implied modes:  in a test context, allow in mode where out mode is
--    expected by assigning a fresh temp variable and generating an =
--    test of the variable against the in value.
--  * Handle in-out call mode where an out-only argument is expected.
--  This code threads a set of assigned variables through, which starts as
--  the set of in parameter names.  It also threads through a list of
--  statements postponed because an unknown flow variable is not assigned yet.
modecheckStmts :: ModSpec -> ProcName -> OptPos -> Typing
                 -> [(Set VarName,Placed Stmt)] -> Set VarName -> Determinism
                 -> [Placed Stmt]
                 -> Compiler ([Placed Stmt], Set VarName,[TypeError])
modecheckStmts _ _ _ _ delayed assigned _ []
    | List.null delayed = return ([],assigned,[])
    | otherwise =
        shouldnt $ "modecheckStmts reached end of body with delayed stmts:\n"
                   ++ show delayed
modecheckStmts m name pos typing delayed assigned detism (pstmt:pstmts) = do
    (pstmt',delayed',assigned',errs') <-
      placedApply (modecheckStmt m name pos typing delayed assigned detism)
        pstmt
    let assigned'' = assigned `Set.union` assigned'
    logTypes $ "New errors   = " ++ show errs'
    logTypes $ "Now assigned = " ++ show assigned''
    logTypes $ "Now delayed  = " ++ show delayed'
    let (doNow,delayed'')
            = List.partition
            (not . Set.null . flip Set.intersection assigned' . fst)
            delayed'
    (pstmts',assigned''',errs) <-
      modecheckStmts m name pos typing delayed'' assigned'' detism
        ((snd <$> doNow) ++ pstmts)
    return (pstmt'++pstmts',assigned''',errs'++errs)


-- |Mode check a single statement, returning a list of moded statements,
--  plus a list of delayed statements, a set of variables bound by this
--  statement, and a list of type (mode) errors.
--
--  We select a mode as follows:
--    0.  If some input arguments are not assigned, report an uninitialised
--        variable error.
--    1.  If there is an exact match for the current instantiation state
--        (treating any FlowUnknown args as ParamIn), select it.
--    2.  If this is a test context and there is a match for the current
--        instantiation state (treating any FlowUnknown args as ParamIn
--        and allowing ParamIn arguments where the parameter is ParamOut),
--        select it, and transform by replacing each non-identical flow
--        ParamIn argument with a fresh ParamOut variable, and adding a
--        = test call to test the fresh variable against the actual ParamIn
--        argument.
--    3.  If there is a match (possibly with some ParamIn args where
--        ParamOut is expected) treating any FlowUnknown args as ParamOut,
--        then select that mode but delay the call.
--    4.  Otherwise report a mode error.
--
--    In case there are multiple modes that match one of those criteria,
--    select the first that matches.
modecheckStmt :: ModSpec -> ProcName -> OptPos -> Typing
                 -> [(Set VarName,Placed Stmt)] -> Set VarName -> Determinism
                 -> Stmt -> OptPos
                 -> Compiler ([Placed Stmt], [(Set VarName,Placed Stmt)],
                              Set VarName,[TypeError])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(ProcCall cmod cname _ _ args) pos = do
    logTypes $ "Mode checking call   : " ++ show stmt
    logTypes $ "    with assigned    : " ++ show assigned
    callInfos <- callProcInfos $ maybePlace stmt pos
    actualTypes <- mapM (expType typing) args
    let actualModes = List.map (expMode assigned) args
    let flowErrs = [ReasonArgFlow cname num pos
                   | ((mode,avail,_),num) <- zip actualModes [1..]
                   , mode == ParamIn && not avail]
    if not $ List.null flowErrs -- Using undefined var as input?
        then do
            logTypes $ "Unpreventable mode errors: " ++ show flowErrs
            return ([],delayed,assigned,flowErrs)
        else do
            let typeMatches
                    = catOKs
                      $ List.map
                        (matchTypeList name cname pos actualTypes detism)
                        callInfos
            -- All the possibly matching modes
            let modeMatches
                    = List.filter (matchModeList actualModes) typeMatches
            logTypes $ "Actual types         : " ++ show actualTypes
            logTypes $ "Actual call modes    : " ++ show actualModes
            logTypes $ "Type-correct modes   : " ++ show typeMatches
            logTypes $ "Possible mode matches: " ++ show modeMatches
            let exactMatches
                    = List.filter (exactModeMatch actualModes) modeMatches
            logTypes $ "Exact mode matches: " ++ show exactMatches
            let delayMatches
                    = List.any (delayModeMatch actualModes) modeMatches
            logTypes $ "Delay mode matches: " ++ show delayMatches
            case exactMatches of
                (match:_) -> do
                  -- XXX If it's semidet, we need to convert to Det by adding
                  -- a Boolean output parameter and a TestBool instruction
                  let matchProc = procInfoProc match
                  let args' = List.zipWith setPExpTypeFlow
                              (procInfoArgs match) args
                  let stmt' = ProcCall (procSpecMod matchProc)
                              (procSpecName matchProc)
                              (Just $ procSpecID matchProc)
                              (procInfoDetism match)
                              args'
                  let assigned' = Set.union
                                  (Set.fromList
                                  $ List.map (expVar . content)
                                  $ List.filter
                                  ((==ParamOut) . expFlow . content) args')
                                  assigned
                  return ([maybePlace stmt' pos],delayed,assigned',[])
                [] -> if delayMatches
                      then do
                        logTypes $ "delaying call: " ++ ": " ++ show stmt
                        let vars = Set.fromList $ catMaybes
                                   $ sel3 <$> actualModes
                        let delayed' = (vars,maybePlace stmt pos):delayed
                        logTypes $ "delayed = " ++ show delayed'
                        return ([],delayed',assigned,[])
                      else do
                        logTypes $ "Mode errors in call:  " ++ show flowErrs
                        return ([],delayed,assigned,
                                [ReasonUndefinedFlow cname pos])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(ForeignCall lang cname flags args) pos = do
    logTypes $ "Mode checking foreign call " ++ show stmt
    logTypes $ "    with assigned " ++ show assigned
    actualTypes <- mapM (expType typing) args
    let actualModes = List.map (expMode assigned) args
    let flowErrs = [ReasonArgFlow cname num pos
                   | ((mode,avail,_yy),num) <- zip actualModes [1..]
                   , not avail && mode == ParamIn]
    if not $ List.null flowErrs -- Using undefined var as input?
        then do
            logTypes "delaying foreign call"
            return ([],delayed,assigned,flowErrs)
        else do
            let typeflows = List.zipWith TypeFlow actualTypes
                            $ sel1 <$> actualModes
            let args' = List.zipWith setPExpTypeFlow typeflows args
            let stmt' = ForeignCall lang cname flags args'
            let assigned' = Set.fromList
                            $ List.map (expVar . content)
                            $ List.filter ((==ParamOut) . expFlow . content)
                              args'
            logTypes $ "New instr = " ++ show stmt'
            return ([maybePlace stmt' pos],delayed,assigned',[])
modecheckStmt _ _ _ _ delayed assigned _ Nop pos = do
    logTypes $ "Mode checking Nop"
    return ([maybePlace Nop pos], delayed, assigned,[])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Cond tstStmt thnStmts elsStmts) pos = do
    logTypes $ "Mode checking conditional " ++ show stmt
    (tstStmt', delayed', assigned1,errs1) <-
      placedApplyM (modecheckStmt m name defPos typing delayed assigned SemiDet)
      tstStmt
    (thnStmts', assigned2,errs2) <-
      modecheckStmts m name defPos typing [] assigned1 detism thnStmts
    (elsStmts', assigned3,errs3) <-
      modecheckStmts m name defPos typing [] assigned2 detism elsStmts
    return ([maybePlace (Cond (seqToStmt tstStmt') thnStmts' elsStmts') pos],
            delayed'++delayed,
            assigned1 `Set.union` (assigned2 `Set.intersection` assigned3),
            errs1++errs2++errs3)
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(TestBool exp) pos = do
    logTypes $ "Mode checking test " ++ show stmt
    let exp' = content $ setPExpTypeFlow (TypeFlow boolType ParamIn)
                                         (maybePlace exp pos)
    return ([maybePlace (TestBool exp') pos], delayed, assigned,[])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Loop stmts) pos = do
    logTypes $ "Mode checking loop " ++ show stmt
    (stmts', assigned',errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    -- XXX Can only assume vars assigned before first loop exit are
    --     actually assigned by loop
    return ([maybePlace (Loop stmts') pos], delayed, assigned',errs')
-- XXX Need to implement these:
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(And stmts) pos = do
    logTypes $ "Mode checking conjunction " ++ show stmt
    (stmts', assigned',errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    return ([maybePlace (And stmts') pos], delayed, assigned',errs')
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Or stmts) pos = do
    logTypes $ "Mode checking disjunction " ++ show stmt
    (stmts', assigned',errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    return ([maybePlace (Or stmts') pos], delayed, assigned',errs')
modecheckStmt m name defPos typing delayed assigned detism
    (Not stmt) pos = do
    logTypes $ "Mode checking negation " ++ show stmt
    (stmt', delayed', assigned',errs') <-
      placedApplyM (modecheckStmt m name defPos typing [] assigned detism) stmt 
    return ([maybePlace (Not (seqToStmt stmt')) pos],
            delayed'++delayed, assigned',errs')
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(For gen stmts) pos = nyi "mode checking For"
modecheckStmt m name defPos typing delayed assigned detism
    Break pos = return ([maybePlace Break pos],delayed,Set.empty,[])
modecheckStmt m name defPos typing delayed assigned detism
    Next pos = return ([maybePlace Next pos],delayed,Set.empty,[])


selectMode :: [ProcInfo] -> [(FlowDirection,Bool,Maybe VarName)]
           -> ProcInfo
selectMode (procInfo:_) _ = procInfo
selectMode _ _ = shouldnt "selectMode with empty list of modes"



-- -- |Type check the body of a single proc definition by type checking
-- --  each clause in turn using the declared parameter typing plus the
-- --  typing of all parameters inferred from previous clauses.  We can
-- --  stop once we've found a contradiction.
-- typecheckProcDef :: ModSpec -> ProcName -> OptPos -> Typing ->
--                      [Placed Stmt] -> Compiler (Typing,[Placed Stmt])
-- typecheckProcDef m name pos paramTypes body = do
--     logTypes $ "\ntype checking: " ++ name
--     typings <- typecheckBody m name paramTypes body
--     logTypes $ "typings:  " ++
--       intercalate "\n          " (List.map show typings) ++ "\n"
--     case typings of
--       [] -> do
--         logTypes "   no valid type"
--         -- XXX This is the wrong reason
--         return (typeError (ReasonAmbig name pos []) initTyping, body)
--       [typing] -> do
--         logTypes $ "   final typing: " ++ show typing
--         logTypes $ "   initial param typing: " ++ show paramTypes
--         let typing' = projectTyping typing paramTypes
--         logTypes $ "   projected typing: " ++ show typing'
--         if validTyping typing
--             then do
--                 logTypes $ "apply body typing" ++ showBody 4 body
--                 body' <- applyBodyTyping typing body
--                 logTypes $ "After body typing:" ++ showBody 4 body'
--                 return (typing',body')
--             else do
--                 logTypes $ "invalid: no body typing" ++ showBody 4 body
--                 return (typing', body)
--       typings -> do
--           logTypes $ name ++ " has " ++ show (length typings) ++
--             " typings, of which " ++
--             show (length (List.filter validTyping typings)) ++
--             " are valid"
--           let typingSets = List.map (Map.map Set.singleton . typingDict) typings
--           let merged = Map.filter ((>1).Set.size) $
--                        Map.unionsWith Set.union typingSets
--           let ambigs = List.map (\(v,ts) -> (v,Set.toAscList ts))
--                        $ assocs merged
--           return (typeError (ReasonAmbig name pos ambigs) initTyping, body)


-- -- |Like a monadic foldl over a list, where each application produces
-- --  a list of values, and for each element of the folded list, the
-- --  function is applied to every result from the previous element,
-- --  finally producing the list of all the results.
-- typecheckSequence :: (Typing -> t -> Compiler [Typing]) -> [Typing] -> [t] ->
--                     Compiler [Typing]
-- typecheckSequence f typings [] = return typings
-- typecheckSequence f typings (t:ts) = do
--     logTypes $ "Type checking " ++ show (1 + length ts) ++ " things with " ++
--       show (length typings) ++ " typings, " ++
--       show (length $ List.filter validTyping typings) ++ " of them valid"
--     typings' <- mapM (`f` t) typings
--     let typings'' = pruneTypings $ concat typings'
--     if List.null typings'
--       then return []
--       else if List.null typings'' || not (validTyping $ List.head typings'')
--               -- No point going further if it's already invalid
--            then return [List.head $ concat typings']
--            else typecheckSequence f typings'' ts


-- pruneTypings :: [Typing] -> [Typing]
-- pruneTypings [] = []
-- pruneTypings typings =
--     let pruned = nub $ List.filter validTyping typings
--     in  if List.null pruned
--         then typings
--         else pruned


-- typecheckBody :: ModSpec -> ProcName -> Typing -> [Placed Stmt] ->
--                  Compiler [Typing]
-- typecheckBody m name typing body = do
--     logTypes "Entering typecheckSequence from typecheckBody"
--     typings' <- typecheckSequence (typecheckPlacedStmt m name)
--                 [typing] body
--     logTypes $ "Body types: " ++ show typings'
--     return typings'
-- 
-- 
-- -- |Type check a single placed primitive operation given a list of
-- --  possible starting typings and corresponding clauses up to this prim.
-- typecheckPlacedStmt :: ModSpec -> ProcName -> Typing -> Placed Stmt ->
--                        Compiler [Typing]
-- typecheckPlacedStmt m caller typing pstmt =
--     typecheckStmt m caller (content pstmt) (place pstmt) typing
-- 
-- 
-- -- |Type check a single primitive operation, producing a list of
-- --  possible typings.
-- typecheckStmt :: ModSpec -> ProcName -> Stmt -> OptPos -> Typing ->
--                  Compiler [Typing]
-- typecheckStmt m caller call@(ProcCall cm name id args) pos typing = do
--     logTypes $ "Type checking call " ++ showStmt 4 call ++
--       showMaybeSourcePos pos
--     logTypes $ "   with types " ++ show typing
--     procs <- case id of
--         Nothing   -> callTargets cm name
--         Just pid -> return [ProcSpec cm name pid] -- XXX check modspec
--                                                   -- is valid; or just
--                                                   -- ignore pid?
--     logTypes $ "   potential procs: " ++
--            List.intercalate ", " (List.map show procs)
--     if List.null procs
--       then if 1 == length args
--            then return [typeError (ReasonUninit caller name pos) typing]
--            else return [typeError (ReasonUndef caller name pos) typing]
--       else do
--         typList <- mapM (matchingArgFlows caller name args pos typing) procs
--         let typList' = concat typList
--         let typList'' = List.filter validTyping typList'
--         let dups = snd $ List.foldr
--                    (\elt (s,l) ->
--                         if Set.member elt s
--                         then (s,if elt `elem` l then l else elt:l)
--                         else (Set.insert elt s,l))
--                    (Set.empty,[]) typList''
--         logTypes $ "Resulting valid types: " ++ show typList''
--         if List.null dups
--         then if List.null typList''
--              then do
--                 logTypes $ "Type error detected:\n" ++
--                     unlines (List.map show typList')
--                 return typList'
--              else return typList''
--         else return [typeError (ReasonOverload
--                                    (List.map fst $
--                                     List.filter
--                                       (List.any (`elem` dups) . snd) $
--                                     zip procs typList)
--                                    pos) typing]
-- typecheckStmt _ _ call@(ForeignCall "llvm" "move" [] args@[a1,a2]) pos typing
--     = (:[]) <$> unifyExprTypes pos a1 a2 typing
-- typecheckStmt _ _ call@(ForeignCall _ _ _ args) pos typing = do
--     -- Pick up any output casts
--     logTypes $ "Type checking foreign call " ++ showStmt 4 call
--     let typing' = List.foldr (noteOutputCast . content) typing args
--     logTypes $ "Resulting typing = " ++ show typing'
--     return [typing']
-- typecheckStmt m caller (Test stmts expr) pos typing = do
--     typings <- typecheckBody m caller typing stmts
--     mapM (\t -> typecheckArg' (content expr) (place expr) AnyType
--                 (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
--         typings
-- typecheckStmt _ _ Nop pos typing = return [typing]
-- typecheckStmt m caller (Cond test expr thn els) pos typing = do
--     typings <- typecheckSequence (typecheckPlacedStmt m caller) [typing] test
--     typings' <- mapM (\t -> typecheckArg' (content expr) (place expr) AnyType
--                             (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
--                 typings
--     typings'' <- typecheckSequence (typecheckPlacedStmt m caller) typings' thn
--     typecheckSequence (typecheckPlacedStmt m caller) typings'' els
-- typecheckStmt m caller (Loop body) pos typing =
--     typecheckSequence (typecheckPlacedStmt m caller) [typing] body
-- typecheckStmt m caller (For itr gen) pos typing =
--     -- XXX must handle generator type
--     return [typing]
-- typecheckStmt _ _ Break pos typing = return [typing]
-- typecheckStmt _ _ Next pos typing = return [typing]


-- |Ensure the two exprs have the same types; if both are variables, this
--  means unifying their types.
unifyExprTypes :: OptPos -> Placed Exp -> Placed Exp -> Typing
               -> Compiler Typing
unifyExprTypes pos a1 a2 typing = do
    let args = [a1,a2]
    let call = ForeignCall "llvm" "move" [] args
    logTypes $ "Type checking foreign instruction unifying arguments "
               ++ show a1 ++ " and " ++ show a2
    let typing' = List.foldr (noteOutputCast . content) typing args
    case expVar' $ content a2 of
        -- XXX Need new error for move to non-variable
        Nothing -> return
                   $ typeError (shouldnt $ "move to non-variable" ++ show call)
                     typing'
        Just toVar ->
          case ultimateExp $ content a1 of
              Var fromVar _ _ -> do
                let typing'' = unifyVarTypes fromVar toVar pos typing'
                logTypes $ "Resulting typing = " ++ show typing''
                return typing''
              expr -> do
                ty <- expType typing' (Unplaced expr)
                return $ constrainVarType
                         (shouldnt $ "type error in move" ++ show call)
                         toVar ty typing'


-- matchingArgFlows :: ProcName -> ProcName -> [Placed Exp] -> OptPos -> Typing -> ProcSpec -> Compiler [Typing]
-- matchingArgFlows caller called args pos typing pspec = do
--     params <- List.filter nonResourceParam <$> getParams pspec
--     logTypes $ "checking flow of call to " ++ show pspec
--         ++ " args " ++ show args
--         ++ " against params " ++ show params ++ "..."
--     case reconcileArgFlows params args of
--       Just args' -> do
--         logTypes $ "MATCHES; checking types: args = " ++ show args'
--         typing <- foldM (typecheckArg pos params $ procSpecName pspec)
--             typing $ zip3 [1..] params args'
--         logTypes $ "Type check result = " ++ show typing
--         return [typing]
--       Nothing -> do
--         logTypes "fails"
--         return [typeError (ReasonArity caller called pos (length args)
--                            (length  params))
--                 typing]

noteOutputCast :: Exp -> Typing -> Typing
noteOutputCast (Typed (Var name flow _) typ True) typing
  | flowsOut flow = constrainVarType ReasonShouldnt name typ typing
noteOutputCast _ typing = typing


-- -- |Match up params to args based only on flow, returning Nothing if
-- --  they don't match, and Just a possibly updated arglist if they
-- --  do.  The purpose is to handle passing an in-out argument pair
-- --  where only an output is expected.  This is permitted, and the
-- --  input half is just ignored.  This is performed after the code has
-- --  been flattened, so ParamInOut have already been turned into
-- --  adjacent pairs of ParamIn and ParamOut parameters.
-- reconcileArgFlows :: [Param] -> [Placed Exp] -> Maybe [Placed Exp]
-- reconcileArgFlows [] [] = Just []
-- reconcileArgFlows _ [] = Nothing
-- reconcileArgFlows [] _ = Nothing
-- reconcileArgFlows (Param _ _ ParamOut _:params)
--   (arg1:arg2:args)
--     | isHalfUpdate ParamIn (content arg1) &&
--       isHalfUpdate ParamOut (content arg2)
--     = (arg2:) <$> reconcileArgFlows params args
-- reconcileArgFlows (Param _ _ pflow _:params) (arg:args)
--     = let aflow = expFlow (content arg)
--       in if pflow == aflow || aflow == FlowUnknown
--       then (arg:) <$> reconcileArgFlows params args
--       else Nothing


-- |Does this parameter correspond to a manifest argument?
nonResourceParam :: Param -> Bool
nonResourceParam (Param _ _ _ (Resource _)) = False
nonResourceParam _ = True


-- typecheckArg :: OptPos -> [Param] -> ProcName ->
--                 Typing -> (Int,Param,Placed Exp) -> Compiler Typing
-- typecheckArg pos params pname typing (argNum,param,arg) = do
--     let reasonType = ReasonArgType pname argNum pos
--     if not $ validTyping typing
--       then return typing
--       else do
--       logTypes $ "type checking " ++ show arg ++ " against " ++ show param
--       typecheckArg' (content arg) (place arg) AnyType
--         (paramType param) typing reasonType
-- 
-- 
-- typecheckArg' :: Exp -> OptPos -> TypeSpec -> TypeSpec -> Typing ->
--                  TypeError -> Compiler Typing
-- typecheckArg' texp@(Typed expr typ cast) pos _ paramType typing reason = do
--     logTypes $ "Checking typed expr " ++ show texp
--     typ' <- fromMaybe AnyType <$> lookupType typ pos
--     logTypes $ "Determined type " ++ show typ'
--     let typ'' = if cast then AnyType else typ'
--     logTypes $ "Considering casting, type is " ++ show typ''
--     typecheckArg' expr pos typ'' paramType typing reason
--     -- typecheckArg' expr pos  typ'
--     --               paramType typing reason
-- typecheckArg' (Var var _ _) _ declType paramType typing reason = do
--     -- XXX should out flow typing be contravariant?
--     logTypes $
--         "Check Var " ++ var ++ ":" ++ show declType ++ " vs. " ++
--         show paramType ++
--         (if paramType `subtypeOf` declType then " succeeded" else " FAILED")
--     if paramType `subtypeOf` declType
--       then return $ constrainVarType reason var paramType typing
--       else if paramType == AnyType -- may be type checking recursion
--            then return typing
--            else return $ typeError reason typing
-- typecheckArg' (IntValue val) _ declType paramType typing reason =
--     return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "int" [])
--       typing reason
-- typecheckArg' (FloatValue val) _ declType paramType typing reason =
--     return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "float" [])
--       typing reason
-- typecheckArg' (StringValue val) _ declType paramType typing reason =
--     return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "string" [])
--       typing reason
-- typecheckArg' (CharValue val) _ declType paramType typing reason =
--     return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "char" [])
--       typing reason
-- typecheckArg' expr _ _ _ _ _ =
--     shouldnt $ "trying to type check expression " ++ show expr ++ "."
-- 
-- 
-- typecheckArg'' :: TypeSpec -> TypeSpec -> TypeSpec -> Typing -> TypeError ->
--                   Typing
-- typecheckArg'' callType paramType constType typing reason =
--     let realType =
--             if constType `subtypeOf` callType then constType else callType
--     in -- trace ("check call type " ++ show callType ++ " against param type " ++ show paramType ++ " for const type " ++ show constType) $
--        if paramType `subtypeOf` realType
--        then typing
--        else -- trace ("type error with constant: " ++ show realType ++ " vs. " ++ show paramType)
--             typeError reason typing


-- firstJust :: [Maybe a] -> Maybe a
-- firstJust [] = Nothing
-- firstJust (j@(Just _):_) = j
-- firstJust (Nothing:rest) = firstJust rest
-- 
-- 
-- listArity :: (t -> ArgFlowType) -> (t -> PrimFlow) -> [t] -> Int
-- listArity toFType toDirection lst =
--     sum [if toFType e == HalfUpdate && toDirection e == FlowOut then 0 else 1
--         | e <- lst]


-- applyBodyTyping :: Typing -> [Placed Stmt] -> Compiler [Placed Stmt]
-- applyBodyTyping typing =
--     mapM (placedApply (applyStmtTyping typing))
-- 
-- 
-- applyStmtTyping :: Typing -> Stmt -> OptPos -> Compiler (Placed Stmt)
-- applyStmtTyping typing call@(ProcCall cm name id args) pos = do
--     logTypes $ "typing call " ++ showStmt 4 call
--     let args' = List.map (fmap $ applyExpTyping typing) args
--     procs <- case id of
--         Nothing   -> callTargets cm name
--         Just n -> return [ProcSpec cm name n]
--     logTypes $ "   " ++ show (length procs) ++ " potential procs: "
--            ++ intercalate ", " (List.map show procs)
--     matches <- catMaybes <$> mapM (matchProcType typing args') procs
--     checkError (show (length matches) ++
--                 " matching procs (should be 1) for stmt "
--                 ++ showStmt 0 call)
--       (1 /= length matches)
--     let [(args'',proc)] = matches
--     let call' = ProcCall (procSpecMod proc) (procSpecName proc)
--                          (Just (procSpecID proc)) args''
--     logTypes $ "typed call = " ++ showStmt 4 call'
--     return $ maybePlace call' pos
-- applyStmtTyping typing call@(ForeignCall lang name flags args) pos = do
--     logTypes $ "typing call " ++ showStmt 0 call
--     let args' = List.map (fmap $ applyExpTyping typing) args
--     let instr = ForeignCall lang name flags args'
--     logTypes $ "typed call = " ++ showStmt 0 instr
--     return $ maybePlace instr pos
-- applyStmtTyping typing (Test stmts expr) pos = do
--     stmts' <- applyBodyTyping typing stmts
--     let expr' = fmap (applyExpTyping typing) expr
--     return $ maybePlace (Test stmts' expr') pos
-- applyStmtTyping typing (Cond test cond thn els) pos = do
--     test' <- applyBodyTyping typing test
--     let cond' = fmap (applyExpTyping typing) cond
--     thn' <- applyBodyTyping typing thn
--     els' <- applyBodyTyping typing els
--     return $ maybePlace (Cond test' cond' thn' els') pos
-- applyStmtTyping typing (Loop body) pos = do
--     body' <- applyBodyTyping typing body
--     return $ maybePlace (Loop body') pos
-- applyStmtTyping typing Nop pos = return $ maybePlace Nop pos
-- applyStmtTyping typing (For itr gen) pos = do
--     let itr' = fmap (applyExpTyping typing) itr
--     let gen' = fmap (applyExpTyping typing) gen
--     return $ maybePlace (For itr' gen') pos
-- applyStmtTyping typing Break pos = return $ maybePlace Break pos
-- applyStmtTyping typing Next pos = return $ maybePlace Next pos
-- 
-- 
-- applyExpTyping :: Typing -> Exp -> Exp
-- applyExpTyping _ expr@(IntValue _) =
--     Typed expr (TypeSpec ["wybe"] "int" []) False
-- applyExpTyping _ expr@(FloatValue _) =
--     Typed expr (TypeSpec ["wybe"] "float" []) False
-- applyExpTyping _ expr@(StringValue _) =
--     Typed expr (TypeSpec ["wybe"] "string" []) False
-- applyExpTyping _ expr@(CharValue _) =
--     Typed expr (TypeSpec ["wybe"] "char" []) False
-- applyExpTyping typing expr@(Var nm flow ftype)
--     = Typed expr (varType nm typing) False
-- applyExpTyping typing typed@(Typed _ _ True) =
--     typed
-- applyExpTyping typing (Typed expr _ False) =
--     applyExpTyping typing expr
-- applyExpTyping _ expr =
--     shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- matchProcType :: Typing -> [Placed Exp] -> ProcSpec
--               -> Compiler (Maybe ([Placed Exp], ProcSpec))
-- matchProcType typing args p = do
--     params <- List.filter nonResourceParam <$> getParams p
--     logTypes $ "   checking call to " ++
--         show p ++ " args " ++
--         show args ++ " against params " ++
--         show params
--     case reconcileArgFlows params args of
--         Nothing -> return Nothing
--         Just as -> do
--             argTypes <- mapM (expType typing) as
--             if all (uncurry subtypeOf)
--                 (zip argTypes (List.map paramType params))
--                 then return $ Just (as,p)
--                 else return Nothing


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
      zip [1..] $ procProtoParams $ procProto def
    mapM_ (placedApply (checkStmtTyped name pos)) $
          procDefSrc $ procImpln def


procDefSrc :: ProcImpln -> [Placed Stmt]
procDefSrc (ProcDefSrc def) = def
procDefSrc (ProcDefPrim _ _ _) = shouldnt "procDefSrc applied to ProcDefPrim"


checkParamTyped :: ProcName -> OptPos -> (Int,Param) -> Compiler ()
checkParamTyped name pos (num,param) =
    when (AnyType == paramType param) $
      reportUntyped name pos (" parameter " ++ show num)


checkStmtTyped :: ProcName -> OptPos -> Stmt -> OptPos -> Compiler ()
checkStmtTyped name pos (ProcCall pmod pname pid _ args) ppos = do
    when (isNothing pid || List.null pmod) $
         shouldnt $ "Call to " ++ pname ++ showMaybeSourcePos ppos ++
                  " left unresolved"
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (ForeignCall _ pname _ args) ppos =
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped _ _ (TestBool _) _ = return ()
checkStmtTyped name pos (And stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (Or stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (Not stmt) _ppos =
    placedApply (checkStmtTyped name pos) stmt
checkStmtTyped name pos (Cond tst thenstmts elsestmts) _ppos = do
    placedApply (checkStmtTyped name pos) tst
    mapM_ (placedApply (checkStmtTyped name pos)) thenstmts
    mapM_ (placedApply (checkStmtTyped name pos)) elsestmts
checkStmtTyped name pos (Loop stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (For itr gen) ppos = do
    checkExpTyped name pos ("for iterator" ++ showMaybeSourcePos ppos) $
                  content itr
    checkExpTyped name pos ("for generator" ++ showMaybeSourcePos ppos) $
                  content itr
checkStmtTyped _ _ Nop _ = return ()
checkStmtTyped _ _ Break _ = return ()
checkStmtTyped _ _ Next _ = return ()


checkArgTyped :: ProcName -> OptPos -> ProcName -> OptPos ->
                 (Int, Exp) -> Compiler ()
checkArgTyped callerName callerPos calleeName callPos (n,arg) =
    checkExpTyped callerName callerPos
                      ("in call to " ++ calleeName ++
                       showMaybeSourcePos callPos ++
                       ", arg " ++ show n) arg


checkExpTyped :: ProcName -> OptPos -> String -> Exp ->
                 Compiler ()
checkExpTyped callerName callerPos msg (Typed expr ty _)
    | ty /= AnyType = checkExpModed callerName callerPos msg expr
checkExpTyped callerName callerPos msg _ =
    reportUntyped callerName callerPos msg


checkExpModed :: ProcName -> OptPos -> String -> Exp
              -> Compiler ()
checkExpModed callerName callerPos msg (Var _ FlowUnknown _)
    = liftIO $ putStrLn $ "Internal error: In " ++ callerName ++
      showMaybeSourcePos callerPos ++ ", " ++ msg ++ " left with FlowUnknown"
checkExpModed _ _ _ _ = return ()



reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg =
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++
      showMaybeSourcePos pos ++ ", " ++ msg ++ " left untyped"


-- |Log a message, if we are logging type checker activity.
logTypes :: String -> Compiler ()
logTypes = logMsg Types

