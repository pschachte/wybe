--  File     : Clause.hs
--  Author   : Peter Schachte
--  Purpose  : Convert Wybe code to clausal (LPVM) form
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Clause (compileProc, compileLocalVTables,
               compileExternalVTables) where

import           AST
import           Control.Monad
import           Control.Monad.Trans               (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.List                         as List
import           Data.Map                          as Map
import           Data.Maybe                        as Maybe
import           Data.Ord                          as Ord
import           Data.Set                          as Set
import           Data.Char                         (ord)
import           UnivSet                           as USet
import           Options                           (LogSelection (Clause))
import           Snippets
import           Text.ParserCombinators.Parsec.Pos
import           Util
import           Resources
import           UnivSet                           (emptyUnivSet)
import           Config                            (byteBits, wordSize, wordSizeBytes,
                                                    vtableNamePrefix, adapterNamePostfix)


----------------------------------------------------------------
--                 Clause compiler monad
----------------------------------------------------------------

-- |The clause compiler monad is a state transformer monad carrying the
--  clause compiler state over the compiler monad.
type ClauseComp = StateT ClauseCompState Compiler


-- |Associate a version number with each variable name.
type Numbering = Map VarName Int


-- |The state of compilation of a clause; used by the ClauseComp monad.
-- This allows us to assign a "version" number to each variable; each
-- time a variable is assigned, the number increments.  All input uses
-- (reads) of a variable in a given statement use the current number of
-- the variable, and output (write) uses use the next number.  This
-- ensures that even a input use that follows an output use in the same
-- statement gets the current number.  At the end of each statement, the
-- next variable map is copied to the current variable map, so input
-- uses of a variable in the following statement refer to the output
-- variables of the previous statement.
data ClauseCompState = ClauseCompState {
        currVars       :: Numbering,   -- ^current var number for each var
        nextVars       :: Numbering,   -- ^var numbers after current stmt
        nextCallSiteID :: CallSiteID,  -- ^The next callSiteID to use
        vTableParamDict :: Map TypeVarBound PrimParam,
                                       -- ^compiled vtable params
        clauseImpurity :: Impurity    -- ^Impurity of the enclosing proc
        }


initClauseComp :: Impurity -> ClauseCompState
initClauseComp = ClauseCompState Map.empty Map.empty 0 Map.empty


-- |Get the next versioned name of the specified variable
nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    newNum <- gets (maybe 0 (+1) . Map.lookup name . nextVars)
    modify $ \st -> st {nextVars = Map.insert name newNum $ nextVars st}
    return $ PrimVarName name newNum


-- |Get the current versioned name of the specified variable
currVar :: String -> OptPos -> ClauseComp PrimVarName
currVar name pos = do
    dict <- gets currVars
    case Map.lookup name dict of
        Nothing -> do
            logClause $ "Found uninitialised variable " ++ name
            lift $ message Error
                    ("Uninitialised variable '" ++ name ++ "'") pos
            return $ PrimVarName name (-1)
        Just n -> return $ PrimVarName name n


-- |Get the current numbering
getCurrNumbering :: ClauseComp Numbering
getCurrNumbering = gets nextVars


-- |Set both current and next numberings to the specified mapping.
putNumberings :: Numbering -> ClauseComp ()
putNumberings numbering =
    modify (\st -> st {currVars = numbering, nextVars = numbering})


-- |Prepare for the next statement, promoting the final variable
-- numbering of the previous statement to be the current variable
-- numbering for the next statement.
finishStmt :: ClauseComp ()
finishStmt = do
    getCurrNumbering >>= putNumberings
    gets currVars >>= logClause . (("Finish with numbering " ++) . show)

-- |Return a list of prims to complete a proc body.  For a SemiDet body
-- that hasn't already had #success assigned a value, this will assign it
-- True; otherwise it'll be empty.
closingStmts :: Determinism -> [Param] -> ClauseComp [Placed Prim]
closingStmts detism params = do
    dict <- gets currVars
    let outs = List.filter (flowsOut . paramFlow) params
    logClause $ "Closing body with output parameters: " ++ show outs
    let undefs = List.filter (not . (`Map.member` dict) . paramName) outs
    logClause $ "  uninitialised outputs: " ++ show undefs
    assigns <- mapM (\Param{paramName=nm,paramType=ty}
                    -> assign nm ty (ArgUndef ty))
                    undefs
    tested <- Map.member outputStatusName <$> getCurrNumbering
    end <- if detism == SemiDet && not tested
               then (:assigns) <$> assign outputStatusName boolType (ArgInt 1 boolType)
               else return assigns
    logClause $ "Adding ending instructions: " ++ showPlacedPrims 4 end
    return end

-- |Return a prim to assign the specified value to the specified variable of the
-- specified type, and record the assignment.
assign :: String -> TypeSpec -> PrimArg -> ClauseComp (Placed Prim)
assign name typ val = do
    primVar <- nextVar name
    return $ Unplaced $ primMove val
           $ ArgVar primVar typ FlowOut Ordinary False


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: Impurity -> ClauseComp t -> Compiler t
evalClauseComp impurity clcomp =
    evalStateT clcomp $ initClauseComp impurity


-- |Compile a ProcDefSrc to a ProcDefPrim, ie, compile a proc
--  definition in source form to one in clausal form.
compileProc :: ProcDef -> Int -> Compiler ProcDef
compileProc proc@ProcDef{procImpln=ProcDefPrim{}} _ =
    -- Vtable generation may add already-compiled adapter procs before the
    -- normal clause pass reaches this module
    return proc
compileProc proc procID =
    evalClauseComp (procImpurity proc) $ do
        let body = case procImpln proc of
                ProcDefSrc body -> body
                ProcDefAbstract -> []
                impl -> shouldnt $ "compileProc ProcDefPrim " ++ show impl
        let proto = procProto proc
        let procName = procProtoName proto
        let params = content <$> procProtoParams proto
        let boundedTypeParams = procBoundedTypeParams proc
        let vTableParams = vtableParamsFor boundedTypeParams
        let vTableParamDict = Map.fromList (zip boundedTypeParams vTableParams)
        modify (\st -> st {nextCallSiteID=procCallSiteCount proc
                          ,vTableParamDict=vTableParamDict})
        logClause $ "--------------\nCompiling proc " ++ show proto
        mapM_ (nextVar . paramName) $ List.filter (flowsIn . paramFlow) params
        finishStmt
        mSpec <- lift getModuleSpec
        let pSpec = ProcSpec mSpec procName procID Set.empty
        startVars <- getCurrNumbering
        compiled <- case procAbstract proc of
            Just id -> compileAbstractBody pSpec id params Det
            Nothing -> compileBody body params Det
        logClause $ "Compiled to  :"  ++ showBlock 4 compiled
        endVars <- getCurrNumbering
        logClause $ "  startVars  : " ++ show startVars
        logClause $ "  endVars    : " ++ show endVars
        logClause $ "  params     : " ++ show params
        let idxs = scanl (\i f -> i + if flowsIn f && flowsOut f then 2 else 1) 0 $ paramFlow <$> params
            params' = concat (zipWith (compileParam gFlows startVars endVars procName) idxs params) ++ vTableParams
            gFlows  = makeGlobalFlows (zip [0..] params') $ procProtoResources proto
        let proto' = PrimProto (procProtoName proto) params' gFlows
        logClause $ "  comparams  : " ++ show params'
        logClause $ "  globalFlows: " ++ show gFlows
        callSiteCount <- gets nextCallSiteID
        return $ proc { procImpln = ProcDefPrim pSpec proto' compiled emptyProcAnalysis Map.empty,
                        procCallSiteCount = callSiteCount}


-- |Compile a proc body to LPVM form. By the time we get here, the form of the
--  body is very limited: it is a list of ProcCalls and ForeignCalls, possibly
--  ending with a single Cond statement whose test is a single TestBool
--  statement and whose then and else branches are also bodies satisfying these
--  conditions. If the proc is SemiDet, then the body must ends with a TestBool
--  statement, or with a Cond statement whose then and else branches satisfy
--  this condition. Everything else has already been transformed away.
--  Furthermore, TestBool statements only appear as the condition of a Cond
--  statement or, in the case of a SemiDet proc, as the final statement of a
--  body. This code assumes that these invariants are observed, and does not
--  worry whether the proc is Det or SemiDet.
compileBody :: [Placed Stmt] -> [Param] -> Determinism -> ClauseComp ProcBody
compileBody [] params detism = do
    logClause $ "Compiling empty body"
    end <- closingStmts detism params
    logClause $ "Compiling empty body produced:" ++ showPlacedPrims 4 end
    return $ ProcBody end NoFork
compileBody stmts params detism = do
    logClause $ "Compiling body:" ++ showBody 4 stmts
    let final = last stmts
    case content final of
        Cond tst thn els _ _ _ ->
          case content tst of
              TestBool var -> do
                front <- mapM compileSimpleStmt $ init stmts
                compileCond front (place final) var thn els params detism
              tstStmt ->
                shouldnt $ "CompileBody of Cond with non-simple test:\n"
                           ++ show tstStmt
        -- XXX There shouldn't be any semidet code here any more
        call@(ProcCall _ SemiDet _ _) ->
            shouldnt "compileBody of SemiDet call"
        _ -> do
          prims <- mapM compileSimpleStmt stmts
          end <- closingStmts detism params
          return $ ProcBody (prims++end) NoFork


-- |Compile an abstract trait method as a virtual call through the vtable
--  supplied for the trait's bounded type parameter.  The method's ordinary
--  parameters are still compiled as call arguments, and the usual closing
--  statements preserve their declared flows.
compileAbstractBody :: ProcSpec -> Int -> [Param] -> Determinism -> ClauseComp ProcBody
compileAbstractBody pSpec index params detism = do
    thisMod <- lift getModuleSpec
    vTableParamDict <- gets vTableParamDict
    -- Type checking guarantees that exactly one bounded type parameter belongs
    -- to this trait, so it identifies the vtable used for dispatch.
    let typeVarBound = trustFromJust "compileAbstractBody" $
            find (\(_,trait) -> typeModule trait == Just thisMod) (Map.keys vTableParamDict)
    let vTableParam = trustFromJust "compileAbstractBody" $ Map.lookup typeVarBound vTableParamDict
    let vTableArg = primParamToArg vTableParam
    procDef <- lift $ getProcDef pSpec
    let forwardedVTableArgs =
            [ primParamToArg $ trustFromJust "compileAbstractBody" $
                  Map.lookup boundedTypeParam vTableParamDict
            | boundedTypeParam <- procBoundedTypeParams procDef
            , boundedTypeParam /= typeVarBound
            ]
    callSiteID <- gets nextCallSiteID
    impurity <- gets clauseImpurity
    -- Compile each source-level parameter into its primitive calling form;
    -- parameters with both input and output flows may produce two arguments.
    let args = List.map paramToVar params
    args' <- concat <$> mapM (placedApply compileArg) args
    gFlows <- lift $ getProcGlobalFlows pSpec
    let prim = Unplaced $ PrimVirtualCall callSiteID vTableArg index impurity
                    (args' ++ forwardedVTableArgs) gFlows
    finishStmt
    end <- closingStmts detism params
    return $ ProcBody (prim:end) NoFork


compileCond :: [Placed Prim] -> OptPos -> Exp -> [Placed Stmt]
    -> [Placed Stmt] -> [Param] -> Determinism -> ClauseComp ProcBody
compileCond front pos (Typed expr _typ _) thn els params detism =
    compileCond front pos expr thn els params detism
compileCond front pos expr thn els params detism = do
    name' <- case expr of
        Var var ParamIn _ -> Just <$> currVar var Nothing
        _                 -> return Nothing
    logClause $ "conditional on " ++ show expr ++ " new name = " ++ show name'
    beforeTest <- getCurrNumbering
    thn' <- compileBody thn params detism
    afterThen <- getCurrNumbering
    logClause $ "  vars after then: " ++ show afterThen
    putNumberings beforeTest
    els' <- compileBody els params detism
    afterElse <- getCurrNumbering
    logClause $ "  vars after else: " ++ show afterElse
    let final = Map.intersectionWith max afterThen afterElse
    putNumberings final
    logClause $ "  vars after ite: " ++ show final
    let thnAssigns = reconcilingAssignments afterThen final params
    let elsAssigns = reconcilingAssignments afterElse final params
    case expr of
        IntValue 0 ->
            return $ prependToBody front $ appendToBody els' elsAssigns
        IntValue _ ->
            return $ prependToBody front $ appendToBody thn' thnAssigns
        Var _ ParamIn _ ->
            return $ ProcBody front
                $ PrimFork (fromJust name') boolType False
                  (zip [0..] [appendToBody els' elsAssigns, appendToBody thn' thnAssigns])
                Nothing
        _ ->
            shouldnt $ "TestBool with invalid argument " ++ show expr

compileSimpleStmt :: Placed Stmt -> ClauseComp (Placed Prim)
compileSimpleStmt stmt = do
    logClause $ "Compiling " ++ showStmt 4 (content stmt)
    stmt' <- compileSimpleStmt' (content stmt)
    finishStmt
    logClause $ "Compiled to " ++ show stmt'
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' call@(ProcCall func _ _ args) = do
    logClause $ "Compiling call " ++ showStmt 4 call
    callSiteID <- gets nextCallSiteID
    modify (\st -> st {nextCallSiteID = callSiteID + 1})
    impurity <- gets clauseImpurity
    case func of
        First mod name procID -> do
            let procID' = trustFromJust ("compileSimpleStmt' for " ++ showStmt 4 call)
                            procID
            let pSpec = ProcSpec mod name procID' generalVersion
            procDef <- lift (getProcDef pSpec)
            let impurity' = max impurity (procImpurity procDef)
            let params = procProtoParams $ procProto procDef
            let boundedTypeParams = procBoundedTypeParams procDef
            let typeVarMap = getTypeVarMap params args
            vTableArgs <- mapM (compileVTableArg typeVarMap) boundedTypeParams
            logClause $ "vTableArgs for " ++ name ++ ": " ++ show vTableArgs
            flows <- paramFlow <$$> lift (getParams pSpec)
            args' <- concat <$> zipWithM (placedApply . compileFlowArg) flows args 
            gFlows <- lift $ getProcGlobalFlows pSpec
            return $ PrimCall callSiteID pSpec impurity' (args' ++ vTableArgs) gFlows
        Higher fn -> do
            let impurity' = max impurity . modifierImpurity . higherTypeModifiers 
                          . trustFromJust ("untyped higher-order term " ++ show fn) . maybeExpType $ content fn
            fn' <- compileHigherFunc fn
            args' <- concat <$> mapM (placedApply compileArg) args 
            return $ PrimHigher callSiteID fn' impurity' args'
compileSimpleStmt' (ForeignCall "lpvm" "sizeof" flags [arg, out]) = do
    let ty = trustFromJust ("untyped in sizeof " ++ show arg)
           $ maybeExpType $ content arg
    unboxedSize <- case ty of
        Representation repn -> return $ typeRepSize repn
        TypeSpec modSpec name _ ->
            trustFromJust "compileSimpleStmt sizeof modTypeSize" 
                    <$> lift (getSpecModule "compileSimpleStmt sizeof" modTypeSize (modSpec ++ [name]))
        _ -> return wordSize
    let size = if "unboxed" `elem` flags then unboxedSize else min unboxedSize wordSize
    let sizeInUnit = if "bits" `elem` flags then size else size `ceilDiv` byteBits
    out' <- placedApply compileArg out
    return $ PrimForeign "lpvm" "cast" [] $ ArgInt (fromIntegral sizeInUnit) intType : out'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- concat <$> mapM (placedApply compileArg) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (TestBool expr) =
    -- Only for handling a TestBool other than as the condition of a Cond:
    compileSimpleStmt' $ content $ move (boolCast expr) (boolVarSet outputStatusName)
compileSimpleStmt' Nop =
    compileSimpleStmt' $ content $ move boolTrue (boolVarSet outputStatusName)
compileSimpleStmt' Fail =
    compileSimpleStmt' $ content $ move boolFalse (boolVarSet outputStatusName)
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


-- | Get a mapping from the type variable names to the argument types in a proc call
getTypeVarMap :: [Placed Param] -> [Placed Exp] -> Map TypeVarName TypeSpec
getTypeVarMap _ [] = Map.empty
getTypeVarMap params@(x:xs) args@(y:ys) =
    case (content x, content y) of
        (Param _ paramType _ _, Typed _ argType _) ->
            getTypeVarMap' paramType argType `Map.union` getTypeVarMap xs ys
        _ -> getTypeVarMap xs ys
getTypeVarMap params args = shouldnt $ "getTypeVariableMap " ++ show params ++ show args

getTypeVarMap' :: TypeSpec -> TypeSpec -> Map TypeVarName TypeSpec
getTypeVarMap' TypeVariable{typeVariableName=name} actual = Map.singleton name actual
getTypeVarMap' TypeSpec{typeParams=formals} TypeSpec{typeParams=actuals} =
    List.foldl' Map.union Map.empty $ zipWith getTypeVarMap' formals actuals
getTypeVarMap' HigherOrderType{higherTypeParams=formals}
           HigherOrderType{higherTypeParams=actuals} =
    List.foldl' Map.union Map.empty $ zipWith matchTypeFlows formals actuals
  where
    matchTypeFlows formal actual =
        getTypeVarMap' (typeFlowType formal) (typeFlowType actual)
getTypeVarMap' _ _ = Map.empty


compileVTableArg :: Map TypeVarName TypeSpec -> TypeVarBound -> ClauseComp PrimArg
compileVTableArg typeVarMap (paramVarName,paramVarBound) = do
    let argType = trustFromJust "compileVTableArg" $ Map.lookup paramVarName typeVarMap
    case argType of
        TypeVariable argVarName _ -> do
            vTableParamDict <- gets vTableParamDict
            let boundedVarInProc = (argVarName, paramVarBound)
            let param = trustFromJust ("compileVTableArg for vtable: " ++ show boundedVarInProc) $
                    Map.lookup boundedVarInProc vTableParamDict
            return $ ArgVTable (Right $ primParamName param)
                (Representation CPointer)
        _ -> do
            let ispec = TraitImplSpec paramVarBound argType
            return $ ArgVTable (Left ispec) (Representation CPointer)

compileFlowArg :: FlowDirection -> Exp -> OptPos -> ClauseComp [PrimArg]
compileFlowArg flow (Typed exp typ coerce) pos = do
    logClause $ "Compiling expression " ++ show exp
    args <- compileArg' typ exp pos
    args' <- 
        if flowsOut flow && not (flowsOut $ flattenedExpFlow exp)
        then do
            out <- nextVar "_"
            return $ args ++ [ArgVar out typ FlowOut Ordinary False]
        else return args
    logClause $ "Expression compiled to " ++ show args'
    return args'
compileFlowArg _ exp pos = shouldnt $ "Compiling untyped argument " ++ show exp

compileArg :: Exp -> OptPos -> ClauseComp [PrimArg]
compileArg exp = compileFlowArg (flattenedExpFlow exp) exp

compileArg' :: TypeSpec -> Exp -> OptPos -> ClauseComp [PrimArg]
compileArg' typ (IntValue int) _ = return [ArgInt int typ]
compileArg' typ (FloatValue float) _ = return [ArgFloat float typ]
compileArg' typ (ConstStruct structID) _ = do
    return [ArgConstRef structID typ]
compileArg' typ (CharValue char) _ = return [ArgInt (fromIntegral $ ord char) typ]
compileArg' typ (Global info) _ = return [ArgGlobal info typ]
compileArg' typ (Closure ms es) _ = do
    as <- concat <$> mapM (placedApply compileArg) es
    unless (sameLength es as)
           $ shouldnt "compileArg' Closure with in/out args"
    return [ArgClosure ms as typ]
compileArg' typ FailExpr _ = return [ArgInt 0 typ]
compileArg' typ var@(Var name flow flowType) pos = do
    inArg <- if flowsIn flow
        then do
            currName <- currVar name pos
            return [ArgVar currName typ FlowIn flowType False]
        else return []
    outArg <- if flowsOut flow
        then do
            nextName <- nextVar name
            return [ArgVar nextName typ FlowOut flowType False]
        else return []
    return $ inArg ++ outArg
compileArg' ty exp@Typed{} pos =
    shouldnt $ "Compiling multi-typed expression "
                ++ show exp ++ " with type " ++ show ty
compileArg' typ arg _ =
    shouldnt $ "Normalisation left complex argument: " ++ show arg

compileHigherFunc :: Placed Exp -> ClauseComp PrimArg
compileHigherFunc exp = do
    exps' <- placedApply compileArg exp
    case exps' of
        [arg] -> return arg
        _ -> shouldnt $ "compileHigherFunc of " ++ show exp


reconcilingAssignments :: Numbering -> Numbering
                       -> [Param] -> [Placed Prim]
reconcilingAssignments caseVars jointVars params =
    Maybe.mapMaybe (reconcileOne caseVars jointVars) params


reconcileOne :: Numbering -> Numbering -> Param
             -> Maybe (Placed Prim)
reconcileOne caseVars jointVars (Param name ty flow ftype) =
    case (Map.lookup name caseVars,
          Map.lookup name jointVars)
    of (Just caseNum, Just jointNum) ->
         if caseNum /= jointNum && elem flow [ParamOut, ParamInOut]
         then Just $ Unplaced $
              PrimForeign "llvm" "move" []
              [ArgVar (PrimVarName name caseNum) ty FlowIn
                      ftype False,
               ArgVar (PrimVarName name jointNum) ty FlowOut
                      ftype False]
         else Nothing
       _ -> Nothing


compileParam :: GlobalFlows -> Numbering -> Numbering -> ProcName -> Int -> Param -> [PrimParam]
compileParam allFlows startVars endVars procName idx param@(Param name ty flow ftype) =
    [PrimParam (PrimVarName name num) ty FlowIn ftype (ParamInfo False gFlows)
    | flowsIn flow
    , let num = Map.findWithDefault
                (shouldnt ("compileParam for input param " ++ show param
                            ++ " of proc " ++ show procName))
                name startVars
          gFlows
            | (isResourcefulHigherOrder ||| genericType ||| (==AnyType)) ty
            = emptyGlobalFlows{globalFlowsParams=USet.singleton inIdx}
            | otherwise = emptyGlobalFlows
    ]
    ++
    [PrimParam (PrimVarName name num) ty FlowOut ftype (ParamInfo False gFlows)
    | flowsOut flow
    , let num = Map.findWithDefault
                (shouldnt ("compileParam for output param " ++ show param
                            ++ " of proc " ++ show procName))
                name endVars
          gFlows
            | isResourcefulHigherOrder ty = univGlobalFlows
            | genericType ty || ty == AnyType = emptyGlobalFlows{globalFlowsParams=UniversalSet}
            | otherwise = emptyGlobalFlows
    ]
  where
    inIdx = idx
    outIdx = if flowsIn flow then idx + 1 else idx


vtableParam :: Int -> PrimParam
vtableParam index =
    PrimParam (PrimVarName vtableNamePrefix index) (Representation CPointer)
            FlowIn VTable (ParamInfo False emptyGlobalFlows)


vtableParamsFor :: [TypeVarBound] -> [PrimParam]
vtableParamsFor bounds =
    [vtableParam i | (i, _) <- zip [0..] bounds]


-- |Compile all locally-defined trait vtables.  This must happen before clause
-- compilation because adapting a concrete implementation to the trait ABI can
-- add adapter procedures to the current module.
compileLocalVTables :: ModSpec -> Compiler ()
compileLocalVTables thisMod = do
    reenterModule thisMod
    traitImpls <- Map.map content <$> getModuleImplementationField modKnownTraitImpls
    let localImpls = Map.toAscList $ Map.filter isNothing traitImpls
    vTables <- Map.fromAscList <$> mapM
        (\(index, (ispec, _)) -> do
            vtable <- compileVTable index ispec Nothing
            return (ispec, vtable))
        (zip [0..] localImpls)
    updateModule (\mod -> mod{ modVTables = Map.union vTables $ modVTables mod })
    reexitModule


-- |Compile declarations for the external vtables actually referenced by the
-- module's lowered code.
compileExternalVTables :: ModSpec -> Compiler ()
compileExternalVTables thisMod = do
    reenterModule thisMod
    defs <- concat . Map.elems <$> getModuleImplementationField modProcs
    let bodies = concatMap allProcBodies defs
        referenced = execState
            (mapM_ (mapLPVMBodyM (const $ return ()) collectVTable) bodies)
            Set.empty
        collectVTable (ArgVTable (Left ispec) _) = modify $ Set.insert ispec
        collectVTable _ = return ()
    traitImpls <- Map.map content <$> getModuleImplementationField modKnownTraitImpls
    let addReferenced impls ispec = case Map.lookup ispec traitImpls of
            Nothing -> shouldnt $ "unknown referenced vtable " ++ show ispec
            Just Nothing -> impls
            Just (Just mod) -> Map.insert ispec mod impls
        externalImpls = Set.foldl' addReferenced Map.empty referenced
    vTables <- Map.traverseWithKey
        (\ispec mod -> do
            definingVTables <- getModule modVTables `inModule` mod
            let (index, _) = trustFromJust
                    ("compileExternalVTables: missing vtable " ++ show ispec
                        ++ " in " ++ showModSpec mod)
                    (Map.lookup ispec definingVTables)
            compileVTable index ispec $ Just mod)
        externalImpls
    updateModule (\mod -> mod{ modVTables = Map.union vTables $ modVTables mod })
    reexitModule


compileVTable :: Int -> TraitImplSpec -> Maybe ModSpec -> Compiler (Int, StructID)
compileVTable index ispec opmod = do
    logMsg Clause $ "Compiling vtable for trait impl " ++ show ispec ++ " defined in " ++ show opmod
    thisMod <- getModuleSpec
    traitImplProcSpecs <- getModuleImplementationField modTraitImplProcs
        `inModule` fromMaybe thisMod opmod
    let procSpecs = trustFromJust "compileVTable" $ Map.lookup ispec traitImplProcSpecs
    procSpecs' <- case opmod of
        Nothing -> adaptTraitImplProcs ispec procSpecs
        Just _  -> return procSpecs
    when (isNothing opmod && procSpecs' /= procSpecs) $
        updateModImplementation $ \imp -> imp {
            modTraitImplProcs = Map.insert ispec procSpecs'
                (modTraitImplProcs imp) }
    let sz = wordSizeBytes * length procSpecs
        values = List.map FnPointerStructMember procSpecs'
    structId <- recordConstStruct
            (VTableInfo sz values (isJust opmod) index ispec (fromMaybe thisMod opmod)) Nothing
    return (index, structId)


-- |Return the procedure specs to store in a locally-defined vtable.  A concrete
-- implementation can have a different ABI from the corresponding abstract
-- method because abstract type variables use defaultTypeRepresentation.  When
-- that happens, store a generated adapter in the vtable instead.
adaptTraitImplProcs :: TraitImplSpec -> [ProcSpec] -> Compiler [ProcSpec]
adaptTraitImplProcs ispec@(TraitImplSpec trait typ) procSpecs = do
    absProcs <- List.map fst <$> abstractProcs trait
    unless (sameLength absProcs procSpecs) $
        shouldnt $ "vtable proc count mismatch for " ++ show ispec
            ++ ": abstract procs " ++ show absProcs
            ++ ", implementation procs " ++ show procSpecs
    zipWithM (adaptTraitImplProc ispec) absProcs procSpecs


adaptTraitImplProc :: TraitImplSpec -> ProcSpec -> ProcSpec -> Compiler ProcSpec
adaptTraitImplProc ispec absProcSpec implProcSpec = do
    absProcDef <- getProcDef absProcSpec
    implProcDef <- getProcDef implProcSpec
    let adapterParams = vtableSlotParams ispec absProcDef
    generateAdapter ispec absProcDef adapterParams implProcSpec implProcDef


-- |The ABI used by a virtual call through a vtable slot.  This is the abstract
-- method's primitive parameters, except that the dispatching vtable parameter
-- itself is supplied by the loaded vtable and is not passed to the target proc.
vtableSlotParams :: TraitImplSpec -> ProcDef -> [PrimParam]
vtableSlotParams (TraitImplSpec trait _) absProcDef =
    procOrdinaryABIParams absProcDef
        ++ vtableParamsFor (forwardedVTableBounds trait absProcDef)


forwardedVTableBounds :: TraitSpec -> ProcDef -> [TypeVarBound]
forwardedVTableBounds dispatchTrait absProcDef =
    [ bounded
    | bounded@(_, bound) <- procBoundedTypeParams absProcDef
    , typeModule bound /= typeModule dispatchTrait
    ]


-- |Return the canonical primitive ABI parameters for the source-level ordinary
-- parameters of a proc.
procOrdinaryABIParams :: ProcDef -> [PrimParam]
procOrdinaryABIParams =
    compileABIParams . (content <$>) . procProtoParams . procProto


-- |Convert source-level parameters to their canonical primitive ABI shape,
-- independent of the SSA numbering used by a compiled proc body.
compileABIParams :: [Param] -> [PrimParam]
compileABIParams = concatMap compileABIParam
  where
    compileABIParam (Param name ty flow ftype) =
        [PrimParam (PrimVarName name 0) ty FlowIn ftype (ParamInfo False emptyGlobalFlows)
            | flowsIn flow]
        ++
        [PrimParam (PrimVarName name (outNum flow)) ty FlowOut ftype (ParamInfo False emptyGlobalFlows)
            | flowsOut flow]
    outNum flow = if flowsIn flow then 1 else 0


generateAdapter :: TraitImplSpec -> ProcDef -> [PrimParam] -> ProcSpec -> ProcDef
                  -> Compiler ProcSpec
generateAdapter ispec absProcDef adapterParams implProcSpec implProcDef = do
    adapterMod <- getModuleSpec
    gFlows <- getProcGlobalFlows implProcSpec
    let adapterOrdinaryParams = procOrdinaryABIParams absProcDef
        implOrdinaryParams = procOrdinaryABIParams implProcDef
    unless (sameLength adapterOrdinaryParams implOrdinaryParams) $
        shouldnt $ "adapter ordinary param count mismatch for "
            ++ show implProcSpec ++ ": abstract params "
            ++ show adapterOrdinaryParams ++ ", implementation params "
            ++ show implOrdinaryParams
    bridges <- zipWith3M adapterArgBridge [0..]
        adapterOrdinaryParams implOrdinaryParams
    let (preCasts, implOrdinaryArgs, postCasts) = unzip3 bridges
        implCallArgs = implOrdinaryArgs
            ++ adapterVTableArgs ispec absProcDef implProcDef adapterParams
    let adapterName = procName absProcDef ++ adapterNamePostfix
        proto = PrimProto adapterName adapterParams
            $ makeGlobalFlows (zip [0..] adapterParams)
                (procProtoResources $ procProto absProcDef)
        body = ProcBody
            (concat preCasts
                ++ [Unplaced $ PrimCall 0 implProcSpec (procImpurity implProcDef)
                    implCallArgs gFlows]
                ++ concat postCasts)
            NoFork
        pSpec = ProcSpec adapterMod adapterName 0 generalVersion
        adapter = ProcDef adapterName (ProcProto adapterName [] [])
            (ProcDefPrim pSpec proto body emptyProcAnalysis Map.empty)
            Nothing 0 1 Map.empty Private Nothing (procDetism implProcDef)
            NoInline (procImpurity implProcDef) AdapterProc
            (initSuperprocSpec Private) Map.empty [] 0
    adapterSpec <- addProcDef adapter `inModule` adapterMod
    updateProcDef
        (\proc -> case procImpln proc of
            prim@ProcDefPrim{} -> proc {
                procImpln = prim { procImplnProcSpec = adapterSpec } }
            _ -> proc)
        adapterSpec
    logMsg Clause $ "Generated vtable adapter " ++ show adapterSpec
        ++ " for " ++ show implProcSpec ++ " in " ++ show ispec
    return adapterSpec


-- |Bridge one ordinary adapter parameter to the corresponding implementation
-- parameter.  The adapter exposes the vtable slot ABI, so any concrete
-- implementation type with a different source type must be reached through an
-- LPVM cast or, for wide concrete values in generic slots, a box/unbox.
adapterArgBridge :: Int -> PrimParam -> PrimParam
                 -> Compiler ([Placed Prim], PrimArg, [Placed Prim])
adapterArgBridge idx adapterParam implParam
    | primParamFlow adapterParam /= primParamFlow implParam =
        shouldnt $ "adapter param flow mismatch: " ++ show adapterParam
            ++ " vs " ++ show implParam
    | primParamType adapterParam == primParamType implParam =
        return ([], primParamToArg adapterParam, [])
    | otherwise = do
        implSize <- typeRepSize <$> typeRepresentation implTy
        let useBox = typeNeedsBoxing adapterTy && implSize > wordSize
            implSizeBytes = ArgInt (fromIntegral $ implSize `ceilDiv` byteBits) intType
            zero = ArgInt 0 intType
        return $ case (primParamFlow implParam, useBox) of
            (FlowIn, True) ->
                ([Unplaced $ PrimForeign "lpvm" "access" []
                    [adapterIn, zero, implSizeBytes, zero, implOut]], implIn, [])
            (FlowIn, False) ->
                ([Unplaced $ primCast implOut adapterIn], implIn, [])
            (FlowOut, True) ->
                ([]
                , implOut
                , [ Unplaced $ PrimForeign "lpvm" "alloc" []
                        [implSizeBytes, adapterBoxOut]
                  , Unplaced $ PrimForeign "lpvm" "mutate" []
                        [adapterBoxIn, adapterOut, zero, zero, implSizeBytes, zero, implIn]
                  ])
            (FlowOut, False) ->
                ([], implOut, [Unplaced $ primCast adapterOut implIn])
            (flow, _) ->
                shouldnt $ "unexpected adapter param flow " ++ show flow
  where
    adapterTy = primParamType adapterParam
    implTy = primParamType implParam
    implFlowType = primParamFlowType implParam
    tmpName = PrimVarName
        (primVarName (primParamName implParam) ++ adapterNamePostfix ++ show idx)
        0
    boxName = PrimVarName
        (primVarName (primParamName adapterParam) ++ adapterNamePostfix ++ "box" ++ show idx)
        0
    implIn = ArgVar tmpName implTy FlowIn implFlowType False
    implOut = ArgVar tmpName implTy FlowOut implFlowType False
    adapterIn = primParamToArg adapterParam
    adapterOut = primParamToArg adapterParam
    adapterBoxIn = ArgVar boxName AnyType FlowIn Ordinary False
    adapterBoxOut = ArgVar boxName AnyType FlowOut Ordinary False


adapterVTableArgs :: TraitImplSpec -> ProcDef -> ProcDef -> [PrimParam] -> [PrimArg]
adapterVTableArgs ispec@(TraitImplSpec trait _) absProcDef implProcDef adapterParams =
    snd $ List.mapAccumL vtableArg forwardedParams (procBoundedTypeParams implProcDef)
  where
    dispatchTraitMod = typeModule trait
    forwardedParams =
        [ param
        | (_, param) <- zip forwardedBounds
            (List.filter ((== VTable) . primParamFlowType) adapterParams)
        ]
    forwardedBounds = forwardedVTableBounds trait absProcDef
    vtableArg params (_, bound)
        | typeModule bound == dispatchTraitMod =
            (params, ArgVTable (Left ispec) (Representation CPointer))
        | otherwise = case params of
            param:rest -> (rest, ArgVTable (Right $ primParamName param)
                (Representation CPointer))
            [] -> shouldnt $ "missing forwarded vtable parameter for bound " ++ show bound


-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param outputStatusName boolType ParamOut Ordinary


-- |Log a message, if we are logging clause generation.
logClause :: String -> ClauseComp ()
logClause s = lift $ logMsg Clause s
