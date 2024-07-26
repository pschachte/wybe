--  File     : LLVM.hs
--  Author   : Peter Schachte, based on work by Ashutosh Rishi Ranjan
--  Purpose  : Generate LLVM code from LPVM form
--  Copyright: (c) 2024 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module LLVM ( llvmMapBinop, llvmMapUnop, writeLLVM ) where

import           AST
import           ASTShow
import           Resources
import           BinaryFactory
import           Config
import           Options
import           Version
import           CConfig
import           Snippets
import           System.IO
import           Data.Set                        as Set
import qualified Data.Map                        as Map
import           Data.Map                        (Map)
import           Data.List                       as List
import           Data.Maybe
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.IO.Class
import           Data.Tuple.HT
import qualified Data.ByteString                 as B
import qualified Data.ByteString.Lazy            as BL
import qualified Data.ByteString.Internal        as BI


-- BEGIN MAJOR DOC
-- 
-- # Generating LLVM code
-- 
-- We generate a `.ll` text file directly for each Wybe `.wybe` file, compiling
-- this as necessary to build `.o`, `.bc` or executable files.  For each
-- generated `.ll` file, we produce the following, in order:
-- 
--  * **Prologue** — contains an introductory comment and any configuration info
--     needed for LLVM.
--
--  * **Constants** — LLVM definitions of the manifest constants used in this
--      module; mostly used for strings.
--
--  * **Global variables** —  LLVM declarations of the global variables used to
--     implement the resources defined in this module.
--
--  * **Externs** — Extern declarations for all symbols used, but not defined, in
--   this module; this includes imported Wybe procedures, C functions,  and
--     global variables.
--
--  * **Definitions** — Definitions of the procs of this module.
--
--  * **Exports** — Everything needed by the Wybe compiler to compile users of
--   this module; currently this is represented as a serialisation of the Module
--   data structure, placed in the LLVM section.
--
-- END MAJOR DOC



----------------------------------------------------------------------------
-- Instruction maps
--
-- What we need to know about LLVM instructions
----------------------------------------------------------------------------


-- | A map of arithmetic binary operations supported through LLVM to
-- their Codegen module counterpart.
llvmMapBinop :: Map Ident (String,
                    TypeFamily, TypeRepresentation -> TypeRepresentation)
llvmMapBinop =
    Map.fromList [
            -- Integer arithmetic
            ("add",  ("add",  IntFamily, id)),
            ("sub",  ("sub",  IntFamily, id)),
            ("mul",  ("mul",  IntFamily, id)),
            ("udiv", ("udiv", IntFamily, id)),
            ("sdiv", ("sdiv", IntFamily, id)),
            ("urem", ("urem", IntFamily, id)),
            ("srem", ("srem", IntFamily, id)),
            -- Integer comparisions
            ("icmp_eq",  ("icmp eq",  IntFamily, const $ Bits 1)),
            ("icmp_ne",  ("icmp ne",  IntFamily, const $ Bits 1)),
            ("icmp_ugt", ("icmp ugt", IntFamily, const $ Bits 1)),
            ("icmp_uge", ("icmp uge", IntFamily, const $ Bits 1)),
            ("icmp_ult", ("icmp ult", IntFamily, const $ Bits 1)),
            ("icmp_ule", ("icmp ule", IntFamily, const $ Bits 1)),
            ("icmp_sgt", ("icmp sgt", IntFamily, const $ Bits 1)),
            ("icmp_sge", ("icmp sge", IntFamily, const $ Bits 1)),
            ("icmp_slt", ("icmp slt", IntFamily, const $ Bits 1)),
            ("icmp_sle", ("icmp sle", IntFamily, const $ Bits 1)),
            -- Bitwise operations
            ("shl",  ("shl",  IntFamily, id)),
            ("lshr", ("lshr", IntFamily, id)),
            ("ashr", ("ashr", IntFamily, id)),
            ("or",   ("or",   IntFamily, id)),
            ("and",  ("and",  IntFamily, id)),
            ("xor",  ("xor",  IntFamily, id)),

            -- Floating point arithmetic
            ("fadd", ("fadd", FloatFamily, id)),
            ("fsub", ("fsub", FloatFamily, id)),
            ("fmul", ("fmul", FloatFamily, id)),
            ("fdiv", ("fdiv", FloatFamily, id)),
            ("frem", ("frem", FloatFamily, id)),
            -- Floating point comparisions
            ("fcmp_eq",  ("fcmp oeq",  FloatFamily, const $ Bits 1)),
            ("fcmp_ne",  ("fcmp one",  FloatFamily, const $ Bits 1)),
            ("fcmp_slt", ("fcmp olt", FloatFamily, const $ Bits 1)),
            ("fcmp_sle", ("fcmp ole", FloatFamily, const $ Bits 1)),
            ("fcmp_sgt", ("fcmp ogt", FloatFamily, const $ Bits 1)),
            ("fcmp_sge", ("fcmp oge", FloatFamily, const $ Bits 1))
           ]

-- | A map of unary llvm operations wrapped in the 'Codegen' module.
llvmMapUnop :: Map String (TypeFamily, TypeFamily)
llvmMapUnop =
    Map.fromList [
            ("uitofp", (IntFamily, FloatFamily)),
            ("sitofp", (IntFamily, FloatFamily)),
            ("fptoui", (FloatFamily, IntFamily)),
            ("fptosi", (FloatFamily, IntFamily))
           ]


----------------------------------------------------------------------------
-- Generating LLVM for a module
----------------------------------------------------------------------------

-- | Generate LLVM code for the specified module, based on its LPVM code, and
-- write it to the specified file handle.
writeLLVM :: Handle -> ModSpec -> Bool -> Compiler ()
writeLLVM handle modSpec withLPVM = do
    reenterModule modSpec
    logMsg LLVM $ "*** Generating LLVM for module " ++ showModSpec modSpec
    logWrapWith '-' . show <$> getModule id
    flip execStateT (initLLVMState handle) $ do
        preScanProcs
        writeAssemblyPrologue
        writeAssemblyConstants
        writeAssemblyGlobals
        writeAssemblyExterns
        writeAssemblyProcs
        when withLPVM writeAssemblyExports
    logMsg LLVM $ "*** Finished generating LLVM for " ++ showModSpec modSpec
    reexitModule


----------------------------------------------------------------------------
-- Scanning the module in preparation
----------------------------------------------------------------------------

-- | Scan proc bodies to find and record whatever we need to later produce the
-- llvm assembly code for the current module.  Currently we collect string
-- constants and extern declarations for foreign procs and imported Wybe procs
-- used by the module.
preScanProcs :: LLVM ()
preScanProcs = do
    mod <- llvmGetModule modSpec
    bodies <- lift $ getModuleImplementationField
            (concatMap (concatMap allProcBodies) . Map.elems . modProcs)
    let (strings,externs) =
            List.foldl (preScanBody mod) (Set.empty, Set.empty) bodies
    modify $ \s -> s{allStrings = strings, allExterns = externs}


type PreScanState = (Set String, Set ExternSpec)


-- | Collect all the string constants appearing in a proc body as a set
preScanBody :: ModSpec -> PreScanState -> ProcBody -> PreScanState
preScanBody mod = foldLPVMPrims (preScanPrim mod)


preScanPrim :: ModSpec -> PreScanState -> Prim -> PreScanState
preScanPrim mod (strings,externs) prim =
    let strings' = foldLPVMPrimArgs argStrings strings prim
        externs' = addExtern mod prim externs
    in (strings', externs')


-- | If the specified PrimArg is a string constant, add it to the set
argStrings set (ArgString str _ _) = Set.insert str set
argStrings set _                   = set


-- | Construct and return a whole extern declaration ready to be emitted.
addExtern :: ModSpec -> Prim -> Set ExternSpec -> Set ExternSpec
addExtern mod (PrimCall _ pspec _ args _) externs =
    if mod `isPrefixOf` procSpecMod pspec then externs
    else recordExtern args (llvmProcName pspec) externs
addExtern _ PrimHigher{} externs = externs
addExtern _ (PrimForeign "llvm" _ _ _) externs = externs
addExtern _ (PrimForeign "lpvm" "alloc" _ _) externs =
    let externName = llvmForeignName "wybe_malloc"
        extern = (externName, [intType], [Representation CPointer])
    in Set.insert extern externs
addExtern _ (PrimForeign "lpvm" _ _ _) externs = externs
addExtern _ (PrimForeign "c" name _ args) externs =
    recordExtern args (llvmForeignName name) externs
addExtern _ (PrimForeign other name _ args) externs =
    shouldnt $ "Unknown foreign language " ++ other


-- | Insert the fact that the named function is an external function with the
-- specified argument types in the provided set, returning the resulting set.
recordExtern :: [PrimArg] -> LLVMName -> Set ExternSpec -> Set ExternSpec
recordExtern args fName externs =
    let (ins,outs,oRefs,iRefs) = partitionByFlow argFlowDirection args
        extern = (fName
                 , (argType <$> ins) ++ (Representation CPointer <$ oRefs)
                 , argType <$> outs)
    in if List.null iRefs then Set.insert extern externs
       else shouldnt $ "Function " ++ fName ++ " has TakeReference parameters"


----------------------------------------------------------------------------
-- Writing the prologue
----------------------------------------------------------------------------

-- | Write out some boilerplate at the beginning of a generated .ll file.
-- Included are a comment identifying the source of the file and the information
-- required for the file to be compilable.
writeAssemblyPrologue :: LLVM ()
writeAssemblyPrologue = do
    mod <- llvmGetModule modSpec
    srcFile <- llvmGetModule modOrigin
    llvmPutStrLn $ ";; FILE GENERATED BY wybemk "
                ++ Version.version
                ++ " (" ++ Version.gitHash
                ++ ") -- see https://github.com/pschachte/wybe"
    llvmPutStrLn $ ";; Module " ++ showModSpec mod
    llvmBlankLine
    llvmPutStrLn $ "source_filename = \"" ++ srcFile ++ "\""
    llvmPutStrLn $ "target triple   = \"" ++ Version.defaultTriple ++ "\""
    llvmBlankLine
    return ()


----------------------------------------------------------------------------
-- Writing the constant definitions
----------------------------------------------------------------------------

-- | Write out definitions of manifest constants used in generated code for this
-- module.
writeAssemblyConstants :: LLVM ()
writeAssemblyConstants = do
    strings <- gets $ Set.toList . allStrings
    zipWithM_ declareString strings [0..]
    llvmBlankLine

-- | Write out a declaration for a string and record its name.
declareString :: String -> Int -> LLVM ()
declareString str n = do
    let textName = specialName2 "cstring" $ show n
    let stringName = specialName2 "string" $ show n
    modify $ \s -> s { stringConstants=Map.insert str stringName
                                       $ stringConstants s}
    declareStructConstant stringName
        [ (ArgInt (fromIntegral $ length str) (Representation $ Bits wordSize)
          , Bits wordSize)
        , (ArgGlobal (GlobalVariable textName) (Representation CPointer)
          , Pointer)]
        Nothing
    declareStringConstant textName str Nothing
    llvmBlankLine


----------------------------------------------------------------------------
-- Writing the global variable definitions
----------------------------------------------------------------------------

-- | Write out definitions of global variables to implement the resources of
-- this module.
writeAssemblyGlobals :: LLVM ()
writeAssemblyGlobals = do
    resDefs <- modResources . trustFromJust "writeAssemblyGlobals"
                <$> llvmGetModule modImplementation
    let ress = concatMap Map.keys (Map.elems resDefs)
    mapM_ defGlobalResource ress


-- | Generate a global declaration for a resource, if it's not a phantom.
defGlobalResource :: ResourceSpec -> LLVM ()
defGlobalResource res = do
    (name, rep) <- llvmResource res
    if repIsPhantom rep
        then return ()
        else llvmPutStrLn $ name ++ " = global " ++ llvmTypeRep rep ++ " undef"


----------------------------------------------------------------------------
-- Writing extern declarations
----------------------------------------------------------------------------

-- | Write out extern declarations for all procs and resources imported from
-- other modules and used by this one.
writeAssemblyExterns :: LLVM ()
writeAssemblyExterns = do
    copyFn <- llvmGlobalName <$> llvmMemcpyFn
    let spec = (copyFn, Representation <$> [CPointer,CPointer,Bits wordSize,Bits 1], [])
    externs <- (spec:) . Set.toList <$> gets allExterns
    mapM_ declareExtern externs


declareExtern :: ExternSpec -> LLVM ()
declareExtern (name, ins, outs) = do
    outs' <- lift $ filterM (notM . typeIsPhantom) outs
    ins' <- lift $ filterM (notM . typeIsPhantom) ins
    outTy <- llvmReturnType outs'
    argTypes <- (llvmTypeRep <$>) <$> mapM typeRep ins'
    llvmPutStrLn $ "declare " ++ outTy ++ " " ++ name ++ "("
                  ++ intercalate ", " argTypes ++ ")"


----------------------------------------------------------------------------
-- Writing procedure definitions
----------------------------------------------------------------------------

-- | Generate and write out the LLVM code for all the procs defined in this
-- module.
writeAssemblyProcs :: LLVM ()
writeAssemblyProcs = do
    mod <- llvmGetModule modSpec
    procs <- lift $ getModuleImplementationField
                    (concatMap (`zip` [0..]) . Map.elems . modProcs)
    mapM_ (uncurry (writeProcLLVM mod)) procs


-- | Generate and write out the LLVM code for the given proc with its proc
-- number and all its specialisations.
writeProcLLVM :: ModSpec -> ProcDef -> Int -> LLVM ()
writeProcLLVM mod def procNum =
    case procImpln def of
        ProcDefPrim {procImplnProcSpec=pspec, procImplnProto=proto,
                     procImplnBody=body, procImplnSpeczBodies=specz} -> do
            let params = primProtoParams proto
            let tmpCount = procTmpCount def
            -- XXX overriding procSpeczVersion should not be needed, but it is!
            writeProcSpeczLLVM pspec{procSpeczVersion=Set.empty} tmpCount params body
            let msg = "Required specialisations should be generated by now"
            let specz' = List.map (mapSnd (trustFromJust msg))
                         $ Map.toList specz
            -- Make sure there aren't collision in specz version id. If this
            -- happens, we should increase the length of id (see AST.hs).
            let hasDuplicates l = List.length l /= (Set.size . Set.fromList) l
            when (hasDuplicates (List.map fst specz'))
                    $ shouldnt $ "Specialisation version hash conflicts"
                        ++ show (List.map fst specz')
            mapM_ (\(speczVersion, speczBody) -> do
                    -- rename this version of proc
                    let pspec' = pspec{procSpeczVersion=speczVersion}
                    writeProcSpeczLLVM pspec' tmpCount params speczBody
                    ) specz'

        _ -> shouldnt $ "Generating assembly code for uncompiled proc "
                        ++ showProcName (procName def)


-- | Write out the LLVM code for a single LPVM proc specialisation (including no
-- specialisation), given the ProcSpec, temp variable count, parameter list, and
-- body.
writeProcSpeczLLVM :: ProcSpec -> Int -> [PrimParam] -> ProcBody -> LLVM ()
writeProcSpeczLLVM pspec tmpCount params body = do
    logLLVM $ "Generating LLVM for proc " ++ show pspec
    initialiseLLVMForProc tmpCount
    let name = llvmProcName pspec
    (ins,outs,oRefs,iRefs) <- partitionParams params
    unless (List.null iRefs)
        $ nyi $ "take-reference parameter for proc " ++ show pspec
    setRenaming $ Set.fromList $ primParamName <$> outs
    returnType <- llvmReturnType $ List.map primParamType outs
    oRefParams <- mapM recordProcOutByRef oRefs
    llParams <- mapM llvmParameter $ ins ++ oRefParams
    llvmBlankLine
    llvmPutStrLn $
        "define external fastcc " ++ returnType ++ " "
            ++ name ++ "(" ++ intercalate ", " llParams ++ ")"
            ++ " alwaysinline {"
    writeAssemblyBody outs body
    llvmPutStrLn "}"



-- | Create an opaque pointer parameter for each out-by-reference parameter, and
-- record the correspondence, so we can translate assignments to the
-- out-by-reference parameter into a store through the opaque pointer.
recordProcOutByRef :: PrimParam -> LLVM PrimParam
recordProcOutByRef param@PrimParam{primParamName=p, primParamType=ty} = do
    tmp <- makeTemp
    let rep = Representation CPointer
    let readCPtrArg = ArgVar tmp rep FlowIn Ordinary True
    let actualParam = param{primParamName=tmp, primParamType=rep,
                            primParamFlow=FlowIn}
    addTakeRefPointer p readCPtrArg ty
    return actualParam


-- | Generate and write out the LLVM code for an LPVM body
writeAssemblyBody :: [PrimParam] -> ProcBody -> LLVM ()
writeAssemblyBody outs ProcBody{bodyPrims=prims, bodyFork=fork} = do
    mapM_ (placedApply writeAssemblyPrim) prims
    case fork of
        NoFork -> do
            releaseDeferredCall
            writeAssemblyReturn outs
        PrimFork{forkVar=v, forkVarType=ty, forkBodies=branches,
                 forkDefault=dflt} -> do
            rep <- typeRep ty
            case (rep,branches,dflt) of
                (Bits 0,_,_) -> shouldnt "Switch on a phantom!"
                (_,[single],Nothing) -> writeAssemblyBody outs single
                (Bits 1, [els,thn],Nothing) -> writeAssemblyIfElse outs v thn els
                (Bits _, cases, dflt) -> writeAssemblySwitch outs v rep cases dflt
                (rep,_,_) -> llvmPutStrLn $ "Switching on " ++ show rep ++ " type "
                                ++ show ty


----------------------------------------------------------------------------
-- Generating and emitting LLVM for a single LPVM Prim instruction
----------------------------------------------------------------------------

--

-- | Generate and write out the LLVM code for a single LPVM prim
writeAssemblyPrim :: Prim -> OptPos -> LLVM ()
writeAssemblyPrim instr@(PrimCall _ proc _ args _) pos = do
    releaseDeferredCall
    logLLVM $ "Translating Wybe call " ++ show instr
    writeWybeCall proc args pos
writeAssemblyPrim instr@(PrimHigher _ fn _ args) pos = do
    releaseDeferredCall
    logLLVM $ "Translating HO call " ++ show instr
    writeHOCall fn args pos
writeAssemblyPrim instr@(PrimForeign "llvm" op flags args) pos = do
    releaseDeferredCall
    logLLVM $ "Translating LLVM instruction " ++ show instr
    writeLLVMCall op flags args pos
writeAssemblyPrim instr@(PrimForeign "lpvm" op flags args) pos = do
    -- Some of these should be handled before releasing deferred calls
    logLLVM $ "Translating LPVM instruction " ++ show instr
    writeLPVMCall op flags args pos
writeAssemblyPrim instr@(PrimForeign "c" cfn flags args) pos = do
    releaseDeferredCall
    logLLVM $ "Translating C call " ++ show instr
    writeCCall cfn flags args pos
writeAssemblyPrim instr@(PrimForeign lang op flags args) pos = do
    shouldnt $ "unknown foreign language " ++ lang
                ++ " in instruction " ++ show instr


-- | Generate and write out an LLVM if-then-else (switch on an i1 value)
writeAssemblyIfElse :: [PrimParam] -> PrimVarName -> ProcBody -> ProcBody
                    -> LLVM ()
writeAssemblyIfElse outs v thn els = do
    releaseDeferredCall
    [thnlbl,elslbl] <- freshLables ["if.then.","if.else."]
    llvar <- varToRead v
    llvmPutStrLnIndented $ "br i1 " ++ llvar
                    ++ ", " ++ llvmLableName thnlbl
                    ++ ", " ++ llvmLableName elslbl
    llvmPutStrLn $ thnlbl ++ ":"
    writeAssemblyBody outs thn
    llvmPutStrLn $ elslbl ++ ":"
    writeAssemblyBody outs els


-- | Generate and write out an LLVM multi-way switch
writeAssemblySwitch :: [PrimParam] -> PrimVarName -> TypeRepresentation
                    -> [ProcBody] -> Maybe ProcBody -> LLVM ()
writeAssemblySwitch outs v rep cases dflt = do
    releaseDeferredCall
    let prefixes0 = ["case."++show n++".switch." | n <- [0..length cases-1]]
    (dfltLabel:labels) <- freshLables $ "default.switch." : prefixes0
    let llType = llvmTypeRep rep
    llvar <- varToRead v
    logLLVM $ "Switch on " ++ llvar ++ " with cases " ++ show cases
    llvmPutStrLnIndented $ "switch " ++ llType ++ " " ++ llvar ++ ", "
        ++ llvmLableName dfltLabel ++ " [\n    "
        ++ intercalate "\n    "
                [llType ++ " " ++ show n ++ ", " ++ llvmLableName lbl
                | (lbl,n) <- zip labels [0..]]
        ++ " ]"
    zipWithM_
        (\lbl cs -> llvmPutStrLn (lbl ++ ":") >> writeAssemblyBody outs cs)
        labels cases
    llvmPutStrLn $ dfltLabel ++ ":"
    -- I don't think the Nothing case ever happens, but in case it does...
    writeAssemblyBody outs $ fromMaybe (last cases) dflt


-- | Generate a Wybe proc call instruction, or defer it if necessary.
writeWybeCall :: ProcSpec -> [PrimArg] -> OptPos -> LLVM ()
writeWybeCall wybeProc args pos = do
    (ins,outs,oRefs,iRefs) <- partitionArgsWithRefs args
    unless (List.null iRefs)
     $ shouldnt $ "Wybe call " ++ show wybeProc ++ " with take-reference arg"
    if List.null oRefs then
        writeActualCall wybeProc ins outs "tail "
    else
        deferCall wybeProc ins outs oRefs


-- | Generate a Wybe proc call instruction, or defer it if necessary.
writeHOCall :: PrimArg -> [PrimArg] -> OptPos -> LLVM ()
writeHOCall callee args pos = do
    (ins,outs,oRefs,iRefs) <- partitionArgsWithRefs args
    let hoCall = PrimHigher 0 callee Pure args
    unless (List.null iRefs)
     $ shouldnt $ "Higher order call " ++ show hoCall
                ++ " with take-reference arg"
    unless (List.null oRefs && List.null iRefs)
     $ nyi $ "Higher order call with out-by-ref or take-ref argument "
            ++ show hoCall
    outTy <- llvmReturnType $ List.map argType outs
    (writeArg,readArg) <- freshTempArgs $ Representation CPointer
    typeConvert callee writeArg
    fnVar <- llvmValue readArg
    argList <- llvmArgumentList ins
    llvmStoreResult outs $
        "tail call fastcc " ++ outTy ++ " " ++ fnVar ++ argList


-- | Actually generate a Wybe proc call.  tailFlag indicates what degree of LLVM
-- tail call optimisation we want.
writeActualCall :: ProcSpec -> [PrimArg] -> [PrimArg] -> String -> LLVM ()
writeActualCall wybeProc ins outs tailFlag = do
        outTy <- llvmReturnType $ List.map argType outs
        argList <- llvmArgumentList ins
        llvmStoreResult outs $
            tailFlag ++ "call fastcc " ++ outTy ++ " " ++ llvmProcName wybeProc
            ++ argList


-- | Generate a native LLVM instruction
writeLLVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLLVMCall op flags args pos = do
    (ins,outs) <- partitionArgs ("llvm " ++ op ++ " instruction") args
    logLLVM $ "llvm instr args " ++ show args ++ " => ins "
             ++ show ins ++ " ; outs " ++ show outs
    argList <- llvmInstrArgumentList ins
    logLLVM $ "translated arg list: " ++ argList
    case (ins,outs) of
        ([],[]) -> return () -- eliminate if all data flow was phantoms
        ([arg],[out@ArgVar{argVarName=outVar}]) ->
            if op == "move" then
                typeConvert arg out
            else if op `Map.member` llvmMapUnop then do
                outTy <- llvmTypeRep <$> argTypeRep out
                llvmStoreResult outs $ op ++ " " ++ argList ++ " to " ++ outTy
            else shouldnt $ "unknown unary llvm op " ++ op
        ([_,_],_) -> do
            let instr =
                    fst3 $ trustFromJust ("unknown binary llvm op " ++ op)
                    $ Map.lookup op llvmMapBinop
            llvmStoreResult outs $ instr ++ " " ++ argList
        _ -> shouldnt $ "unknown llvm op " ++ op ++ " (arity "
                         ++ show (length ins) ++ ")"


-- | Generate LPVM (memory management) instruction
writeLPVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLPVMCall "alloc" _ args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm alloc instruction" args
    case args' of
        ([sz],[out]) ->
            marshalledCCall "wybe_malloc" [] [sz,out] ["int","pointer"] pos
        _ ->
            shouldnt $ "lpvm alloc with arguments " ++ show args
writeLPVMCall "cast" _ args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm cast instruction" args
    case args' of
        ([],[]) -> return ()
        ([val],[var]) -> do
            typeConvert val var
        (ins, outs) ->
            shouldnt $ "lpvm cast with arguments " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall "load" _ args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm load instruction" args
    case args' of
        ([],[]) -> return ()
        ([global],[outVar]) -> llvmLoad global outVar
        (ins, outs) ->
            shouldnt $ "lpvm load with inputs " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall "store" _ args pos = do
    -- XXX We could actually support take-reference for this op
    releaseDeferredCall
    args' <- partitionArgs "lpvm store instruction" args
    case args' of
        ([],[]) -> return ()
        (args@[_,_],[]) -> do
            llargs <- llvmArgumentList args
            llvmPutStrLnIndented $ "store " ++ llargs
        (ins, outs) ->
            shouldnt $ "lpvm store with inputs " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall "access" _ args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm access instruction" args
    case args' of
        ([struct, offset, _, _], outs@[member]) -> do
            logLLVM $ "llvm access offset = " ++ show offset
            addrArg <- case offset of
                ArgInt 0 _ -> return struct
                _ -> do
                        (writeArg,readArg) <- freshTempArgs $ argType struct
                        writeLLVMCall "add" [] [struct,offset,writeArg] Nothing
                        return readArg
            lltype <- llvmTypeRep <$> argTypeRep member
            arg <- typeConverted addrArg CPointer
            llvmStoreResult outs $ "load " ++ lltype ++ ", " ++ arg
        (ins,outs) ->
            shouldnt $ "lpvm access with inputs " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall "mutate" _ args pos = do
    args' <- partitionArgsWithRefs args
    case args' of
        (_,_,_:_,_) ->
             shouldnt $ "LPVM mutate instruction with out-by-reference arg: "
                        ++ show args
        (struct:offset:destr:size:startOffset:restIns,[struct2],_,iRefs) -> do
            -- XXX Must support take-reference for this op
            when (List.null iRefs) releaseDeferredCall
            case destr of
                ArgInt 1 _ -> do
                    logLLVM "lpvm mutate destructive case"
                    typeConvert struct struct2
                ArgInt 0 _ -> do
                    logLLVM "lpvm mutate non-destructive case"
                    duplicateStruct struct startOffset size struct2
                _ ->
                    nyi "lpvm mutate instr with non-const destructive flag"
            ptrArg <- case offset of
                ArgInt 0 _ -> return struct2
                _ -> do
                    (writeArg,readArg) <- freshTempArgs $ argType struct
                    writeLLVMCall "add" [] [struct,offset,writeArg] Nothing
                    return readArg
            logLLVM $ "address to store into is held by " ++ show ptrArg
            case (restIns,iRefs) of
                ([member],[]) -> do
                    logLLVM "Normal (non-take-reference) case"
                    llMember <- llvmArgument member
                    dest <- typeConverted ptrArg CPointer
                    llvmPutStrLnIndented $ "store " ++ llMember
                                            ++ ", " ++ dest
                ([],[takeRef]) -> do
                    -- FlowTakeReference case:  generate and record a fresh
                    -- local variable to hold the pointer to the location the
                    -- value should be written in, once it's generated.
                    logLLVM "Special take-reference case"
                    (writeCPtrArg,readCPtrArg) <-
                        freshTempArgs $ Representation CPointer
                    let takeRefVar = argVar "in lpvm alloc" takeRef
                    addTakeRefPointer takeRefVar readCPtrArg (argType takeRef)
                    takeRefs <- gets takeRefVars
                    logLLVM $ "take-ref pointers = " ++ show takeRefs
                    typeConvert ptrArg writeCPtrArg
                _ ->
                    shouldnt $ "lpvm mutate with inputs "
                            ++ show (struct:offset:destr:size:startOffset:restIns)
                            ++ " and output " ++ show struct2
        (ins,outs,oRefs,iRefs) ->
            shouldnt $ "lpvm mutate with inputs " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall op flags args pos =
    shouldnt $ "unknown lpvm operation:  " ++ op


-- | Generate C function call
writeCCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeCCall cfn flags args pos = do
    (ins,outs) <- partitionArgs ("call to C function " ++ cfn) args
    outTy <- llvmReturnType $ List.map argType outs
    argList <- llvmArgumentList ins
    llvmStoreResult outs $ "call " ++ outTy ++ " " ++ llvmGlobalName cfn
                            ++ argList


-- | Generate C function call with inputs and outputs type converted as needed.
marshalledCCall :: ProcName -> [Ident] -> [PrimArg] -> [String] -> OptPos
                -> LLVM ()
marshalledCCall cfn flags args ctypes pos = do
    (ins,outs) <- partitionArgTuples cfn $ zip args ctypes
    argList <- llvmStringArgList <$> mapM (uncurry marshallArgument) ins
    let instr = llvmGlobalName cfn ++ argList
    case outs of
        [] -> llvmPutStrLnIndented $ "call void " ++ instr
        [(out,cType)] -> marshallCallResult out cType instr
        _ -> shouldnt "C function call with multiple outputs"


-- | Generate and write out the LLVM return statement.
writeAssemblyReturn :: [PrimParam] -> LLVM ()
writeAssemblyReturn [] = llvmPutStrLnIndented "ret void"
writeAssemblyReturn [PrimParam{primParamName=v, primParamType=ty}] = do
    llty <- llvmTypeRep <$> typeRep ty
    llvar <- varToRead v
    llvmPutStrLnIndented $ "ret " ++ llty ++ " " ++ llvar
writeAssemblyReturn params = do
    retType <- llvmReturnType $ List.map primParamType params
    tuple <- buildTuple retType "undef" 0 params
    llvmPutStrLnIndented $ "ret " ++ retType ++ " " ++ tuple


-- | Generate code to build a tuple to return for multi-output functions.
-- Returns the last variable generated.
-- Generated code looks like %"temp#25" = insertvalue {i64, i1} undef, i64 %8, 0
buildTuple :: LLVMType -> LLVMName -> Int -> [PrimParam] -> LLVM LLVMName
buildTuple _ tuple _ [] = return tuple
buildTuple outType tuple argNum
           (PrimParam{primParamName=v, primParamType=ty}:params) = do
    llty <- llvmTypeRep <$> typeRep ty
    llvar <- varToRead v
    nextVar <- llvmLocalName <$> makeTemp
    llvmPutStrLnIndented $ nextVar ++ " = insertvalue " ++ outType ++ " "
                            ++ tuple ++ ", " ++ llty ++ " " ++ llvar
                            ++ ", " ++ show argNum
    buildTuple outType nextVar (argNum+1) params


----------------------------------------------------------------------------
-- Writing the export information ("header" file equivalent)
----------------------------------------------------------------------------

-- | Write out data needed for wybemk to compile users of this module.  This
-- includes all the declared types and other submodules, resources, interfaces
-- of all public procs, and definitions of inline public procs, written as a
-- large constant string in the LPVM section of the file.
writeAssemblyExports :: LLVM ()
writeAssemblyExports = do
    llvmBlankLine
    m <- llvmGetModule modSpec
    modBS <- lift $ List.map BI.w2c . BL.unpack <$> encodeModule m
    declareStringConstant (showModSpec m) modBS $ Just "__LPVM,__lpvm"


----------------------------------------------------------------------------
-- Support code
----------------------------------------------------------------------------

-- | Emit an LLVM declaration for a string constant, optionally specifying a
-- file section.
declareStringConstant :: LLVMName -> String -> Maybe String -> LLVM ()
declareStringConstant name str section = do
    llvmPutStrLn $ llvmGlobalName name
                    ++ " = private unnamed_addr constant "
                    ++ showLLVMString str True
                    ++ maybe "" ((", section "++) . show) section
                    ++ ", align " ++ show wordSizeBytes


-- | Emit an LLVM declaration for a string constant, optionally specifying a
-- file section.
declareStructConstant :: LLVMName -> [ConstSpec] -> Maybe String -> LLVM ()
declareStructConstant name fields section = do
    llvmFields <- llvmConstStruct fields
    llvmPutStrLn $ llvmGlobalName name
                    ++ " = private unnamed_addr constant " ++ llvmFields
                    ++ maybe "" ((", section "++) . show) section
                    ++ ", align " ++ show wordSizeBytes


-- | Build a string giving the body of an llvm constant structure declaration
llvmConstStruct :: [ConstSpec] -> LLVM String
llvmConstStruct fields = do
    llvmVals <- mapM (uncurry convertedConstant) fields
    return $ llvmRepReturnType (snd <$> fields)
            ++ " { " ++ intercalate ", " llvmVals ++ " }"


-- | Generate an LLVM load instruction to load from the specified address into
-- the specified variable
llvmLoad :: PrimArg -> PrimArg -> LLVM ()
llvmLoad ptr outVar = do
    lltype <- llvmTypeRep <$> argTypeRep outVar
    arg <- typeConverted ptr CPointer
    llvmStoreResult [outVar] $ "load " ++ lltype ++ ", " ++ arg


-- | Return the representation for the specified type
typeRep :: TypeSpec -> LLVM TypeRepresentation
typeRep ty =
    trustFromJust ("lookupTypeRepresentation of unknown type " ++ show ty)
      <$> lift (lookupTypeRepresentation ty)



llvmResource :: ResourceSpec -> LLVM (LLVMName, TypeRepresentation)
llvmResource res = do
    (res', ty) <-
        mapSnd (trustFromJust $ "defGlobalResource " ++ show res)
        <$> lift (canonicaliseResourceSpec Nothing "newLLVMModule" res)
    rep <- typeRep ty
    return (llvmGlobalName (makeGlobalResourceName res'), rep)



-- | The LLVM representation of a Wybe type based on its TypeRepresentation
llvmTypeRep :: TypeRepresentation -> LLVMType
llvmTypeRep (Bits bits)     = "i" ++ show bits
llvmTypeRep (Signed bits)   = "i" ++ show bits
llvmTypeRep (Floating 16)   = "half"
llvmTypeRep (Floating 32)   = "float"
llvmTypeRep (Floating 64)   = "double"
llvmTypeRep (Floating 128)  = "fp128"
llvmTypeRep (Floating n)    = shouldnt $ "invalid float size " ++ show n
-- XXX these should be made more accurate (use pointer and function types):
llvmTypeRep (Func _ _)      = llvmTypeRep $ Bits wordSize
llvmTypeRep Pointer         = llvmTypeRep $ Bits wordSize
llvmTypeRep CPointer        = "ptr"


-- | The LLVM return type for proc with the specified list of output type specs.
llvmRepReturnType :: [TypeRepresentation] -> LLVMType
llvmRepReturnType [] = "void"
llvmRepReturnType [ty] = llvmTypeRep ty
llvmRepReturnType tys =
    "{" ++ intercalate ", " (List.map llvmTypeRep tys) ++ "}"


-- | The LLVM return type for proc with the specified list of output type specs.
llvmReturnType :: [TypeSpec] -> LLVM LLVMType
llvmReturnType specs = llvmRepReturnType <$> mapM typeRep specs


-- | The LLVM parameter declaration for the specified Wybe input parameter as a
-- pair of LLVM type and variable name.
llvmParameter :: PrimParam -> LLVM String
llvmParameter PrimParam{primParamName=name, primParamType=ty,
                        primParamFlow=FlowIn} = do
    let llname = llvmLocalName name
    lltype <- llvmTypeRep <$> typeRep ty
    return $ lltype ++ " " ++ llname
llvmParameter PrimParam{primParamName=name,
                        primParamFlow=FlowOutByReference} = do
    let llname = llvmLocalName name
    return $ "ptr " ++ llname
llvmParameter param =
    shouldnt $ "parameter " ++ show param ++ " should be an input"


-- | The LLVM translation of the specified call instruction argument list
llvmArgumentList :: [PrimArg] -> LLVM String
llvmArgumentList inputs = llvmStringArgList <$> mapM llvmArgument inputs


llvmStringArgList :: [String] -> String
llvmStringArgList = ('(':). (++")") . intercalate ", "


-- | The LLVM translation of the specified LLVM instruction argument list
llvmInstrArgumentList :: [PrimArg] -> LLVM String
llvmInstrArgumentList [] = return ""
llvmInstrArgumentList inputs@(in1:_) = do
    lltype <- llvmTypeRep <$> argTypeRep in1
    argsString <- intercalate ", " <$> mapM llvmValue inputs
    return $ lltype ++ " " ++ argsString


-- | Write the LLVM translation of the specified output argument list as target
-- for the specified instruction.  For multiple outputs, we must unpack a tuple.
llvmStoreResult :: [PrimArg] -> String -> LLVM ()
llvmStoreResult [] instr = llvmPutStrLnIndented instr
llvmStoreResult [ArgVar{argVarName=varName}] instr = do
    llVar <- varToWrite varName
    llvmPutStrLnIndented $ llVar ++ " = " ++ instr
llvmStoreResult multiOuts instr = do
    tuple <- llvmLocalName <$> makeTemp
    retType <- llvmReturnType $ argVarType <$> multiOuts
    llvmPutStrLnIndented $ tuple ++ " = " ++ instr
    -- This uses llvmStoreResult to store each individual element of tuple
    zipWithM_ (unpackArg retType tuple) multiOuts [0..]


-- | Marshall data returned by C code.  Emits a C call instruction, which
-- returns its result in the specified type representation, leaving its
-- output in the specified output variable with its expected type
-- representation, type converting it if necessary.
marshallCallResult :: PrimArg -> String -> String -> LLVM ()
marshallCallResult outArg@ArgVar{argVarName=varName} cType instr = do
    let inTypeRep = trustFromJust
            ("marshalling output with unknown C type " ++ cType)
            $ cTypeRepresentation cType
    outTypeRep <- argTypeRep outArg
    let instr' = "call " ++ llvmTypeRep inTypeRep ++ " " ++ instr
    if inTypeRep == outTypeRep then llvmStoreResult [outArg] instr'
    else do
        (writeTmp,readTmp) <- freshTempArgs $ Representation inTypeRep
        llvmStoreResult [writeTmp] instr'
        typeConvert readTmp outArg
marshallCallResult outArg inTypeRep instr =
    shouldnt $ "Can't marshall result into non-variable " ++ show outArg


-- | Write an LLVM instruction to unpack one argument from a tuple.
-- instruction looks like:  %var = extractvalue {i64, i1} %0, 0
unpackArg :: LLVMType -> LLVMName -> PrimArg -> Int -> LLVM ()
unpackArg typ tuple arg argNum = do
    llvmStoreResult [arg] $ "extractvalue " ++ typ
                            ++ tuple ++ ", " ++ show argNum


-- | Marshall data being passed to C code.  Emits code to transform the argument
-- to the expected format for C code, and returns the llvm argument to actually
-- pass to the C function.
marshallArgument :: PrimArg -> String -> LLVM LLVMArg
marshallArgument arg cType = do
    let outTypeRep = trustFromJust
            ("marshalling argument with unknown C type " ++ cType)
            $ cTypeRepresentation cType
    inTypeRep <- argTypeRep arg
    if inTypeRep == outTypeRep then llvmArgument arg
    else typeConverted arg outTypeRep


-- | The LLVM type of the specified 
argTypeRep :: PrimArg -> LLVM TypeRepresentation
argTypeRep ArgString{} = return CPointer -- strings are all C pointers
argTypeRep arg = typeRep $ argType arg


-- | The LLVM argument for the specified PrimArg as an LLVM type and value
llvmArgument :: PrimArg -> LLVM LLVMArg
llvmArgument arg = do
    lltype <- llvmTypeRep <$> argTypeRep arg
    llVal <- llvmValue arg
    return $ lltype ++ " " ++ llVal


-- | A PrimArg as portrayed in LLVM code
llvmValue :: PrimArg -> LLVM String
llvmValue ArgVar{argVarName=var} = varToRead var
llvmValue (ArgInt val _) = return $ show val
llvmValue (ArgFloat val _) = return $ show val
llvmValue (ArgString str _ _) =
    gets $ llvmGlobalName
            . trustFromJust ("String constant " ++ show str ++ " not recorded")
            . Map.lookup str
            . stringConstants
llvmValue (ArgChar val _) = return $ show $ fromEnum val
llvmValue cl@ArgClosure{} = nyi $ "passing closure argument " ++ show cl
llvmValue (ArgGlobal val _) = llvmGlobalInfoName val
llvmValue (ArgUnneeded val _) = shouldnt "llvm value of unneeded arg"
llvmValue (ArgUndef _) = return "undef"


-- | The variable name of a PrimArg, or Nothing if not a variable
argVar :: String -> PrimArg -> PrimVarName
argVar _ ArgVar{argVarName=var} =  var
argVar msg _ = shouldnt $ "variable argument expected " ++ msg


-- | Emit an instruction to convert the specified input argument to the
-- specified output argument.
typeConvert :: PrimArg -> PrimArg -> LLVM ()
typeConvert fromArg toArg = do
    toTy <- argTypeRep toArg
    fromTy <- argTypeRep fromArg
    fromVal <- llvmValue fromArg
    case toArg of
        ArgVar{argVarName=varName} | fromTy == toTy ->
            renameVariable varName fromVal
        _ ->
            llvmStoreResult [toArg]
              $ typeConvertOp fromTy toTy ++ " "
                ++ llvmTypeRep fromTy ++ " " ++ fromVal
                ++ " to " ++ llvmTypeRep toTy


-- | LLVM code to convert PrimArg fromVal to representation toTy, returning a
-- LLVMName holding the converted value.
typeConverted :: PrimArg -> TypeRepresentation -> LLVM LLVMArg
typeConverted fromArg toTy
    | argIsConst fromArg = convertedConstant fromArg toTy
    | otherwise = do
        argRep <- argTypeRep fromArg
        if argRep == toTy
            then llvmArgument fromArg
            else do
                (writeArg,readArg) <- freshTempArgs $ Representation toTy
                typeConvert fromArg writeArg
                llvmArgument readArg

-- | An LLVM constant expression of the specified type toTy, when the constant
-- is initially of the specified type fromTy.  This may take the form of an
-- LLVM type conversion expression, which is fully evaluated at compile-time, so
-- it cannot involve conversion instructions.
convertedConstant :: PrimArg -> TypeRepresentation -> LLVM LLVMArg
convertedConstant arg toTy = do
    -- XXX should verify that arg is constant, if ArgGlobal is considered const
    fromTy <- argTypeRep arg
    let llvmTy = llvmTypeRep toTy
    if trivialConstConversion fromTy toTy
        then ((llvmTy++" ") ++) <$> llvmValue arg
        else do
            fromArg <- llvmArgument arg
            return $ llvmTy ++ " " ++ typeConvertOp fromTy toTy ++ "( "
                         ++ fromArg ++ " to " ++ llvmTy ++ " )"

-- Converting constants between these types is completely trivial, because the
-- constant is automatically considered to have both types.
trivialConstConversion (Bits _) (Bits _)         = True
trivialConstConversion (Bits _) (Signed _)       = True
trivialConstConversion (Signed _) (Signed _)     = True
trivialConstConversion (Signed _) (Bits _)       = True
trivialConstConversion (Floating _) (Floating _) = True
trivialConstConversion _ _                       = False


-- | The appropriate type conversion operator to convert from fromTy to toTy
typeConvertOp :: TypeRepresentation -> TypeRepresentation -> String
typeConvertOp fromTy toTy
    | fromTy == toTy = "bitcast" -- use bitcast for no-op conversion
typeConvertOp (Bits n) Pointer = "bitcast"
typeConvertOp (Signed n) Pointer = "bitcast"
typeConvertOp CPointer Pointer = "ptrtoint"
typeConvertOp rep Pointer =
    shouldnt $ "can't convert from " ++ show rep ++ " to address"
typeConvertOp Pointer (Bits n) = "bitcast"
typeConvertOp Pointer (Signed n) = "bitcast"
typeConvertOp Pointer CPointer = "inttoptr"
typeConvertOp Pointer rep =
    shouldnt $ "can't convert from address to " ++ show rep
typeConvertOp (Bits m) (Bits n)
    | m < n = "zext"
    | n < m = "trunc"
    | otherwise = shouldnt "no-op unsigned int conversion"
typeConvertOp (Bits m) (Signed n)
    | m < n = "sext"
    | n < m = "trunc"
    | otherwise = -- no instruction actually needed, but one is expected
        "bitcast"
typeConvertOp (Bits m) (Floating n) = "uitofp"
typeConvertOp (Signed m) (Bits n)
    | m < n = "zext"
    | n < m = "trunc"
    | otherwise = -- no instruction actually needed, but one is expected
        "bitcast"
typeConvertOp (Signed m) (Signed n)
    | m < n = "sext"
    | n < m = "trunc"
    | otherwise = shouldnt "no-op signed int conversion"
typeConvertOp (Signed m) (Floating n) = "sitofp"
typeConvertOp (Floating m) (Bits n) = "fptoui"
typeConvertOp (Floating m) (Signed n) = "fptosi"
typeConvertOp (Floating m) (Floating n)
    | m < n = "fpext"
    | n < m = "fptrunc"
    | otherwise = shouldnt "no-op floating point conversion"
typeConvertOp (Func _ _) CPointer = "inttoptr"
typeConvertOp repIn toTy =
    shouldnt $ "Don't know how to convert from " ++ show repIn
                 ++ " to " ++ show toTy


-- | Generate code to copy a structure, given a tagged pointer, the tag, the
-- size of the structure, and the variable to write the new tagged pointer into.
duplicateStruct :: PrimArg -> PrimArg -> PrimArg -> PrimArg -> LLVM ()
duplicateStruct struct startOffset size newStruct = do
    start <- case startOffset of
        ArgInt 0 _ -> return struct
        _ -> do
            (writeStart,readStart) <- freshTempArgs $ Representation Pointer
            writeLLVMCall "sub" [] [struct,startOffset,writeStart] Nothing
            return readStart
    (writeStartCPtr,readStartCPtr) <- freshTempArgs $ Representation CPointer
    llvmStart <- llvmArgument start
    typeConvert start writeStartCPtr
    (writeCPtr,readCPtr) <- freshTempArgs $ Representation CPointer
    marshalledCCall "wybe_malloc" [] [size,writeCPtr] ["int","pointer"] Nothing
    copyfn <- llvmMemcpyFn
    let nonvolatile = ArgInt 0 $ Representation $ Bits 1
    writeCCall copyfn [] [readCPtr,readStartCPtr,size,nonvolatile] Nothing
    (writePtr,readPtr) <- freshTempArgs $ Representation Pointer
    typeConvert readCPtr writePtr
    case startOffset of
        ArgInt 0 _ -> typeConvert readPtr newStruct
        _ -> writeLLVMCall "add" [] [readPtr,startOffset,newStruct] Nothing


-- | Split parameter list into separate list of input, output, out-by-reference,
-- and take-reference arguments, ignoring any phantom parameters.
partitionParams :: [PrimParam]
                -> LLVM ([PrimParam],[PrimParam],[PrimParam],[PrimParam])
partitionParams params = do
    partitionByFlow primParamFlow <$> lift (realParams params)


-- | Split argument list into separate list of inputs and outputs, after
-- eliminating phantom arguments.  Report an error if there are any
-- out-by-reference or take-reference arguments.
partitionArgs :: String -> [PrimArg] -> LLVM ([PrimArg],[PrimArg])
partitionArgs op args = do
    (ins,outs,oRefs,iRefs) <- partitionArgsWithRefs args
    unless (List.null oRefs) $ shouldnt $ "out-by-reference argument of " ++ op
    unless (List.null iRefs) $ shouldnt $ "take-reference argument of " ++ op
    return (ins,outs)


-- | Split the provided list of arguments into input, output, out-by-reference,
-- and take-reference arguments, after eliminating phantom arguments.
partitionArgsWithRefs :: [PrimArg]
                      -> LLVM ([PrimArg],[PrimArg],[PrimArg],[PrimArg])
partitionArgsWithRefs args = do
    realArgs <- lift $ filterM argIsReal args
    return $ partitionByFlow argFlowDirection realArgs


-- | Split list of pairs of argument and something else into separate lists of
-- input, output, out-by-reference, and take-reference arguments, after
-- eliminating phantom arguments.
partitionArgTuples :: String -> [(PrimArg,a)]
                   -> LLVM ([(PrimArg,a)],[(PrimArg,a)])
partitionArgTuples cfn args = do
    realArgs <- lift $ filterM (notM . argIsPhantom . fst) args
    let (ins,outs,oRefs,iRefs) =
            partitionByFlow (argFlowDirection . fst) realArgs
    unless (List.null oRefs)
     $ nyi $ "out-by-reference argument in call to C function " ++ cfn
    unless (List.null iRefs)
     $ nyi $ "take-reference argument in call to C function " ++ cfn
    return (ins,outs)


-- | Split the provided list into input, output, out-by-reference, and
-- take-reference arguments, given a function to determine the flow direction of
-- each element.  Out-by-reference means the flow is FlowOutByReference, which
-- denotes an argument that is notionally an output, but actually a reference
-- input that points to the location to write the output.  Take-reference
-- denotes a notional input argument that in actually produces the reference to
-- pass as an out-by-reference argument.  The key benefit of these flows comes
-- when the call with the out-by-reference argument precedes the one with the
-- take-reference argument (ie, the former notionally produces the value to use
-- in the latter):  if no other dependency forces this order of execution,
-- making these out-by-reference and take-reference allows us to swap their
-- order, potentially allowing last call optimisation.  The LastCallAnalysis
-- module contains the analysis and transformation introducing these flows.
partitionByFlow :: (a -> PrimFlow) -> [a] -> ([a],[a],[a],[a])
partitionByFlow fn lst =
    (List.filter ((==FlowIn)  . fn) lst,
     List.filter ((==FlowOut) . fn) lst,
     List.filter ((==FlowOutByReference) . fn) lst,
     List.filter ((==FlowTakeReference) . fn) lst)


----------------------------------------------------------------------------
-- The LLVM Monad and LLVM code generation and manipulation               --
----------------------------------------------------------------------------


-- At least for now, we represent LLVM info as strings

-- | An LLVM type name, such as i8
type LLVMType = String

-- | An LLVM global name, such as a function, variable or constant name, which must
--   begin with @; or an LLVM local variable name, which must begin with %; or an LLVM
--   constant value.
type LLVMName = String

-- | An LLVM value (constant or LLVMName), preceded by and LLVMType
type LLVMArg = String

-- | Information we collect about external functions we call in a module, so we
-- can declare them.
type ExternSpec = (LLVMName, [TypeSpec], [TypeSpec])

-- | Information needed to specify one constant value, giving the representation
-- to be stored and the (constant) value itself.
type ConstSpec = (PrimArg,TypeRepresentation)


-- | The LLVM State monad
data LLVMState = LLVMState {
        fileHandle :: Handle,       -- ^ The file handle we're writing to
        tmpCounter :: Int,          -- ^ Next temp var to make for current proc
        labelCounter :: Int,        -- ^ Next label number to use
        allStrings :: Set String,   -- ^ String constants appearing in module
        allExterns :: Set ExternSpec, -- ^ Extern declarations needed by module
        varDefRenaming :: Set PrimVarName,
                                    -- ^ Vars to rename on definition
        varUseRenaming :: Map PrimVarName LLVMName,
                                    -- ^ New action for some variables to read
        stringConstants :: Map String Ident,
                                    -- ^ local name given to string constants
        deferredCall :: Maybe (ProcSpec, [PrimArg], [PrimArg], [PrimArg]),
                                    -- ^ Wybe proc call deferred for
                                    -- out-by-reference arg, with in, out, and
                                    -- out-by-ref args
        takeRefVars :: Map PrimVarName (PrimArg,TypeSpec)
                                    -- ^ arg to read each take-reference ptr,
                                    -- plus the type of the original variable
}


-- | Set up LLVM monad to translate a module into the given file handle
initLLVMState :: Handle -> LLVMState
initLLVMState h = LLVMState h 0 0 Set.empty Set.empty Set.empty
                     Map.empty Map.empty Nothing Map.empty


-- | Reset the LLVM monad in preparation for translating a proc definition with
-- the specified temp counter.
initialiseLLVMForProc :: Int -> LLVM ()
initialiseLLVMForProc tmpCount = do
    modify $ \s -> s { tmpCounter = tmpCount
                     , labelCounter = 0
                     , varDefRenaming = Set.empty
                     , varUseRenaming = Map.empty
                     , deferredCall = Nothing
                     , takeRefVars = Map.empty
                     }


type LLVM = StateT LLVMState Compiler


-- | Apply some function to (access some member of) the current module from
-- within the LLVM monad.
llvmGetModule :: (Module -> a) -> LLVM a
llvmGetModule fn = lift $ getModule fn


-- | Write a string followed by a newline to the current LLVM output file handle
llvmPutStrLn :: String -> LLVM ()
llvmPutStrLn str = do
    logLLVM $ "EMIT: " ++ str
    h <- gets fileHandle
    liftIO $ hPutStrLn h str


-- | Write an indented string to the current LLVM output file handle.
llvmPutStrLnIndented :: String -> LLVM ()
llvmPutStrLnIndented str = llvmPutStrLn $ "  " ++ str


-- | Write a blank line to the current LLVM output file handle
llvmBlankLine :: LLVM ()
llvmBlankLine = llvmPutStrLn ""


-- | Return labels made unique by adding the next label suffix
freshLables :: [String] -> LLVM [String]
freshLables bases = do
    nxt <- gets labelCounter
    modify $ \s -> s {labelCounter = nxt+1}
    return $ List.map (++show nxt) bases


-- |Return a fresh prim variable name.
makeTemp :: LLVM PrimVarName
makeTemp = do
    ctr <- gets tmpCounter
    modify (\s -> s { tmpCounter = ctr + 1 })
    return $ PrimVarName (mkTempName ctr) 0


-- |Return a pair of PrimArgs to write and read, respectively, a fresh temp
-- variable of the specified type, along with the variable name.
freshTempArgs :: TypeSpec -> LLVM (PrimArg, PrimArg)
freshTempArgs ty = do
    tmp <- makeTemp
    let writeArg = ArgVar tmp ty FlowOut Ordinary False
    let readArg = ArgVar tmp ty FlowIn Ordinary True
    return (writeArg,readArg)


-- | Set the set of variables that need to be renamed to convert to SSA.
-- LPVM is a (dynamic) single assignment language, but LLVM demands static
-- single assignment.  We generate LPVM that is in SSA form, except for output
-- parameters, so here we rename all output parameters as they are assigned,
-- and then use the new names when we return the outputs.
setRenaming :: Set PrimVarName -> LLVM ()
setRenaming vars = modify $ \s -> s { varDefRenaming = vars }


-- | Replace the specified variable with the specified new value in all
-- following code.
renameVariable :: PrimVarName -> LLVMName -> LLVM ()
renameVariable var val =
    modify $ \s -> s { varUseRenaming = Map.insert var val $ varUseRenaming s }


-- | The LLVM name for a variable we are about to assign.  If this is one of the
-- output parameters, rename it, otherwise leave it alone, and in either case,
-- transform it to an LLVM local variable name.
varToWrite :: PrimVarName -> LLVM LLVMName
varToWrite v = do
    mustRename <- Set.member v <$> gets varDefRenaming
    if mustRename then do
        tmp <- llvmLocalName <$> makeTemp
        renameVariable v tmp
        return tmp
    else return $ llvmLocalName v


-- | The LLVM name for a variable we are about to read.
varToRead :: PrimVarName -> LLVM LLVMName
varToRead v = do
    renaming <- gets varUseRenaming
    return $ fromMaybe (llvmLocalName v) $ Map.lookup v renaming


----------------------------------------------------------------------------
-- Handling deferred calls and FlowOutByReference
--
-- This module handles FlowOutByReference and FlowTakeReference arguments as
-- follows.  First, Wybe calls with any FlowOutByReference arguments are
-- deferred, allowing following instructions with FlowTakeReference arguments to
-- be handled first.  Before any other instruction without a FlowTakeReference
-- argument is handled (or at the end of the proc body), any deferred
-- instruction is generated, as described below.
--
-- An instruction with a FlowTakeReference argument is transformed into an
-- instruction that stores the address the instruction would write the value
-- into, were it not FlowTakeReference, in a fresh temp variable, that is then
-- associated with that argument variable.
--
-- When a deferred call with a FlowOutByReference argument is generated, we
-- first check whether any temp variable has previously been associated with it
-- when handling a FlowTakeReference argument.  If not, we create such a
-- variable and generate an alloca instruction to assign the variable.  Then we
-- generate the call as usual, except that we pass the temp variable as input to
-- the call in place of the FlowOutByReference argument.  Following the call,
-- for each temp variable that was not previously assigned for a
-- FlowTakeReference instruction, we generate an instruction to load the
-- variable from the associated temp variable.
--
-- FlowOutByReference arguments appear in two contexts:  in what will become a
-- tail call after the following instructions with FlowTakeReference arguments,
-- and in other calls to the same proc.  In the latter case, it is necessary to
-- create a (stack) memory location to hold the output of the call, and then to
-- load the variable with the value produced.  In the former case, this is not
-- necessary, because the procedure never actually uses the value of the
-- FlowOutByReference variable.
--
----------------------------------------------------------------------------


-- | Record the specified instruction to be emitted later, after any
-- instructions with FlowTakeReference instructions have been handled.
deferCall :: ProcSpec -> [PrimArg] -> [PrimArg] -> [PrimArg] -> LLVM ()
deferCall wybeProc ins outs oRefs = do
    logLLVM $ "deferring call to " ++ show wybeProc
            ++ " with out-by-reference argument(s): " ++ show oRefs
    currDeferred <- gets deferredCall
    unless (isNothing currDeferred)
     $ shouldnt "deferring a call when one is already deferred"
    modify $ \s -> s{ deferredCall = Just (wybeProc, ins, outs, oRefs) }


-- | Record llvar as the llvm variable that holds the pointer to the value to
-- write to the FlowTakeReference variable takeRef when we see its
-- FlowOutByReference use.
addTakeRefPointer :: PrimVarName -> PrimArg -> TypeSpec -> LLVM ()
addTakeRefPointer takeRefVar readPtrArg ty = do
    logLLVM $ "Recording take-ref pointer " ++ show readPtrArg
            ++ " as replacement for output to " ++ show takeRefVar
            ++ ":" ++ show ty
    modify $ \s -> s{ takeRefVars =
                        Map.insert takeRefVar (readPtrArg,ty) $ takeRefVars s }


-- | Emit the deferred instruction, if there is one.  If not, do nothing.  This
-- must be done before handling every instruction other than one that has a
-- FlowTakeReference argument.
releaseDeferredCall :: LLVM ()
releaseDeferredCall = do
    deferred <- gets deferredCall
    case deferred of
        Nothing -> return ()
        Just (wybeProc, ins, outs, oRefs) -> do
            logLLVM $ "releasing deferred call to " ++ show wybeProc
            (refIns,old) <- mapAndUnzipM convertOutByRefArg oRefs
            takeRefs <- gets takeRefVars
            logLLVM $ "take-ref pointers = " ++ show takeRefs
            logLLVM $ "new ref args: " ++ show refIns ++ "; old = " ++ show old
            let allOld = and old
            let tailFlag = if allOld then "musttail " else ""
            writeActualCall wybeProc (ins++refIns) outs tailFlag
            unless allOld $ forM_ refIns $ \oRef -> do
                let oVar = argVar "in releaseDeferredCall" oRef
                (ptrArg,ty) <-
                    trustFromJust "TakeReference pointer variable lost!"
                    . Map.lookup oVar <$> gets takeRefVars
                let byRefArg = setArgFlow FlowOut oRef
                llvmLoad ptrArg byRefArg
            modify $ \s -> s{ deferredCall = Nothing, takeRefVars = Map.empty }


-- | Convert a FlowOutByeReference argument into an input CPointer arg.  If
-- we've already created a variable for the pointer, use that, otherwise alloca
-- space for the value and return an argument holding a pointer to it.  Also
-- return a Boolean indicating whether the variable was already created.
convertOutByRefArg :: PrimArg -> LLVM (PrimArg,Bool)
convertOutByRefArg ArgVar{argVarName=name, argVarType=ty,
                        argVarFlow=FlowOutByReference} = do
    maybePtrArg <- Map.lookup name <$> gets takeRefVars
    case maybePtrArg of
        Just (ptrArg,_) -> return (ptrArg,True)
        Nothing -> do
            (writeArg,readArg) <- freshTempArgs $ Representation CPointer
            llvmStoreResult [writeArg]
                $ "alloca ptr align " ++ show wordSizeBytes
            addTakeRefPointer name readArg ty
            return (readArg,False)
convertOutByRefArg other =
    shouldnt $ "Expected out-by-reference argument: " ++ show other



----------------------------------------------------------------------------
-- Formatting for LLVM                                                    --
----------------------------------------------------------------------------

-- | The LLVM name for a Wybe proc.
llvmProcName :: ProcSpec -> LLVMName
llvmProcName pspec = llvmGlobalName $ show pspec


-- | Make a suitable LLVM name for a global variable or constant.  We prefix it
-- with @, enclose the rest in quotes, and escape any special characters.
llvmGlobalName :: String -> LLVMName
llvmGlobalName s = '@' : show s


-- | Produce a suitable LLVM global name based on a GlobalInfo
llvmGlobalInfoName :: GlobalInfo -> LLVM LLVMName
llvmGlobalInfoName (GlobalResource res) =
     llvmGlobalName . fst <$> llvmResource res
llvmGlobalInfoName (GlobalVariable var) = return $ llvmGlobalName var


-- | Make a suitable LLVM name for a foreign (e.g., C) function.  We just prefix
-- it with @, with no escaping of any characters.
llvmForeignName :: String -> LLVMName
llvmForeignName s = '@' : s


-- | Make a suitable LLVM name for a local variable.  We prefix it
-- with %, enclose the rest in quotes, and escape any special characters.
llvmLocalName :: PrimVarName -> LLVMName
llvmLocalName varName =
    "%\"" ++ show varName ++ "\""


-- | Make an LLVM reference to the specified label.
llvmLableName :: String -> String
llvmLableName varName = "label %\"" ++ varName ++ "\""


-- | Format a string as an LLVM string; the Bool indicates whether to add
-- a zero terminator.
showLLVMString :: String -> Bool -> String
showLLVMString str zeroTerminator =
    let suffix = if zeroTerminator then "\0" else ""
        len = length str + length suffix
    in "[ " ++ show len ++ " x i8 ] c\""
        ++ concatMap showLLVMChar str ++ concatMap showLLVMChar suffix ++ "\""

-- | Format a single character as a character in an LLVM string.
showLLVMChar :: Char -> String
showLLVMChar char
    | char == '\\'               = "\\\\"
    | char == '"'                = "\\22"
    | char >= ' ' && char <= '~' = [char]
    | otherwise                  =
        let ascii = fromEnum char
            hexChar i = if i < 10 then toEnum $ fromEnum '0' + i
                        else toEnum $ fromEnum 'A' + i - 10
        in ['\\', hexChar (ascii `div` 16), hexChar (ascii `mod` 16)]


-- | The name of the LLVM memcpy intrinsic that applies to 2 CPointers and one
-- Wybe int type argument (there's also a Boolean flag).
llvmMemcpyFn :: LLVM String
llvmMemcpyFn = ("llvm.memcpy.p0.p0." ++) . llvmTypeRep <$> typeRep intType


----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the LLVM monad.
logLLVM :: String -> LLVM ()
logLLVM = lift . logMsg LLVM


-- | Log with a wrapping line of replicated characters above and below.
logWrapWith :: Char -> String -> Compiler ()
logWrapWith ch s = do
    logMsg LLVM (replicate 65 ch)
    logMsg LLVM s
    logMsg LLVM (replicate 65 ch)