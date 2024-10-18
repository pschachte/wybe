--  File     : LLVM.hs
--  Author   : Peter Schachte, based on work by Ashutosh Rishi Ranjan
--  Purpose  : Generate LLVM code from LPVM form
--  Copyright: (c) 2024 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module LLVM ( llvmMapBinop, llvmMapUnop, writeLLVM, BinOpInfo(..) ) where

import           AST
import           ASTShow
import           Resources
import           BinaryFactory
import           Config
import           Options
import           Version
import           CConfig
import           Snippets
import           Util                            ((|||), showArguments, sameLength)
import           System.IO
import           Data.Char                       (isAlphaNum)
import           Data.Set                        as Set
import qualified Data.Map                        as Map
import           Data.Map                        (Map)
import           Data.List                       as List
import           Data.List.Extra
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
import Distribution.TestSuite (TestInstance(name))


-- BEGIN MAJOR DOC
-- 
-- # Generating LLVM code
-- 
-- We generate a `.ll` text file directly for each Wybe `.wybe` file, compiling
-- this as necessary to build `.o`, `.bc` `.s`, or executable files.  For each
-- generated `.ll` file, we produce the following, in order:
-- 
--  * **Prologue** — contains an introductory comment and any configuration info
--    needed for LLVM.
--
--  * **Constants** — LLVM definitions of the manifest constants used in this
--    module; mostly used for strings.
--
--  * **Global variables** —  LLVM declarations of the global variables used to
--    implement the resources defined in this module.
--
--  * **Externs** — Extern declarations for all symbols used, but not defined,
--    in this module; this includes imported Wybe procedures, C functions,  and
--    global variables.
--
--  * **Definitions** — Definitions of the procs of this module.
--
--  * **Exports** — Everything needed by the Wybe compiler to compile users of
--    this module; currently this is represented as a serialisation of the
--    Module data structure, placed in the LLVM section.
--
-- END MAJOR DOC



----------------------------------------------------------------------------
-- Instruction maps
--
-- What we need to know about LLVM instructions
----------------------------------------------------------------------------


-- | How to determine the sizes of the inputs of a binary llvm instruction. The
-- compiler handles arguments of different sizes, which may be different from
-- the output size.  Both arguments in the generated instruction must have the
-- same size.  If the specified LLVMArgSize of an instruction is SizeFromOutput,
-- then both arguments must be converted to the type of the output before the
-- instruction.  If it is SizeFromInputs, then both arguments must be converted
-- to the type of the larger input argument.  For SizeFromLargest, both inputs
-- must be converted to the type of the largest of the inputs and output, and
-- the result must be converted (truncated if necessary) to the expected output
-- type.
data LLVMArgSize = SizeFromOutput | SizeFromInputs | SizeFromLargest
    deriving Eq


-- | Determine the type representations of the inputs of a binary LLVM
-- instruction, given the LLVMArgSize policy, the representation of the output,
-- and the representations of the inputs.  These instructions require both
-- arguments to be the same size.
resolveLLVMArgType :: LLVMArgSize -> TypeRepresentation -> [TypeRepresentation]
                   -> TypeRepresentation
resolveLLVMArgType SizeFromOutput outTy _ = outTy
resolveLLVMArgType SizeFromInputs _ inTys = List.foldr1 maxSizeRep inTys
resolveLLVMArgType SizeFromLargest outTy inTys =
    List.foldr maxSizeRep outTy inTys


-- | Pick the larger of two compatible types; an error if the types are not
-- compatible.
maxSizeRep :: TypeRepresentation -> TypeRepresentation -> TypeRepresentation
maxSizeRep (Bits sz1) (Bits sz2)         = Bits (max sz1 sz2)
maxSizeRep (Bits sz1) (Signed sz2)       = Bits (max sz1 sz2)
maxSizeRep (Bits sz) Pointer             = Pointer
maxSizeRep Pointer (Bits sz)             = Pointer
maxSizeRep (Signed sz1) (Bits sz2)       = Bits (max sz1 sz2)
maxSizeRep (Signed sz1) (Signed sz2)     = Signed (max sz1 sz2)
maxSizeRep (Signed sz) Pointer           = Pointer
maxSizeRep Pointer (Signed sz)           = Pointer
maxSizeRep (Floating sz1) (Floating sz2) = Floating (max sz1 sz2)
maxSizeRep rep1 rep2 | rep1 == rep2      = rep1
maxSizeRep rep1 rep2 =
    shouldnt $ "Generating LLVM instruction with incompatible types "
             ++ show rep1 ++ " and " ++ show rep2


data BinOpInfo = BinOpInfo {
    binOpInstr :: String,           -- ^ full llvm instruction
    binOpFamily :: TypeFamily,      -- ^ Type family of inputs
    binOpArgSize :: LLVMArgSize,    -- ^ How to convert arguments and result
    binOpResultFn :: TypeRepresentation -> TypeRepresentation
                                    -- ^ Determine result representation from
                                    --   (common) argument representation
}

-- | Create a mapping for a binary instruction given its argument family, how to
-- convert the arguments, and whether the operation returns a Boolean (otherwise
-- it returns the same type as the arguments).
binaryInstr :: String -> TypeFamily -> LLVMArgSize -> Bool -> (String,BinOpInfo)
binaryInstr instr family argSize toBool =
    (instr, BinOpInfo (unwords $ wordsBy (=='_') instr) family argSize
                $ if toBool then const $ Bits 1 else id)


-- | A map of arithmetic binary operations supported by LLVM to the info we need
-- to know to compile calls to them.
llvmMapBinop :: Map Ident BinOpInfo
llvmMapBinop =
    Map.fromList [
            -- Integer arithmetic
            binaryInstr "add"       IntFamily   SizeFromLargest False,
            binaryInstr "sub"       IntFamily   SizeFromLargest False,
            binaryInstr "mul"       IntFamily   SizeFromLargest False,
            binaryInstr "udiv"      IntFamily   SizeFromLargest False,
            binaryInstr "sdiv"      IntFamily   SizeFromLargest False,
            binaryInstr "urem"      IntFamily   SizeFromLargest False,
            binaryInstr "srem"      IntFamily   SizeFromLargest False,
            -- Integer comparisions
            binaryInstr "icmp_eq"   IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_ne"   IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_ugt"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_uge"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_ult"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_ule"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_sgt"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_sge"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_slt"  IntFamily   SizeFromInputs  True,
            binaryInstr "icmp_sle"  IntFamily   SizeFromInputs  True,
            -- Bitwise operations
            binaryInstr "shl"       IntFamily   SizeFromOutput  False,
            binaryInstr "lshr"      IntFamily   SizeFromInputs  False,
            binaryInstr "ashr"      IntFamily   SizeFromInputs  False,
            binaryInstr "or"        IntFamily   SizeFromOutput  False,
            binaryInstr "and"       IntFamily   SizeFromOutput  False,
            binaryInstr "xor"       IntFamily   SizeFromOutput  False,

            -- Floating point arithmetic
            binaryInstr "fadd"      FloatFamily SizeFromLargest False,
            binaryInstr "fsub"      FloatFamily SizeFromLargest False,
            binaryInstr "fmul"      FloatFamily SizeFromLargest False,
            binaryInstr "fdiv"      FloatFamily SizeFromLargest False,
            binaryInstr "frem"      FloatFamily SizeFromLargest False,
            -- Floating point comparisions
            binaryInstr "fcmp_false" FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_oeq"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_one"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_olt"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ole"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ogt"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_oge"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ord"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ueq"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_une"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ult"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ule"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_ugt"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_uge"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_uno"  FloatFamily SizeFromInputs  True,
            binaryInstr "fcmp_true" FloatFamily SizeFromInputs  True
           ]


-- | Create a mapping for a unary instruction given its input and output
-- argument families.
unaryInstr :: String -> TypeFamily -> TypeFamily
           -> (String,(TypeFamily,TypeFamily))
unaryInstr instr inFamily outFamily = (instr, (inFamily,outFamily))


-- | A map of unary llvm operations wrapped in the 'Codegen' module.
llvmMapUnop :: Map String (TypeFamily, TypeFamily)
llvmMapUnop =
    Map.fromList [
            unaryInstr "uitofp" IntFamily   FloatFamily,
            unaryInstr "sitofp" IntFamily   FloatFamily,
            unaryInstr "fptoui" FloatFamily IntFamily,
            unaryInstr "fptosi" FloatFamily IntFamily
           ]


----------------------------------------------------------------------------
-- Generating LLVM for a module
----------------------------------------------------------------------------

-- | Generate LLVM code for the specified module and all its submodules, based
-- on its LPVM code, and write it to the specified file handle.  The specified
-- ModSpec is the "root" module of the file.
writeLLVM :: Handle -> ModSpec -> Bool -> Bool -> Compiler ()
writeLLVM handle modSpec withLPVM recursive = do
    allMods <-
        if recursive
        then (modSpec:) <$> sameOriginModules modSpec
        else return [modSpec]
    logMsg LLVM $ "*** Generating LLVM for module(s) " ++ showModSpecs allMods
    mod <- gets $ trustFromJust "writeLLVM of unknown module"
            <$> Map.lookup modSpec . modules
    logWrapWith '-' $ show mod
    reenterModule modSpec
    flip execStateT (initLLVMState handle) $ do
        forEachModule allMods preScanProcs
        writeAssemblyPrologue
        writeAssemblyConstants
        writeAssemblyExterns
        forEachModule allMods writeAssemblyGlobals
        forEachModule allMods writeAssemblyProcs
        when withLPVM $ do
            writeAssemblyExports
    reexitModule
    logMsg LLVM $ "*** Finished generating LLVM for " ++ showModSpecs allMods


-- | Execute the specified monadic computation in each of the specified modules.
forEachModule :: [ModSpec] -> LLVM () -> LLVM ()
forEachModule mods code =
    forM_ mods $ \m -> do
        lift $ reenterModule m
        code
        lift reexitModule


----------------------------------------------------------------------------
-- Scanning the module in preparation
----------------------------------------------------------------------------

-- | Scan proc bodies to find and record whatever we need to later produce the
-- llvm assembly code for the current module.  Currently we collect string
-- constants and extern declarations for foreign procs and imported Wybe procs
-- used by the module.
preScanProcs :: LLVM ()
preScanProcs = do
    thisMod <- llvmGetModule modSpec
    mod <- fromMaybe thisMod <$> llvmGetModule modRootModSpec
    procss <- lift $ getModuleImplementationField (Map.elems . modProcs)
    logLLVM $ "preScanProcs: "
                ++ intercalate ", " (concatMap (List.map (show.procName)) procss)
    let bodies = concatMap (concatMap allProcBodies) procss
    mapM_ (mapLPVMBodyM (recordExtern mod) prescanArg) bodies


-- | What's needed to identify a manifest constant string in generated LLVM
-- code.  Wybe string constants (usually) consist of a size and a pointer to a C
-- string, while C strings are C pointers to 0-terminated packed arrays of
-- bytes.
data StaticConstSpec = CStringSpec String
                     | WybeStringSpec String
                     | ClosureSpec ProcSpec [PrimArg]
    deriving (Eq,Ord)

instance Show StaticConstSpec where
    show (CStringSpec str) = 'c' : show str
    show (WybeStringSpec str) = show str
    show (ClosureSpec pspec args) = show pspec ++ showArguments args


-- | If the specified PrimArg is a string constant or closure with only constant
-- arguments, add it to the set.  For Wybe strings, add both the Wybe string and
-- the C string, since the Wybe string constant refers to the C string.
prescanArg :: PrimArg -> LLVM ()
prescanArg (ArgString str WybeString _) = do
    recordConst $ WybeStringSpec str
    recordConst $ CStringSpec str
prescanArg (ArgString str CString _) =
    recordConst $ CStringSpec str
prescanArg (ArgClosure pspec args _) = do
    args' <- neededFreeArgs pspec args
    if all argIsConst args'
    then
        recordConst $ ClosureSpec pspec args
    else
        recordExternSpec externAlloc
prescanArg _ = return ()


-- | Record that the specified constant needs to be declared in this LLVM module
recordConst :: StaticConstSpec -> LLVM ()
recordConst spec =
    modify $ \s -> s {allConsts=Set.insert spec $ allConsts s}



-- | If needed, add an extern declaration for a prim to the set.
recordExtern :: ModSpec -> Prim -> LLVM ()
recordExtern mod (PrimCall _ pspec _ args _) = do
    logLLVM $ "Check if " ++ show pspec ++ " is extern to " ++ showModSpec mod
    unless (mod /= [] && mod `isPrefixOf` procSpecMod pspec) $ do
        logLLVM " ... it is"
        let (nm,cc) = llvmProcName pspec
        recordExternFn cc nm args
recordExtern _ PrimHigher{} = return ()
recordExtern _ (PrimForeign "llvm" _ _ _) = return ()
recordExtern _ (PrimForeign "lpvm" "alloc" _ _) =
    recordExternSpec externAlloc
recordExtern mod (PrimForeign "lpvm" "load" _ [ArgGlobal glob ty,_]) =
    recordExternVar mod glob ty
recordExtern mod (PrimForeign "lpvm" "store" _ [_,ArgGlobal glob ty]) =
    recordExternVar mod glob ty
recordExtern _ (PrimForeign "lpvm" "mutate" _ (_:_:destr:_)) =
    case destr of
        ArgInt 1 _ -> return ()
        _ -> recordExternSpec externAlloc
recordExtern _ (PrimForeign "lpvm" _ _ _) = return ()
recordExtern _ (PrimForeign "c" name _ args) =
    recordExternFn "ccc" (llvmForeignName name) args
recordExtern _ (PrimForeign other name _ args) =
    shouldnt $ "Unknown foreign language " ++ other


recordExternSpec :: ExternSpec -> LLVM ()
recordExternSpec spec = do
    logLLVM $ "Recording external " ++ show spec
    name <- externID spec
    modify $ \s -> s {allExterns=Map.insert name spec $ allExterns s}


externCFunction :: String -> [String] -> String -> ExternSpec
externCFunction name argTypes resultType =
    let convert t = Representation
                    $ trustFromJust ("unknown C type " ++ t)
                    $ cTypeRepresentation t
        typeReps = List.map convert argTypes
        resultRep = convert resultType
    in ExternFunction "ccc" name typeReps [resultRep]


-- | An extern spec for the wybe_malloc function.
externAlloc :: ExternSpec
externAlloc = externCFunction (llvmForeignName mallocFn) ["int"] "pointer"


-- | Record the fact that the named function is an external function using the
-- specified calling convention and taking the specified (input and output)
-- argument types.
recordExternFn :: String -> LLVMName -> [PrimArg] -> LLVM ()
recordExternFn cc fName args =
    let (ins,outs,oRefs,iRefs) = partitionByFlow argFlowDirection args
        extern = ExternFunction cc fName
                 ((argType <$> ins) ++ (Representation CPointer <$ oRefs))
                 (argType <$> outs)
    in if List.null iRefs
        then recordExternSpec extern
        else shouldnt $ "Function " ++ fName
                ++ " has TakeReference parameter(s) " ++ show iRefs


-- | Insert the fact that the named function is an external function with the
-- specified argument types in the provided set, returning the resulting set.
-- Only add the spec if it's for an external global var.
recordExternVar :: ModSpec -> GlobalInfo -> TypeSpec -> LLVM ()
recordExternVar mspec global ty =
    unless (globalIsLocal mspec global)
        $ recordExternSpec (ExternVariable global ty)


-- | Test if the GlobalInfo specifies a global variable defined in the current
-- file, determined by whether is from (a submodule of) the current module.
globalIsLocal :: ModSpec -> GlobalInfo -> Bool
globalIsLocal mspec (GlobalResource (ResourceSpec mod _)) =
    notNull mspec && mspec `isPrefixOf` mod
globalIsLocal _ _ = False


----------------------------------------------------------------------------
-- Writing the prologue
----------------------------------------------------------------------------

-- | Write out some boilerplate at the beginning of a generated .ll file.
-- Included are a comment identifying the source of the file and the information
-- required for the file to be compilable.
writeAssemblyPrologue :: LLVM ()
writeAssemblyPrologue = do
    logLLVM "writeAssemblyPrologue"
    mod <- llvmGetModule modSpec
    srcFile <- llvmGetModule modOrigin
    llvmPutStrLn $ ";; FILE GENERATED BY wybemk "
                ++ Version.version
                ++ " -- see https://github.com/pschachte/wybe"
    llvmPutStrLn $ "; ModuleID = '" ++ showModSpec mod ++ "'"
    llvmBlankLine
    llvmPutStrLn $ "source_filename = \"" ++ srcFile ++ "\""
    llvmPutStrLn $ "target triple   = \"" ++ Version.defaultTriple ++ "\""
    llvmBlankLine
    return ()


----------------------------------------------------------------------------
-- Writing the constant definitions
----------------------------------------------------------------------------

-- | Write out definitions of manifest constants used in generated code for this
-- module.  This assumes that sets are converted to lists such that the CStrings
-- appear before the WybeStrings.
writeAssemblyConstants :: LLVM ()
writeAssemblyConstants = do
    logLLVM "writeAssemblyConstants"
    strings <- gets $ Set.toList . allConsts
    zipWithM_ writeConstDeclaration strings [0..]
    llvmBlankLine


-- | Write out a declaration for a string and record its name.  This code
-- assumes that the CString that a WybeString refers to has already been
-- declared and recorded.  This will happen because sets are sorted
-- alphabetically, and CString comes before WybeString.
writeConstDeclaration :: StaticConstSpec -> Int -> LLVM ()
writeConstDeclaration spec@(WybeStringSpec str) n = do
    let stringName = specialName2 "string" $ show n
    modify $ \s -> s { constNames=Map.insert spec stringName
                                       $ constNames s}
    textName <- lookupConstant $ CStringSpec str
    declareStructConstant stringName
        [ (ArgInt (fromIntegral $ length str) (Representation $ Bits wordSize)
          , Bits wordSize)
        , (ArgGlobal (GlobalVariable textName) (Representation CPointer)
          , Pointer)]
        Nothing
writeConstDeclaration spec@(CStringSpec str) n = do
    let textName = specialName2 "cstring" $ show n
    modify $ \s -> s { constNames=Map.insert spec textName
                                       $ constNames s}
    declareStringConstant textName str Nothing
writeConstDeclaration spec@(ClosureSpec pspec args) n = do
    let closureName = specialName2 "closure" $ show n
    modify $ \s -> s { constNames=Map.insert spec closureName $ constNames s}
    let pname = show pspec
    argReps <- mapM argTypeRep args
    declareStructConstant closureName
        ((ArgGlobal (GlobalVariable pname) (Representation CPointer), CPointer)
         : zip args argReps)
        Nothing


-- | Find the global constant that holds the value of the specified string
-- constant.
lookupConstant :: StaticConstSpec -> LLVM Ident
lookupConstant spec =
    trustFromJust ("lookupConstant " ++ show spec) <$> tryLookupConstant spec


-- | Find the global constant that holds the value of the specified string
-- constant.
tryLookupConstant :: StaticConstSpec -> LLVM (Maybe Ident)
tryLookupConstant spec =
    gets $ Map.lookup spec . constNames


----------------------------------------------------------------------------
-- Writing the global variable definitions
----------------------------------------------------------------------------

-- | Write out definitions of global variables to implement the resources of
-- this module.
writeAssemblyGlobals :: LLVM ()
writeAssemblyGlobals = do
    logLLVM "writeAssemblyGlobals"
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
    logLLVM "writeAssemblyExterns"
    copyFn <- llvmGlobalName <$> llvmMemcpyFn
    let spec = ExternFunction "ccc" copyFn
                (Representation <$> [CPointer,CPointer,Bits wordSize,Bits 1]) []
    externs <- Map.elems <$> gets allExterns
    mapM_ declareExtern externs
    declareExtern spec


declareExtern :: ExternSpec -> LLVM ()
declareExtern (ExternFunction cc name ins outs) = do
    outs' <- lift $ filterM (notM . typeIsPhantom) outs
    ins' <- lift $ filterM (notM . typeIsPhantom) ins
    outTy <- llvmReturnType outs'
    argTypes <- (llvmTypeRep <$>) <$> mapM typeRep ins'
    llvmPutStrLn $ "declare external " ++ cc ++ " "
                  ++ outTy ++ " " ++ name ++ "("
                  ++ intercalate ", " argTypes ++ ")"
declareExtern (ExternVariable glob ty) = do
    rep <- typeRep ty
    unless (repIsPhantom rep) $ do
        name <- llvmGlobalInfoName glob
        llvmPutStrLn $ name ++ " = external global " ++ llvmTypeRep rep


----------------------------------------------------------------------------
-- Writing procedure definitions
----------------------------------------------------------------------------

-- | Generate and write out the LLVM code for all the procs defined in this
-- module.
writeAssemblyProcs :: LLVM ()
writeAssemblyProcs = do
    logLLVM "writeAssemblyProcs"
    mod <- llvmGetModule modSpec
    procs <- lift $ getModuleImplementationField
                    (concatMap (`zip` [0..]) . Map.elems . modProcs)
    mapM_ (uncurry writeProcLLVM) procs


-- | Generate and write out the LLVM code for the given proc with its proc
-- number and all its specialisations.
writeProcLLVM :: ProcDef -> Int -> LLVM ()
writeProcLLVM def procNum =
    case procImpln def of
        ProcDefPrim {procImplnProcSpec=pspec, procImplnProto=proto,
                     procImplnBody=body, procImplnSpeczBodies=specz} -> do
            (proto', body') <- if isClosureVariant $ procVariant def
                        then do
                            logLLVM $ "Compiling closure variant for proc "
                                        ++ showProcName (procName def) ++ ":"
                            let (p',b') = closeClosure proto body
                            logLLVM $ "Params: " ++ show p'
                            logLLVM $ "Body  : " ++ show b'
                            return (p',b')
                        else return (proto, body)
            let params = primProtoParams proto'
            let tmpCount = procTmpCount def
            -- XXX overriding procSpeczVersion should not be needed, but it is!
            writeProcSpeczLLVM pspec{procSpeczVersion=Set.empty}
                    tmpCount params body'
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


-- | Updates a PrimProto and ProcBody as though the Free Params are accessed
-- via the closure environment
closeClosure :: PrimProto -> ProcBody -> (PrimProto, ProcBody)
closeClosure proto@PrimProto{primProtoParams=params}
             body@ProcBody{bodyPrims=prims} =
    (proto{primProtoParams=envPrimParam:genericParams},
     body{bodyPrims=unpacker ++ inwardConverter ++ prims ++ outwardConverter})
  where
    (free, actualParams) = List.partition ((==Free) . primParamFlowType) params
    genericParams = [p {primParamType=AnyType
                       ,primParamName=genericVarName (primParamName p)}
                    | p <- actualParams]
    neededFree = List.filter (not . paramInfoUnneeded
                                  . primParamInfo) free
    unpacker = Unplaced <$>
                [ primAccess (ArgVar envParamName AnyType FlowIn Ordinary False)
                             (ArgInt (i * toInteger wordSizeBytes) intType)
                             (ArgInt (toInteger wordSize) intType)
                             (ArgInt 0 intType)
                             (ArgVar genName AnyType FlowOut Free False)
                | (i,PrimParam nm ty _ _ _) <- zip [1..] neededFree
                , let genName = genericVarName nm]
    inwardConverter = Unplaced <$>
                [ PrimForeign "llvm" "move" [] [
                    ArgVar (genericVarName nm) AnyType FlowIn Ordinary False,
                    ArgVar nm ty FlowOut Ordinary False]
                | PrimParam nm ty FlowIn _ _ <- actualParams ++ neededFree ]
    outwardConverter = Unplaced <$>
                [ PrimForeign "llvm" "move" [] [
                    ArgVar nm ty FlowIn Ordinary False,
                    ArgVar (genericVarName nm) AnyType FlowOut Ordinary False]
                | PrimParam nm ty FlowOut _ _ <- actualParams ]

-- | Create a name for the generic type version of a variable/parameter
genericVarName :: PrimVarName -> PrimVarName
genericVarName p@PrimVarName{primVarName=v} = p {primVarName="generic#" ++ v}


-- | Write out the LLVM code for a single LPVM proc specialisation (including no
-- specialisation), given the ProcSpec, temp variable count, parameter list, and
-- body.
writeProcSpeczLLVM :: ProcSpec -> Int -> [PrimParam] -> ProcBody -> LLVM ()
writeProcSpeczLLVM pspec tmpCount params body = do
    logLLVM $ "Generating LLVM for proc " ++ show pspec
    initialiseLLVMForProc tmpCount
    let (name,cc) = llvmProcName pspec
    (ins,outs,oRefs,iRefs) <- partitionParams params
    unless (List.null iRefs)
        $ nyi $ "take-reference parameter for proc " ++ show pspec
    setRenaming $ Set.fromList $ primParamName <$> outs
    returnType <- llvmReturnType $ List.map primParamType outs
    oRefParams <- mapM recordProcOutByRef oRefs
    llParams <- mapM llvmParameter $ ins ++ oRefParams
    llvmBlankLine
    llvmPutStrLn $
        "define external " ++ cc ++ " " ++ returnType ++ " "
            ++ name ++ "(" ++ intercalate ", " llParams ++ ")"
            ++ " {"
    writeAssemblyBody outs body
    llvmPutStrLn "}"



-- | Create an opaque pointer parameter for each out-by-reference parameter, and
-- record the correspondence, so we can translate assignments to the
-- out-by-reference parameter into a store through the opaque pointer.
recordProcOutByRef :: PrimParam -> LLVM PrimParam
recordProcOutByRef param@PrimParam{primParamName=p, primParamType=ty} = do
    tmp <- makeTemp
    let readCPtrArg = ArgVar tmp (Representation CPointer) FlowIn Ordinary True
    let actualParam = convertOutByRefParam param{primParamName=tmp}
    addOutByRefPointer p readCPtrArg ty
    return actualParam


-- | Generate and write out the LLVM code for an LPVM body
writeAssemblyBody :: [PrimParam] -> ProcBody -> LLVM ()
writeAssemblyBody outs ProcBody{bodyPrims=prims, bodyFork=fork} = do
    logLLVM $ "Generating LLVM body with outs " ++ show outs
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
                (Signed _, cases, dflt) -> writeAssemblySwitch outs v rep cases dflt
                (rep,_,_) -> shouldnt $ "Switching on " ++ show rep ++ " type "
                                ++ show ty


-- | Generate and write out an LLVM if-then-else (switch on an i1 value)
writeAssemblyIfElse :: [PrimParam] -> PrimVarName -> ProcBody -> ProcBody
                    -> LLVM ()
writeAssemblyIfElse outs v thn els = do
    releaseDeferredCall
    [thnlbl,elslbl] <- freshLables ["if.then.","if.else."]
    llvar <- varToRead v
    llvmPutStrLnIndented $ "br i1 " ++ llvar
                    ++ ", " ++ llvmLabelName thnlbl
                    ++ ", " ++ llvmLabelName elslbl
    llvmPutStrLn $ thnlbl ++ ":"
    writeAssemblyBody outs thn
    llvmPutStrLn $ elslbl ++ ":"
    writeAssemblyBody outs els


-- | Generate and write out an LLVM multi-way switch
writeAssemblySwitch :: [PrimParam] -> PrimVarName -> TypeRepresentation
                    -> [ProcBody] -> Maybe ProcBody -> LLVM ()
writeAssemblySwitch outs v rep cases dflt = do
    releaseDeferredCall
    let prefixes = ["case."++show n++".switch." | n <- [0..length cases-1]]
    (dfltLabel,numLabels) <- if isJust dflt
        then do
            (dfltLabel:numLabels) <- freshLables $ "default.switch.":prefixes
            return (dfltLabel,numLabels)
        else do
            labels <- freshLables prefixes
            return (last labels, labels) -- if no default, use last case
    let llType = llvmTypeRep rep
    llvar <- varToRead v
    logLLVM $ "Switch on " ++ llvar ++ " with cases " ++ show cases
    llvmPutStrLnIndented $ "switch " ++ makeLLVMArg llType llvar ++ ", "
        ++ llvmLabelName dfltLabel ++ " [\n    "
        ++ intercalate "\n    "
                [makeLLVMArg llType (show n) ++ ", " ++ llvmLabelName lbl
                | (lbl,n) <- zip numLabels [0..]]
        ++ " ]"
    zipWithM_
        (\lbl cs -> llvmPutStrLn (lbl ++ ":") >> writeAssemblyBody outs cs)
        numLabels cases
    case dflt of
        Nothing -> return ()
        Just dfltCode -> do
            llvmPutStrLn $ dfltLabel ++ ":"
            -- I don't think the Nothing case ever happens, but just in case...
            writeAssemblyBody outs dfltCode


----------------------------------------------------------------------------
-- Generating and emitting LLVM for a single LPVM Prim instruction
----------------------------------------------------------------------------


-- | Generate and write out the LLVM code for a single LPVM prim
writeAssemblyPrim :: Prim -> OptPos -> LLVM ()
writeAssemblyPrim instr@(PrimCall _ proc _ args _) pos = do
    releaseDeferredCall
    logLLVM $ "* Translating Wybe call " ++ show instr
    writeWybeCall proc args pos
writeAssemblyPrim instr@(PrimHigher _ fn _ args) pos = do
    releaseDeferredCall
    logLLVM $ "* Translating HO call " ++ show instr
    writeHOCall fn args pos
writeAssemblyPrim instr@(PrimForeign "llvm" op flags args) pos = do
    releaseDeferredCall
    logLLVM $ "* Translating LLVM instruction " ++ show instr
    writeLLVMCall op flags args pos
writeAssemblyPrim instr@(PrimForeign "lpvm" op flags args) pos = do
    -- Some of these must be handled before releasing deferred calls
    logLLVM $ "* Translating LPVM instruction " ++ show instr
    writeLPVMCall op flags args pos
writeAssemblyPrim instr@(PrimForeign "c" cfn flags args) pos = do
    releaseDeferredCall
    logLLVM $ "* Translating C call " ++ show instr
    writeCCall cfn flags args pos
writeAssemblyPrim instr@(PrimForeign lang op flags args) pos = do
    shouldnt $ "unknown foreign language " ++ lang
                ++ " in instruction " ++ show instr


-- | Generate a Wybe proc call instruction, or defer it if necessary.
writeWybeCall :: ProcSpec -> [PrimArg] -> OptPos -> LLVM ()
writeWybeCall wybeProc args pos = do
    (ins,outs,oRefs,iRefs) <- partitionArgsWithRefs args
    unless (List.null iRefs)
     $ shouldnt $ "Wybe call " ++ show wybeProc ++ " with take-reference arg"
    tailKind <- tailMarker False
    if List.null oRefs then
        writeActualCall wybeProc ins outs tailKind
    else
        deferCall wybeProc ins outs oRefs


-- | Generate a Wybe proc call instruction, or defer it if necessary.
writeHOCall :: PrimArg -> [PrimArg] -> OptPos -> LLVM ()
writeHOCall (ArgClosure pspec closed _) args pos = do
    -- NB:  this case doesn't seem to ever occur
    pspec' <- fromMaybe pspec <$> lift (maybeGetClosureOf pspec)
    logLLVM $ "Compiling HO call as first order call to " ++ show pspec'
              ++ " closed over " ++ show closed
    writeWybeCall pspec' (closed ++ args) pos
writeHOCall closure args pos = do
    (ins,outs,oRefs,iRefs) <- partitionArgsWithRefs $ closure:args
    unless (List.null oRefs && List.null iRefs)
        $ nyi $ "Higher order call with out-by-ref or take-ref argument "
                ++ show (PrimHigher 0 closure Pure args)
    allPhantoms <- and <$> lift (mapM argIsPhantom outs)
    let ty = argVarType closure
    unless (allPhantoms && not (isResourcefulHigherOrder ty)
                && modifierImpurity (higherTypeModifiers ty) <= Pure) $ do
        outTy <- llvmReturnType $ List.map argType outs
        (writeFnPtr,readFnPtr) <- freshTempArgs $ Representation CPointer
        llvmLoad closure writeFnPtr
        fnVar <- llvmValue readFnPtr
        argList <- llvmArgumentList ins
        prefix <- tailMarker False
        llvmAssignResults outs $
            prefix ++ "call fastcc " ++ outTy ++ " " ++ fnVar ++ argList


-- | Work out the appropriate prefix for a call:  tail, musttail, or nothing.
-- The input specifies whether this call is has had out-by-ref arguments
-- converted to input pointers.
tailMarker :: Bool -> LLVM String
tailMarker must = do
    didAlloca <- gets doesAlloca
    return $ case (didAlloca, must) of
        (True,_)      -> ""
        (False,True)  -> "musttail "
        (False,False) -> "tail "


-- | Actually generate a Wybe proc call.  tailKind indicates what degree of LLVM
-- tail call optimisation we want.
writeActualCall :: ProcSpec -> [PrimArg] -> [PrimArg] -> String -> LLVM ()
writeActualCall wybeProc ins outs tailKind = do
    params <- lift $ getPrimParams wybeProc
    (inPs,outPs,oRefPs,iRefPs) <- partitionParams params
    unless (List.null iRefPs)
      $ shouldnt $ "take-reference parameter(s) " ++ show iRefPs
    let allInPs = inPs ++ List.map convertOutByRefParam oRefPs
    unless (sameLength allInPs ins)
      $ shouldnt $ "in call to " ++ show wybeProc
            ++ ", argument count " ++ show (length ins)
            ++ " does not match parameter count " ++ show (length allInPs)
            ++ "\n " ++ show ins
            ++ " vs. " ++ show allInPs
    unless (sameLength outPs outs)
      $ shouldnt $ "in call to " ++ show wybeProc
            ++ ", output argument count " ++ show (length outs)
            ++ " does not match output parameter count " ++ show (length outPs)
            ++ "\n " ++ show outs
            ++ " vs. " ++ show outPs
    paramTypes <- mapM (typeRep . primParamType) allInPs
    argList <- llvmStringArgList <$> zipWithM typeConvertedArg paramTypes ins
    outReps <- mapM (typeRep . primParamType) outPs
    let outTy = llvmRepReturnType outReps
    let (name,cc) = llvmProcName wybeProc
    llvmAssignConvertedResults outs outReps $
        tailKind ++ "call " ++ cc ++ " " ++ outTy ++ " " ++ name ++ argList


-- | Generate a native LLVM instruction
writeLLVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLLVMCall op flags args pos = do
    (ins,outs) <- partitionArgs ("llvm " ++ op ++ " instruction") args
    logLLVM $ "llvm instr args " ++ show args ++ " => ins "
             ++ show ins ++ " ; outs " ++ show outs
    case (ins,outs) of
        ([],[]) -> return () -- eliminate if all data flow was phantoms
        ([arg],[out@ArgVar{}]) ->
            if op == "move" then
                typeConvert arg out
            else if op `Map.member` llvmMapUnop then do
                outTy <- llvmTypeRep <$> argTypeRep out
                llvmArg <- llvmArgument arg
                llvmAssignResults outs $ op ++ " " ++ llvmArg ++ " to " ++ outTy
            else shouldnt $ "unknown unary llvm op " ++ op
        ([_,_],[out]) -> do
            let BinOpInfo {binOpInstr=instr,binOpArgSize=argSize,
                           binOpResultFn=resultFn} =
                    trustFromJust ("unknown binary llvm op " ++ op)
                    $ Map.lookup op llvmMapBinop
            (argList,outRep) <- llvmInstrArgumentList argSize out ins resultFn
            llvmAssignConvertedResult out outRep $ instr ++ " " ++ argList
        _ -> shouldnt $ "unknown llvm op " ++ op ++ " (arity "
                         ++ show (length ins) ++ ")"


-- | Generate LPVM (memory management) instruction
writeLPVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLPVMCall "alloc" _ args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm alloc instruction" args
    case args' of
        ([sz],[out]) -> heapAlloc out sz pos
        _            -> shouldnt $ "lpvm alloc with arguments " ++ show args
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
    -- TODO We could actually support take-reference for this op
    releaseDeferredCall
    args' <- partitionArgs "lpvm store instruction" args
    case args' of
        ([],[]) -> return ()
        ([val,ptr],[]) -> llvmStore ptr val
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
            arg <- typeConvertedArg CPointer addrArg
            llvmAssignResults outs $ "load " ++ lltype ++ ", " ++ arg
        (ins,outs) ->
            shouldnt $ "lpvm access with inputs " ++ show ins ++ " and outputs "
                ++ show outs
writeLPVMCall "mutate" _ args pos = do
    args' <- partitionArgsWithRefs args
    case args' of
        (_,_,_:_,_) ->
             shouldnt $ "LPVM mutate instruction with out-by-reference arg: "
                        ++ show args
        (struct:offset:destr:size:startOffset:restIns,
                [struct2@ArgVar{argVarName=struct2Name}],_,iRefs) -> do
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
                    (writeArg,readArg) <- freshTempArgs $ argType struct2
                    writeLLVMCall "add" []
                        [setArgFlow FlowIn struct2,offset,writeArg] Nothing
                    return readArg
            logLLVM $ "address to store into is held by " ++ show ptrArg
            case (restIns,iRefs) of
                ([member],[]) -> do
                    logLLVM "Normal (non-take-reference) case"
                    llvmStore ptrArg member
                ([],[takeRef]) -> do
                    -- FlowTakeReference case:  generate and record a fresh
                    -- local variable to hold the pointer to the location the
                    -- value should be written in, once it's generated.
                    logLLVM "Special take-reference case"
                    (writeCPtrArg,readCPtrArg) <-
                        freshTempArgs $ Representation CPointer
                    let takeRefVar = argVar "in lpvm mutate" takeRef
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
    llvmAssignResults outs $ "call ccc " ++ outTy ++ " " ++ llvmGlobalName cfn
                            ++ argList


-- | Generate C function call with inputs and outputs type converted as needed.
marshalledCCall :: ProcName -> [Ident] -> [PrimArg] -> [String] -> OptPos
                -> LLVM ()
marshalledCCall cfn flags args ctypes pos = do
    (ins,outs) <- partitionArgTuples cfn $ zip args ctypes
    argList <- llvmStringArgList <$> mapM (uncurry marshallArgument) ins
    let instr = llvmGlobalName cfn ++ argList
    case outs of
        [] -> llvmPutStrLnIndented $ "call ccc void " ++ instr
        [(out,cType)] -> marshallCallResult out cType instr
        _ -> shouldnt "C function call with multiple outputs"


-- | Generate and write out the LLVM return statement.
writeAssemblyReturn :: [PrimParam] -> LLVM ()
writeAssemblyReturn [] = llvmPutStrLnIndented "ret void"
writeAssemblyReturn [PrimParam{primParamName=v, primParamType=ty}] = do
    llty <- llvmTypeRep <$> typeRep ty
    llvar <- varToRead v
    llvmPutStrLnIndented $ "ret " ++ makeLLVMArg llty llvar
writeAssemblyReturn params = do
    retType <- llvmReturnType $ List.map primParamType params
    tuple <- buildTuple retType "undef" 0 params
    llvmPutStrLnIndented $ "ret " ++ makeLLVMArg retType tuple


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
                            ++ tuple ++ ", " ++ makeLLVMArg llty llvar
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
    logLLVM "writeAssemblyExports"
    llvmBlankLine
    m <- llvmGetModule modSpec
    modBS <- lift $ List.map BI.w2c . BL.unpack <$> encodeModule m
    let constName = "##MODULE:" ++ showModSpec m
    declareStringConstant constName modBS $ Just lpvmSectionName


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
    llvmVals <- mapM (uncurry convertedConstantArg) fields
    return $ llvmStructType (snd <$> fields)
            ++ " { " ++ intercalate ", " llvmVals ++ " }"


----------------------------------------------------------------------------
-- Support code
----------------------------------------------------------------------------

-- | Generate an LLVM load instruction to load from the specified address into
-- the specified variable
llvmLoad :: PrimArg -> PrimArg -> LLVM ()
llvmLoad ptr outVar = do
    lltype <- llvmTypeRep <$> argTypeRep outVar
    arg <- typeConvertedArg CPointer ptr
    llvmAssignResult outVar $ "load " ++ lltype ++ ", " ++ arg


-- | Generate an LLVM store instruction to store the specified PrimArg into the
-- specified address.
llvmStore :: PrimArg -> PrimArg -> LLVM ()
llvmStore ptr toStore = llvmArgument toStore >>= llvmStoreValue ptr


-- | Generate an LLVM store instruction to store the specified LLVM argument
-- into the specified address.
llvmStoreValue :: PrimArg -> LLVMArg -> LLVM ()
llvmStoreValue ptr llVal = do
    cptr <- typeConvertedArg CPointer ptr
    llvmAssignResults [] $ "store " ++ llVal ++ ", " ++ cptr


-- | Generate LLVM store instructions to store all elements of the specified
-- list into words of memory beginning with the specified pointer.
llvmStoreArray :: PrimArg -> [LLVMArg] -> LLVM ()
llvmStoreArray ptr [] = return ()
llvmStoreArray ptr (llVal:llVals) = do
    llvmStoreValue ptr llVal
    foldM_ (\p v -> do
        cptr <- pointerOffset p wordSizeBytes
        llvmStoreValue cptr llVal
        return cptr
      ) ptr llVals


-- | Compute the specified offset to a pointer, returning the result as a
-- CPointer ready to use for loading or storing.  The input pointer can be a
-- Pointer or CPointer.
pointerOffset :: PrimArg -> Int -> LLVM PrimArg
pointerOffset ptr 0 = typeConvertedPrim CPointer ptr
pointerOffset ptr offset = do
    addr <- typeConvertedPrim Pointer ptr
    addrArg <- llvmArgument addr
    (writePtr,readPtr) <- freshTempArgs $ Representation Pointer
    llvmAssignConvertedResult writePtr Pointer
        $ "add " ++ addrArg ++ ", " ++ show offset
    return readPtr


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
    marshalledCCall mallocFn [] [size,writeCPtr] ["int","pointer"] Nothing
    copyfn <- llvmMemcpyFn
    let nonvolatile = ArgInt 0 $ Representation $ Bits 1
    writeCCall copyfn [] [readCPtr,readStartCPtr,size,nonvolatile] Nothing
    (writePtr,readPtr) <- freshTempArgs $ Representation Pointer
    typeConvert readCPtr writePtr
    case startOffset of
        ArgInt 0 _ -> typeConvert readPtr newStruct
        _ -> writeLLVMCall "add" [] [readPtr,startOffset,newStruct] Nothing


----------------------------------------------------------------------------
-- Handling parameters and arguments
----------------------------------------------------------------------------

-- | The LLVM parameter declaration for the specified Wybe input parameter as a
-- pair of LLVM type and variable name.
llvmParameter :: PrimParam -> LLVM String
llvmParameter PrimParam{primParamName=name, primParamType=ty,
                        primParamFlow=FlowIn} = do
    let llname = llvmLocalName name
    tyRep <- typeRep ty
    let lltype = llvmTypeRep tyRep
    modify $ \s -> s { varTypes=Map.insert llname tyRep $ varTypes s }
    return $ makeLLVMArg lltype llname
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


-- | The LLVM translation of the specified LLVM instruction argument list.
-- Since all arguments of these instructions must have the same types, the type
-- is only shown once, at the front.
llvmInstrArgumentList :: LLVMArgSize -> PrimArg -> [PrimArg]
        -> (TypeRepresentation -> TypeRepresentation)
        -> LLVM (String,TypeRepresentation)
llvmInstrArgumentList argSize output inputs repFn = do
    (outTy : inTys) <- mapM argTypeRep $ output : inputs
    let typeRep = resolveLLVMArgType argSize outTy inTys
    let outTyRep = repFn typeRep
    let llArgTyRep = llvmTypeRep typeRep
    argsString <- intercalate ", " <$> mapM (typeConverted typeRep) inputs
    return (makeLLVMArg llArgTyRep argsString, outTyRep)


-- | Write the LLVM translation of the specified output argument list as target
-- for the specified instruction.  For multiple outputs, we must unpack a tuple.
llvmAssignResults :: [PrimArg] -> String -> LLVM ()
llvmAssignResults [] instr = llvmPutStrLnIndented instr
llvmAssignResults [arg] instr = do
    llvmAssignResult arg instr
llvmAssignResults multiOuts instr = do
    tuple <- llvmLocalName <$> makeTemp
    retType <- llvmReturnType $ argVarType <$> multiOuts
    llvmPutStrLnIndented $ tuple ++ " = " ++ instr
    -- This uses llvmAssignSingleResult to store each individual tuple element
    zipWithM_ (unpackArg retType tuple) multiOuts [0..]


-- | Write the LLVM translation of the specified single output argument as
-- target for the specified instruction.
llvmAssignResult :: PrimArg -> String -> LLVM ()
llvmAssignResult arg@ArgVar{argVarName=varName,argVarType=ty} instr = do
    tyRep <- typeRep ty
    let llty = llvmTypeRep tyRep
    llVar <- varToWrite varName llty
    logLLVM $ "Assigning variable " ++ show varName ++ " (=> " ++ llVar ++ ")"
    llvmPutStrLnIndented $ llVar ++ " = " ++ instr
    varValue <- llvmArgument arg
    storeValueIfNeeded varName varValue
    knownType <- gets $ Map.lookup llVar . varTypes
    when (isJust knownType) $
        shouldnt $ "Error generating LLVM:  reassigning LLVM variable " ++ llVar
    modify $ \s -> s { varTypes = Map.insert llVar tyRep $ varTypes s}
llvmAssignResult notAVar instr = do
    shouldnt $ "llvmAssignResult into non-variable " ++ show notAVar


-- | Write the LLVM translation of the specified variables as target for the
-- specified instruction, converting from the specified type representations if
-- necessary.
llvmAssignConvertedResults :: [PrimArg] -> [TypeRepresentation] -> String
                           -> LLVM ()
llvmAssignConvertedResults [] _ instr = llvmPutStrLnIndented instr
llvmAssignConvertedResults [arg] (actualRep:_) instr =
     llvmAssignConvertedResult arg actualRep instr
llvmAssignConvertedResults multiOuts multiReps instr = do
    tuple <- llvmLocalName <$> makeTemp
    let retType = llvmRepReturnType multiReps
    llvmPutStrLnIndented $ tuple ++ " = " ++ instr
    -- This uses llvmAssignResult to store each individual tuple element
    sequence_
        $ zipWith3 (unpackConvertedArg retType tuple) multiOuts multiReps [0..]


-- | Write the LLVM translation of the specified single output variable as
-- target for the specified instruction, converting from the specified type
-- representation if necessary.
llvmAssignConvertedResult :: PrimArg -> TypeRepresentation -> String -> LLVM ()
llvmAssignConvertedResult arg@ArgVar{argVarName=varName,argVarType=ty}
                         actualRep instr = do
    neededRep <- typeRep ty
    if equivLLTypes neededRep actualRep
        then do
            llvmAssignResult arg instr
        else do
            (writeArg,readArg) <- freshTempArgs $ Representation actualRep
            llvmAssignResult writeArg instr
            typeConvert readArg arg
llvmAssignConvertedResult notAVar _ _ =
    shouldnt $ "llvmAssignConvertedResult into non-variable " ++ show notAVar


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
    let instr' = "call ccc " ++ llvmTypeRep inTypeRep ++ " " ++ instr
    if equivLLTypes inTypeRep outTypeRep then llvmAssignResult outArg instr'
    else do
        (writeTmp,readTmp) <- freshTempArgs $ Representation inTypeRep
        llvmAssignResult writeTmp instr'
        typeConvert readTmp outArg
marshallCallResult outArg inTypeRep instr =
    shouldnt $ "Can't marshall result into non-variable " ++ show outArg


-- | Write an LLVM instruction to unpack one argument from a tuple.
-- instruction looks like:  %var = extractvalue {i64, i1} %0, 0
unpackArg :: LLVMType -> LLVMName -> PrimArg -> Int -> LLVM ()
unpackArg typ tuple arg argNum = do
    logLLVM $ "Extracting arg " ++ show argNum ++ " into " ++ show arg
    llvmAssignResult arg $ "extractvalue " ++ typ
                            ++ tuple ++ ", " ++ show argNum

-- | Write an LLVM instruction to unpack one argument from a tuple.
-- instruction looks like:  %var = extractvalue {i64, i1} %0, 0
unpackConvertedArg :: LLVMType -> LLVMName -> PrimArg -> TypeRepresentation
                   -> Int -> LLVM ()
unpackConvertedArg typ tuple arg tyRep argNum = do
    logLLVM $ "Extracting arg " ++ show argNum
            ++ " (representation " ++ show tyRep ++ ") into " ++ show arg
    llvmAssignConvertedResult arg tyRep $ "extractvalue " ++ typ
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
    else typeConvertedArg outTypeRep arg


-- | The LLVM type of the specified argument.  Wybe strings are Wybe pointers; C
-- strings are also Wybe pointers, because we do address arithmetic on them;
-- globals are C pointers.  Other kinds of args are represented however their
-- types say they are.
argTypeRep :: PrimArg -> LLVM TypeRepresentation
argTypeRep (ArgString _ WybeString _) = return Pointer
argTypeRep (ArgString _ CString _)    = return Pointer
argTypeRep ArgGlobal{}                = return CPointer
argTypeRep ArgClosure{}               = return CPointer
argTypeRep arg                        = typeRep $ argType arg


-- | The LLVM argument for the specified PrimArg as an LLVM type and value
llvmArgument :: PrimArg -> LLVM LLVMArg
llvmArgument arg = do
    tyRep <- argTypeRep arg
    let lltype = llvmTypeRep tyRep
    llVal <- llvmValue arg
    return $ makeLLVMArg lltype llVal


makeLLVMArg :: LLVMType -> String -> LLVMArg
makeLLVMArg ty val = ty ++ " " ++ val


-- | A PrimArg as portrayed in LLVM code
llvmValue :: PrimArg -> LLVM String
llvmValue argVar@ArgVar{argVarName=var, argVarType=ty} = do
    realVar <- varToRead var
    thisRep <- typeRep ty
    currRep <- gets $ Map.lookup realVar . varTypes
    case (currRep,thisRep) of
        (Nothing,_) -> do
            logLLVM $ "Using unknown LLVM variable " ++ realVar
            return realVar
        (Just defRep, useRep) | equivLLTypes defRep useRep -> return realVar
        (Just defRep, useRep) ->
            typeConverted thisRep argVar{argVarType=Representation defRep}
llvmValue (ArgInt val _) = return $ show val
llvmValue (ArgFloat val _) = return $ show val
llvmValue (ArgString str stringVariant _) = do
    let spec = case stringVariant of
                WybeString -> WybeStringSpec str
                CString    -> CStringSpec str
    glob <- lookupConstant spec
    convertedConstant
        (ArgGlobal (GlobalVariable glob) $ Representation CPointer) Pointer
llvmValue (ArgChar val _) = return $ show $ fromEnum val
llvmValue arg@(ArgClosure pspec args ty) = do
    logLLVM $ "llvmValue of " ++ show arg
    -- See if we've already allocated a constant for this closure
    glob <- tryLookupConstant $ ClosureSpec pspec args
    case glob of
        Just constName ->
            return $ llvmGlobalName constName
        Nothing -> do
            (writePtr,readPtr) <- freshTempArgs $ Representation CPointer
            let fnRef = funcRef pspec
            let sizeVar =
                    ArgInt (fromIntegral (wordSizeBytes * (1 + length args)))
                            intType
            logLLVM "Creating closure"
            heapAlloc writePtr sizeVar Nothing
            llArgs <- mapM llvmArgument args
            llvmStoreArray readPtr (fnRef:llArgs)
            logLLVM $ "Finished creating closure; result is " ++ show readPtr
            rep <- typeRep ty
            logLLVM $ "Converting to representation " ++ show rep
            llvmValue readPtr
llvmValue (ArgGlobal val _) = llvmGlobalInfoName val
llvmValue (ArgUnneeded val _) = return "undef"
llvmValue (ArgUndef _) = return "undef"


-- | The LLVMArg translation of a ProcSpec.
funcRef :: ProcSpec -> LLVMArg
funcRef pspec = "ptr " ++ llvmGlobalName (show pspec)


-- | The variable name of a PrimArg; report an error if not a variable.
argVar :: String -> PrimArg -> PrimVarName
argVar _ ArgVar{argVarName=var} =  var
argVar msg _ = shouldnt $ "variable argument expected " ++ msg


neededFreeArgs :: ProcSpec -> [PrimArg] -> LLVM [PrimArg]
neededFreeArgs pspec args = lift $ do
    params <- List.filter ((==Free) . primParamFlowType) . primProtoParams
              . procImplnProto . procImpln <$> getProcDef pspec
    List.map snd <$> filterM (paramIsReal . fst) (zip params args)



----------------------------------------------------------------------------
-- Converting Wybe types to LLVM types 
----------------------------------------------------------------------------

-- | Return the representation for the specified type
typeRep :: TypeSpec -> LLVM TypeRepresentation
typeRep ty =
    trustFromJust ("lookupTypeRepresentation of unknown type " ++ show ty)
      <$> lift (lookupTypeRepresentation ty)


-- | Return the LLMV name and type representation of the specified resource.
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
llvmTypeRep (Func _ _)      = llvmTypeRep Pointer
llvmTypeRep Pointer         = llvmTypeRep $ Bits wordSize
llvmTypeRep CPointer        = "ptr"


-- | The LLVM return type for proc with the specified list of output type specs.
llvmRepReturnType :: [TypeRepresentation] -> LLVMType
llvmRepReturnType [] = "void"
llvmRepReturnType [ty] = llvmTypeRep ty
llvmRepReturnType tys = llvmStructType tys


-- | An LLVM structure type based on a list of LLVM type representations
llvmStructType :: [TypeRepresentation] -> LLVMType
llvmStructType tys = "{" ++ intercalate ", " (List.map llvmTypeRep tys) ++ "}"


-- | The LLVM return type for proc with the specified list of output type specs.
llvmReturnType :: [TypeSpec] -> LLVM LLVMType
llvmReturnType specs = llvmRepReturnType <$> mapM typeRep specs


----------------------------------------------------------------------------
-- LLVM Type conversion
--
-- We convert between LLVM types in a few contexts:
--
--   * To pass Wybe values to C or return C values to Wybe
--
--   * To convert typed values to generic ones or vice versa
--
--   * To make LLVM binary operation argument types consistent (eg, to add an
--     int to a char)
--
--   * To convert between CPointer and Pointer types for address arithmetic
--
--   * To implement the lpvm cast operation
--
-- This excludes explicit conversion, such as float:float or float:iround, which
-- are handled by explicitly using LLVM intrinsics or instructions.
----------------------------------------------------------------------------

-- | Emit an instruction to convert the specified input argument to the
-- specified output argument.
typeConvert :: PrimArg -> PrimArg -> LLVM ()
typeConvert fromArg toArg = do
    toTy <- argTypeRep toArg
    fromTy <- argTypeRep fromArg
    fromVal <- llvmValue fromArg
    logLLVM $ "typeConvert " ++ fromVal ++ " from " ++ show fromTy
                ++ " to " ++ show toTy
    case toArg of
        ArgVar{argVarName=varName} | equivLLTypes fromTy toTy ->
            renameVariable varName fromVal $ llvmTypeRep fromTy
        _ ->
            llvmAssignResult toArg
              $ typeConvertOp fromTy toTy ++ " "
                ++ makeLLVMArg (llvmTypeRep fromTy) fromVal
                ++ " to " ++ llvmTypeRep toTy


-- | Convert the specified PrimArg to a PrimArg with the specified
-- representation.
typeConvertedPrim :: TypeRepresentation -> PrimArg -> LLVM PrimArg
typeConvertedPrim toTy fromArg = do
    logLLVM $ "Converting PrimArg " ++ show fromArg ++ " to " ++ show toTy
    argRep <- argTypeRep fromArg
    if equivLLTypes argRep toTy
        then return fromArg
        else do
            (writeArg,readArg) <- freshTempArgs $ Representation toTy
            typeConvert fromArg writeArg
            return readArg


-- | LLVM code to convert PrimArg fromVal to representation toTy, returning an
-- LLVMArg holding the converted value.
typeConvertedArg :: TypeRepresentation -> PrimArg -> LLVM LLVMArg
typeConvertedArg toTy fromArg
    | argIsConst fromArg = convertedConstantArg fromArg toTy
    | otherwise = typeConvertedPrim toTy fromArg >>= llvmArgument


-- | LLVM code to convert PrimArg fromVal to representation toTy, returning a
-- LLVMName (ie, without type prefix) holding the converted value.
typeConverted :: TypeRepresentation -> PrimArg -> LLVM LLVMName
typeConverted toTy fromArg
    | argIsConst fromArg = convertedConstant fromArg toTy
    | otherwise = do
        argRep <- argTypeRep fromArg
        if equivLLTypes argRep toTy
            then llvmValue fromArg
            else do
                (writeArg,readArg) <- freshTempArgs $ Representation toTy
                typeConvert fromArg writeArg
                llvmValue readArg


-- | An LLVM constant expression of the specified type toTy, when the constant
-- is initially of the specified type fromTy.  This may take the form of an
-- LLVM type conversion expression, which is fully evaluated at compile-time, so
-- it cannot involve conversion instructions.
convertedConstant :: PrimArg -> TypeRepresentation -> LLVM LLVMName
convertedConstant arg toTy = do
    -- XXX should verify that arg is constant, if ArgGlobal is considered const
    logLLVM $ "Converting constant " ++ show arg ++ " to type " ++ show toTy
    fromTy <- argTypeRep arg
    logLLVM $ "  conversion " ++ show fromTy ++ " -> " ++ show toTy
            ++ (if trivialConstConversion fromTy toTy then " IS" else " is NOT")
            ++ " trivial"
    if trivialConstConversion fromTy toTy
        then llvmValue arg
        else do
            fromArg <- llvmArgument arg
            return $ typeConvertOp fromTy toTy ++ "( "
                         ++ fromArg ++ " to " ++ llvmTypeRep toTy ++ " )"


-- | An LLVM constant expression of the specified type toTy, when the constant
-- is initially of the specified type fromTy.  This may take the form of an
-- LLVM type conversion expression, which is fully evaluated at compile-time, so
-- it cannot involve conversion instructions.
convertedConstantArg :: PrimArg -> TypeRepresentation -> LLVM LLVMArg
convertedConstantArg arg toTy = do
    -- XXX should verify that arg is constant, if ArgGlobal is considered const
    makeLLVMArg (llvmTypeRep toTy) <$> convertedConstant arg toTy



-- Converting constants from the first type to the second is completely trivial,
-- because the constant is automatically considered to have both types.
trivialConstConversion :: TypeRepresentation -> TypeRepresentation -> Bool
trivialConstConversion ty1 ty2 | ty1 == ty2       = True
trivialConstConversion (Bits _) (Bits _)          = True
trivialConstConversion (Bits _) (Signed _)        = True
trivialConstConversion (Bits _) Pointer           = True
trivialConstConversion (Signed _) (Signed _)      = True
trivialConstConversion (Signed _) (Bits _)        = True
trivialConstConversion (Signed _) Pointer         = True
trivialConstConversion (Floating _) (Floating _)  = True
trivialConstConversion Pointer (Bits b)           = b == wordSize
trivialConstConversion Pointer (Signed b)         = b == wordSize
trivialConstConversion _ _                        = False


-- | Are two type representations the same in LLVM (and hence need no
-- conversion)?
equivLLTypes :: TypeRepresentation -> TypeRepresentation -> Bool
equivLLTypes Pointer (Bits b)      = b == wordSize
equivLLTypes Pointer (Signed b)    = b == wordSize
equivLLTypes (Bits b) Pointer      = b == wordSize
equivLLTypes (Signed b) Pointer    = b == wordSize
equivLLTypes (Signed b1) (Bits b2) = b1 == b2
equivLLTypes (Bits b1) (Signed b2) = b1 == b2
equivLLTypes Func{} Func{}         = True -- Since LLVM just considers them ptrs
equivLLTypes Pointer Func{}        = True
equivLLTypes Func{} Pointer        = True
equivLLTypes t1 t2 = t1 == t2


-- | The appropriate type conversion operator to convert from fromTy to toTy
typeConvertOp :: TypeRepresentation -> TypeRepresentation -> String
typeConvertOp fromTy toTy
    | fromTy == toTy = "bitcast" -- use bitcast for no-op conversion
typeConvertOp Pointer toTy   = typeConvertOp (Bits wordSize) toTy
typeConvertOp fromTy Pointer = typeConvertOp fromTy (Bits wordSize)
typeConvertOp Func{} toTy    = typeConvertOp (Bits wordSize) toTy
typeConvertOp fromTy Func{}  = typeConvertOp fromTy (Bits wordSize)
typeConvertOp (Bits m) (Bits n)
    | m < n = "zext"
    | n < m = "trunc"
    | otherwise = shouldnt "no-op unsigned conversion"
typeConvertOp (Bits m) (Signed n)
    | m < n = "sext"
    | n < m = "trunc"
    | otherwise = -- no instruction actually needed, but one is expected
        "bitcast"
typeConvertOp (Bits _) CPointer = "inttoptr"
typeConvertOp (Signed m) (Bits n)
    | m < n = "zext"
    | n < m = "trunc"
    | otherwise = -- no instruction actually needed, but one is expected
        "bitcast"
typeConvertOp (Signed m) (Signed n)
    | m < n = "sext"
    | n < m = "trunc"
    | otherwise = shouldnt "no-op signed int conversion"
typeConvertOp (Floating m) (Floating n)
    | m < n = "fpext"
    | n < m = "fptrunc"
    | otherwise = shouldnt "no-op floating point conversion"
typeConvertOp CPointer (Bits _) = "ptrtoint"
-- These don't change representation, or change any bits.  They just
-- re-interpret a FP number as an integer or vice versa.  This ensures we don't
-- lose precision or waste time on round trip conversion.
typeConvertOp (Bits m) (Floating n) = "bitcast"
typeConvertOp (Signed m) (Floating n) = "bitcast"
typeConvertOp (Floating m) (Bits n) = "bitcast"
typeConvertOp (Floating m) (Signed n) = "bitcast"
typeConvertOp repIn toTy =
    shouldnt $ "Don't know how to convert from " ++ show repIn
                 ++ " to " ++ show toTy


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

-- | Information we collect about external things referenced by this module, so
-- we can declare them.  For functions, this includes the LLVM calling
-- convention, the LLVM name of the function, and the input and output argument
-- types.
data ExternSpec =
    -- | An external function we call
    ExternFunction {
        extFnCC   :: String,     -- ^ The function's calling convention
        extFnName :: LLVMName,   -- ^ The function's LLVM name (with @)
        extFnArgs :: [TypeSpec], -- ^ The function's input argument types
        extFnOut  :: [TypeSpec]  -- ^ The function's result (tuple) types
        }
      -- | An external global variable we refer to
    | ExternVariable {
        extVarName :: GlobalInfo, -- ^ The global variable to declare
        extVarType :: TypeSpec    -- ^ The variable's Wybe type
        }
    deriving (Eq,Ord,Show)


-- | Return the name of the thing that the EsternSpec declares
externID :: ExternSpec -> LLVM LLVMName
externID ExternFunction{extFnName=name}  = return name
externID ExternVariable{extVarName=name} = llvmGlobalInfoName name


-- | Information needed to specify one constant value, giving the representation
-- to be stored and the (constant) value itself.
type ConstSpec = (PrimArg,TypeRepresentation)


-- | The LLVM State monad
data LLVMState = LLVMState {
        -- These values apply to a whole module (and submodules)
        allConsts :: Set StaticConstSpec,
                                     -- ^ Static constants appearing in module
        constNames :: Map StaticConstSpec Ident,
                                    -- ^ local name given to static constants
        allExterns :: Map String ExternSpec,
                                    -- ^ Extern declarations needed by module
        fileHandle :: Handle,       -- ^ The file handle we're writing to
        -- These values apply to the single proc being translated
        tmpCounter :: Int,          -- ^ Next temp var to make for current proc
        labelCounter :: Int,        -- ^ Next label number to use
        varDefRenaming :: Set PrimVarName,
                                    -- ^ Vars to rename on definition
        varUseRenaming :: Map PrimVarName LLVMName,
                                    -- ^ New action for some variables to read
        varTypes :: Map LLVMName TypeRepresentation,
                                    -- ^ The LLVM type rep of defined vars
        deferredCall :: Maybe (ProcSpec, [PrimArg], [PrimArg], [PrimArg]),
                                    -- ^ Wybe proc call deferred for
                                    -- out-by-reference arg, with in, out, and
                                    -- out-by-ref args
        takeRefVars :: Map PrimVarName (PrimArg,TypeSpec),
                                    -- ^ arg to read each take-reference ptr,
                                    -- plus the type of the original variable
        outByRefVars :: Map PrimVarName (PrimArg,TypeSpec),
                                    -- ^ ptr to write each out-by-reference var
                                    -- to, when the var is written, plus the
                                    -- type of the var
        doesAlloca :: Bool          -- Does current body do alloca?
}


-- | Set up LLVM monad to translate a module into the given file handle
initLLVMState :: Handle -> LLVMState
initLLVMState h = LLVMState Set.empty Map.empty Map.empty h 0 0 Set.empty
                     Map.empty Map.empty Nothing Map.empty Map.empty False


-- | Reset the LLVM monad in preparation for translating a proc definition with
-- the specified temp counter.
initialiseLLVMForProc :: Int -> LLVM ()
initialiseLLVMForProc tmpCount = do
    modify $ \s -> s { tmpCounter = tmpCount
                     , labelCounter = 0
                     , varDefRenaming = Set.empty
                     , varUseRenaming = Map.empty
                     , varTypes = Map.empty
                     , deferredCall = Nothing
                     , takeRefVars = Map.empty
                     , outByRefVars = Map.empty
                     , doesAlloca = False
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
setRenaming vars = do
    logLLVM $ "Recording variables needing renaming = " ++ show vars
    modify $ \s -> s { varDefRenaming = vars }


-- | Replace the specified variable with the specified new value in all
-- following code.
renameVariable :: PrimVarName -> LLVMName -> LLVMType -> LLVM ()
renameVariable var val llty = do
    modify $ \s -> s { varUseRenaming = Map.insert var val $ varUseRenaming s }
    storeValueIfNeeded var $ makeLLVMArg llty val


-- | The LLVM name for a variable we are about to assign.  If this is one of the
-- output parameters, rename it, otherwise leave it alone, and in either case,
-- transform it to an LLVM local variable name.
varToWrite :: PrimVarName -> LLVMType -> LLVM LLVMName
varToWrite v llty = do
    mustRename <- Set.member v <$> gets varDefRenaming
    logLLVM $ "varToWrite " ++ show v ++ "; mustRename = " ++ show mustRename
    vdr <- gets varDefRenaming
    logLLVM $ "varDefRenaming = " ++ show vdr
    if mustRename then do
        tmp <- llvmLocalName <$> makeTemp
        renameVariable v tmp llty
        return tmp
    else do
        -- rename v next time we try to assign it.  This can happen because LPVM
        -- isn't quite *static* single assignment, so the same variable name can
        -- be assigned in multiple branches.  In that case, rename later
        -- assignments.
        modify $ \s -> s { varDefRenaming = Set.insert v $ varDefRenaming s }
        return $ llvmLocalName v


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


-- | Record readPtrArg as the variable that holds the pointer to the place to
-- store the value assigned when a value is assigned to var, along with the type
-- of the value.
addOutByRefPointer :: PrimVarName -> PrimArg -> TypeSpec -> LLVM ()
addOutByRefPointer var readPtrArg ty = do
    logLLVM $ "Recording out-by-ref pointer " ++ show readPtrArg
            ++ " as place to store values assigned to " ++ show var
            ++ ":" ++ show ty
    modify $ \s -> s{ outByRefVars =
                        Map.insert var (readPtrArg,ty) $ outByRefVars s }


-- | The specified value is to be assigned to the specified variable.  If that
-- variable is recorded as an out-by-reference, then store the value where we've
-- recorded it should be stored.
storeValueIfNeeded :: PrimVarName -> LLVMArg -> LLVM ()
storeValueIfNeeded var val = do
    rec <- gets $ Map.lookup var . outByRefVars
    case rec of
        Nothing -> return ()
        Just (readPtrArg,ty) -> do
            logLLVM $ "Storing value " ++ show val ++ ":" ++ show ty
                    ++ " through pointer " ++ show readPtrArg
            llvmStoreValue readPtrArg val


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
            tailKind <- tailMarker allOld
            writeActualCall wybeProc (ins++refIns) outs tailKind
            unless allOld $ zipWithM_ (\refIn oRef -> do
                let byRefArg = setArgFlow FlowOut oRef
                llvmLoad refIn byRefArg
              ) refIns oRefs
            modify $ \s -> s{ deferredCall = Nothing, takeRefVars = Map.empty }


-- | Convert a FlowOutByeReference argument into an input CPointer arg.  If
-- we've already created a variable for the pointer, use that, otherwise alloca
-- space for the value and return an argument holding a pointer to it.  Also
-- return a Boolean indicating whether the variable was already created.
convertOutByRefArg :: PrimArg -> LLVM (PrimArg,Bool)
convertOutByRefArg ArgVar{argVarName=name, argVarType=ty,
                        argVarFlow=FlowOutByReference} = do
    logLLVM $ "Converting out-by-ref var " ++ show name
    maybePtrArg <- gets $ Map.lookup name . takeRefVars
    case maybePtrArg of
        Just (ptrArg,_) -> do
            logLLVM $ " -> already a take-reference: returning " ++ show ptrArg
            return (ptrArg,True)
        Nothing -> do
            logLLVM " -> Not a take-reference, checking for out-by-reference"
            maybeOBRVar <- gets $ Map.lookup name . outByRefVars
            case maybeOBRVar of
                Just (ptrArg,_) -> do
                    logLLVM $ " -> already out-by-reference: returning "
                                ++ show ptrArg
                    return (ptrArg,True)
                Nothing -> do
                    logLLVM " -> Not out-by-reference: making fresh alloca ptr"
                    (writeArg,readArg) <- freshTempArgs $ Representation CPointer
                    stackAlloc writeArg wordSizeBytes
                    addTakeRefPointer name readArg ty
                    return (readArg,False)
convertOutByRefArg other =
    shouldnt $ "Expected out-by-reference argument: " ++ show other


-- | Convert an out-by-reference parameter into an input parameter that points
-- to the place to write the actual output.
convertOutByRefParam :: PrimParam -> PrimParam
convertOutByRefParam param =
    param{primParamType=Representation CPointer, primParamFlow=FlowIn}


-- | Generate code to allocate heap memory, with the size in bytes specified as
-- a PrimArg, so it can be a variable.  The result will be converted to the type
-- of the result variable.
heapAlloc :: PrimArg -> PrimArg -> OptPos -> LLVM ()
heapAlloc result sizeVar =
    marshalledCCall mallocFn [] [sizeVar,result] ["int","pointer"]


-- | Generate code to allocate memory on the stack (alloca), with the size in
-- bytes specified as an Int, so it must be a constant.    The result will be
-- converted to the type of the result variable.
stackAlloc :: PrimArg -> Int -> LLVM ()
stackAlloc result size = do
    llvmAssignResult result $ "alloca i8, i64 " ++ show size
        ++ ", align " ++ show wordSizeBytes
    modify $ \s -> s { doesAlloca = True }


----------------------------------------------------------------------------
-- Formatting for LLVM                                                    --
----------------------------------------------------------------------------

-- | The LLVM name for a Wybe proc, with its LLVM calling convention.
llvmProcName :: ProcSpec -> (LLVMName,String)
llvmProcName ProcSpec{procSpecMod=[],procSpecName=""} =
    (llvmGlobalName "main", "ccc")
llvmProcName pspec = (llvmGlobalName $ show pspec, "fastcc")


-- | Make a suitable LLVM name for a global variable or constant.  We prefix it
-- with @, enclose the rest in quotes, and escape any special characters.
llvmGlobalName :: String -> LLVMName
llvmGlobalName s =
    '@' : llvmQuoteIfNecessary s


-- | Wrap quotes around the specified string, using character escapes for any
-- special characters, if it contains any characters but alphanumerics,
-- underscores, or period characters.
llvmQuoteIfNecessary :: String -> String
llvmQuoteIfNecessary s =
     if all ((=='_')|||(=='.')|||isAlphaNum) s
        then s
        else '"' : concatMap showLLVMChar s ++ "\""


-- | Produce a suitable LLVM global name based on a GlobalInfo
llvmGlobalInfoName :: GlobalInfo -> LLVM LLVMName
llvmGlobalInfoName (GlobalResource res) =
     fst <$> llvmResource res
llvmGlobalInfoName (GlobalVariable var) = return $ llvmGlobalName var


-- | Make a suitable LLVM name for a foreign (e.g., C) function.
llvmForeignName :: String -> LLVMName
llvmForeignName s = '@' : llvmQuoteIfNecessary s


-- | Make a suitable LLVM name for a local variable.  We prefix it
-- with %, enclose the rest in quotes, and escape any special characters.
llvmLocalName :: PrimVarName -> LLVMName
llvmLocalName varName =
    '%' : llvmQuoteIfNecessary (show varName)


-- | Make an LLVM reference to the specified label.
llvmLabelName :: String -> String
llvmLabelName varName = "label %" ++ llvmQuoteIfNecessary varName


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


-- | The malloc function we call.  Currently wybe_malloc, which just calls
-- GC_malloc.
mallocFn :: Ident
mallocFn = "wybe_malloc"


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
