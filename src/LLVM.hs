--  File     : LLVM.hs
--  Author   : Peter Schachte, based on work by Ashutosh Rishi Ranjan
--  Purpose  : Generate LLVM code from LPVM form
--  Copyright: (c) 2024 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
{-# LANGUAGE LambdaCase #-}

module LLVM ( llvmMapBinop, llvmMapUnop, writeLLVM ) where

import           AST
import           ASTShow
import           Resources
import           BinaryFactory
import           Config
import           Options
import           Version
import           CConfig
import           System.IO
import           Data.Set                        as Set
import           Data.Map                        as Map
import           Data.List                       as List
import           Data.Maybe
-- import           Control.Exception               (handle)
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.IO.Class
import           Data.Tuple.HT
import qualified Data.ByteString                 as B
import qualified Data.ByteString.Lazy            as BL

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
-- LLVM Assembler Generation
--
-- We generate an LLVM assembler (.ll) file as a translation of the generated
-- LPVM code for a module.  The parts of this file are:
--
--  the prologue     : boilerplate comments and declarations
--  constants        : manifest constants used in this module
--  global variables : implementation of the resources of this module
--  externs          : declarations of functions and globals defined elsewhere
--  definitions      : definitions of the procs of this module
--  exports          : everything needed to compile users of this module
--
----------------------------------------------------------------------------

-- At least for now, we represent LLVM types as strings
type LLVMType = String              -- ^ An LLVM type name, such as i8
type LLVMName = String              -- ^ An LLVM global name, such as a
                                    --   function, variable or constant name;
                                    --   must begin with @
type LLVMLocal = String             -- ^ An LLVM local variable name; must begin
                                    --   with %


data LLVMState = LLVMState {
        fileHandle :: Handle,       -- ^ The file handle we're writing to
        tmpCounter :: Int,          -- ^ Next temp var to make for current proc
        labelCounter :: Int,        -- ^ Next label number to use
        toRename :: Set PrimVarName, -- ^ Variables that need to get fresh names
        newNames :: Map PrimVarName PrimVarName
                                    -- | New names for some variables
}


initLLVMState :: Handle -> LLVMState
initLLVMState h = LLVMState h 0 0 Set.empty Map.empty

type LLVM = StateT LLVMState Compiler


-- | Apply some function to (access some member of) the current module from
-- within the LLVM monad.
llvmGetModule :: (Module -> a) -> LLVM a
llvmGetModule fn = lift $ getModule fn


-- | Write a string followed by a newline to the current LLVM output file handle
llvmPutStrLn :: String -> LLVM ()
llvmPutStrLn str = do
    h <- gets fileHandle
    liftIO $ hPutStrLn h str


-- | Write a blank line to the current LLVM output file handle
llvmBlankLine :: LLVM ()
llvmBlankLine = llvmPutStrLn ""


-- | Write an indented string to the current LLVM output file handle.
llvmPutStrLnIndented :: String -> LLVM ()
llvmPutStrLnIndented str = llvmPutStrLn $ "  " ++ str


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


-- | Set the set of variables that need to be renamed to convert to SSA.
-- LPVM is a (dynamic) single assignment language, but LLVM demands static
-- single assignment.  We generate LPVM that is in SSA form, except for output
-- parameters, so here we rename all output parameters as they are assigned,
-- and then use the new names when we return the outputs.
setRenaming :: Set PrimVarName -> LLVM ()
setRenaming vars = modify $ \s -> s {toRename = vars}


-- | The LLVM name for a variable we are about to assign.  If this is one of the
-- output parameters, rename it, otherwise leave it alone, and in either case,
-- transform it to an LLVM local variable name.
varToWrite :: PrimVarName -> LLVM LLVMLocal
varToWrite v = do
    mustRename <- Set.member v <$> gets toRename
    if mustRename then do
        tmp <- makeTemp
        modify $ \s -> s { newNames = Map.insert v tmp $ newNames s }
        return $ llvmLocalName tmp
    else return $ llvmLocalName v
 

-- | The LLVM name for a variable we are about to read.
varToRead :: PrimVarName -> LLVM LLVMLocal
varToRead v = llvmLocalName . fromMaybe v . Map.lookup v <$> gets newNames


-- | Generate LLVM code for the specified module, based on its LPVM code, and
-- write it to the specified file handle.
writeLLVM :: Handle -> ModSpec -> Bool -> Compiler ()
writeLLVM handle modSpec withLPVM = do
    reenterModule modSpec
    logMsg LLVM $ "*** Generating LLVM for module " ++ showModSpec modSpec
    logWrapWith '-' . show <$> getModule id
    flip execStateT (initLLVMState handle) $ do
        writeAssemblyPrologue
        writeAssemblyConstants
        writeAssemblyGlobals
        writeAssemblyExterns
        writeAssemblyProcs
        when withLPVM writeAssemblyExports
    logMsg LLVM $ "*** Finished generating LLVM for " ++ showModSpec modSpec
    reexitModule


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
writeAssemblyConstants = return ()


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
    (res', ty) <-
        mapSnd (trustFromJust $ "defGlobalResource " ++ show res)
        <$> lift (canonicaliseResourceSpec Nothing "newLLVMModule" res)
    ifM (lift $ typeIsPhantom ty)
        (return ())
        (do
            llvmRep <- llvmTypeRep <$> typeRep ty
            llvmPutStrLn $ llvmGlobalName (makeGlobalResourceName res')
                    ++ " = global " ++ llvmRep ++ " undef")


----------------------------------------------------------------------------
-- Writing extern declarations
----------------------------------------------------------------------------

-- | Write out extern declarations for all procs and resources imported from
-- other modules and used by this one.
writeAssemblyExterns :: LLVM ()
writeAssemblyExterns = return ()


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
    mapM_ (uncurry (writeAssemblyProc mod)) procs


-- | Generate and write out the LLVM code for the given proc with its proc
-- number.
writeAssemblyProc :: ModSpec -> ProcDef -> Int -> LLVM ()
writeAssemblyProc mod def procNum =
    case procImpln def of
        ProcDefPrim {procImplnProcSpec=pspec, procImplnProto=proto,
                     procImplnBody=body, procImplnSpeczBodies=specz} -> do
            let name = llvmProcName pspec
            (ins,outs) <- partitionParams $ primProtoParams proto
            setRenaming $ Set.fromList $ primParamName <$> outs
            returnType <- llvmReturnType $ List.map primParamType outs
            llParams <- mapM llvmParameter ins
            modify $ \s -> s {tmpCounter = procTmpCount def}
            llvmBlankLine
            llvmPutStrLn $
                "define external fastcc " ++ returnType ++ " "
                    ++ name ++ "(" ++ intercalate ", " llParams ++ ")"
                    ++ " alwaysinline {"
            writeAssemblyBody outs body
            llvmPutStrLn "}"
            -- XXX need to write out specialisations.
        _ -> shouldnt $ "Generating assembly code for uncompiled proc "
                        ++ showProcName (procName def)


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
buildTuple :: LLVMType -> LLVMLocal -> Int -> [PrimParam] -> LLVM LLVMLocal
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

-- | Generate and write out the LLVM code for an LPVM body
writeAssemblyBody :: [PrimParam] -> ProcBody -> LLVM ()
writeAssemblyBody outs ProcBody{bodyPrims=prims, bodyFork=fork} = do
    mapM_ (placedApply writeAssemblyPrim) prims
    case fork of
        NoFork -> writeAssemblyReturn outs
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


-- | Generate and write out the LLVM code for a single LPVM prim
writeAssemblyPrim :: Prim -> OptPos -> LLVM ()
writeAssemblyPrim (PrimCall _ proc _ args _) pos = do
    writeWybeCall proc args pos
writeAssemblyPrim (PrimHigher _ fn _ args) pos = do
    llvmPutStrLnIndented $ "call " ++ show fn ++ show args
writeAssemblyPrim (PrimForeign "llvm" op flags args) pos = do
    writeLLVMCall op flags args pos
writeAssemblyPrim (PrimForeign "lpvm" op flags args) pos = do
    writeLPVMCall op flags args pos
writeAssemblyPrim (PrimForeign "c" cfn flags args) pos = do
    writeCCall cfn flags args pos
writeAssemblyPrim (PrimForeign lang op flags args) pos = do
    shouldnt $ "unknown foreign language " ++ lang
                ++ " in instruction at " ++ show pos


-- | Generate and write out an LLVM if-then-else (switch on an i1 value)
writeAssemblyIfElse :: [PrimParam] -> PrimVarName -> ProcBody -> ProcBody
                    -> LLVM ()
writeAssemblyIfElse outs v thn els = do
    llvar <- varToRead v
    [thnlbl,elslbl] <- freshLables ["if.then.","if.else."]
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
    llvar <- varToRead v
    let prefixes0 = ["case."++show n++".switch." | n <- [0..length cases]]
    (dfltLabel:labels) <- freshLables $ "default.switch." : prefixes0
    let llType = llvmTypeRep rep
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


-- | Generate a Wybe proc call instruction
writeWybeCall :: ProcSpec -> [PrimArg] -> OptPos -> LLVM ()
writeWybeCall wybeProc args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    outTy <- llvmReturnType $ List.map argType outs
    llvmStoreResult outs $
        "tail call fastcc " ++ outTy ++ " " ++ llvmProcName wybeProc ++ argList


-- | Generate a native LLVM instruction
writeLLVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLLVMCall op flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmInstrArgumentList ins
    case ins of
        [_] ->
            if op == "move" then do
                outTy <- llvmTypeRep <$> typeRep (argVarType $ head outs)
                llvmStoreResult outs $
                    "bitcast " ++ argList ++ " to " ++ outTy
            else if op `Map.member` llvmMapUnop && not (List.null outs) then do
                outTy <- llvmTypeRep <$> typeRep (argVarType $ head outs)
                llvmStoreResult outs $ op ++ " " ++ argList ++ "to " ++ outTy
            else shouldnt $ "unknown unary llvm op " ++ op
        [_,_] -> do
            let instr =
                    fst3 $ trustFromJust ("unknown binary llvm op " ++ op)
                    $ Map.lookup op llvmMapBinop
            llvmStoreResult outs $ instr ++ " " ++ argList
        _ -> shouldnt $ "unknown llvm op " ++ op ++ " (arity "
                         ++ show (length ins) ++ ")"


-- | Generate LPVM (memory management) instruction
writeLPVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
-- writeLPVMCall "alloc" [] [sz,noEscape,out] pos =
writeLPVMCall "alloc" [] args@[sz,out] pos = do
    marshalledCCall "wybe_malloc" [] [sz,out] ["int","pointer"] pos
writeLPVMCall op flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    llvmStoreResult outs $ "LPVM " ++ op ++ argList

-- | Generate C function call
writeCCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeCCall cfn flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    outTy <- llvmReturnType $ List.map argType outs
    llvmStoreResult outs $ "call " ++ outTy ++ " " ++ llvmGlobalName cfn
                            ++ argList


-- | Generate C function call with inputs and outputs type converted as needed.
marshalledCCall :: ProcName -> [Ident] -> [PrimArg] -> [String] -> OptPos
                -> LLVM ()
marshalledCCall cfn flags args ctypes pos = do
    (ins,outs) <- partitionArgsWithTypes $ zip args ctypes
    argList <- llvmStringArgList <$> mapM (uncurry marshallArgument) ins
    let instr = llvmGlobalName cfn ++ argList
    case outs of
        [] -> llvmPutStrLnIndented $ "call void " ++ instr
        [(out,cType)] -> marshallCallResult out cType instr
        _ -> shouldnt "C function call with multiple outputs"


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
    modBS <- lift $ encodeModule m
    declareByteStringConstant (showModSpec m) modBS $ Just "__LPVM,__lpvm"


----------------------------------------------------------------------------
-- Support code
----------------------------------------------------------------------------

-- | Emit an LLVM declaration for a string constant.
declareStringConstant :: LLVMName -> String -> LLVM ()
declareStringConstant name str = do
    llvmPutStrLn $ "@\"" ++ name ++ "\" = local_unnamed_addr constant ["
        ++ show (length str) ++ " x i8] c"
        ++ show str


-- | Emit an LLVM declaration for a string constant represented as a ByteString.
declareByteStringConstant :: LLVMName -> BL.ByteString -> Maybe String -> LLVM ()
declareByteStringConstant name str section = do
    llvmPutStrLn $ "@\"" ++ name ++ "\" = local_unnamed_addr constant ["
        ++ show (BL.length str) ++ " x i8] c"
        ++ show str
        ++ maybe "" ((", section "++) . show) section


-- | Return the representation for the specified type
typeRep :: TypeSpec -> LLVM TypeRepresentation
typeRep ty =
    trustFromJust ("lookupTypeRepresentation of unknown type " ++ show ty)
      <$> lift (lookupTypeRepresentation ty)


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
llvmTypeRep Address         = llvmTypeRep $ Bits wordSize


-- | The LLVM return type for proc with the specified list of output type specs.
llvmReturnType :: [TypeSpec] -> LLVM LLVMType
llvmReturnType [] = return "void"
llvmReturnType [ty] = llvmTypeRep <$> typeRep ty
llvmReturnType tys = do
    lltys <- mapM ((llvmTypeRep <$>) . typeRep) tys
    return $ "{" ++ intercalate ", " lltys ++ "}"


-- | The LLVM parameter declaration for the specified Wybe input parameter as a
-- pair of LLVM type and variable name
llvmParameter :: PrimParam -> LLVM String
llvmParameter PrimParam{primParamName=name, primParamType=ty} = do
    let llname = llvmLocalName name
    lltype <- llvmTypeRep <$> typeRep ty
    return $ lltype ++ " " ++ llname


-- | The LLVM translation of the specified call instruction argument list
llvmArgumentList :: [PrimArg] -> LLVM String
llvmArgumentList inputs = llvmStringArgList <$> mapM llvmArgument inputs


llvmStringArgList :: [String] -> String
llvmStringArgList = ('(':). (++")") . intercalate ", "



-- | The LLVM translation of the specified LLVM instruction argument list
llvmInstrArgumentList :: [PrimArg] -> LLVM String
llvmInstrArgumentList [] = return ""
llvmInstrArgumentList inputs@(in1:_) = do
    lltype <- llvmTypeRep <$> typeRep (argType in1)
    argsString <- intercalate ", " <$> mapM llvmValue inputs
    return $ lltype ++ " " ++ argsString


-- | Write the LLVM translation of the specified output argument list as target
-- for the specified instruction.  For multiple outputs, we must unpack a tuple.
llvmStoreResult :: [PrimArg] -> String -> LLVM ()
llvmStoreResult [] instr = llvmPutStrLn instr
llvmStoreResult [ArgVar{argVarName=varName}] instr = do
    llVar <- varToRead varName
    llvmPutStrLnIndented $ llVar ++ " = " ++ instr
llvmStoreResult multiOuts instr = do
    tuple <- llvmLocalName <$> makeTemp
    retType <- llvmReturnType $ argVarType <$> multiOuts
    llvmPutStrLnIndented $ tuple ++ " = " ++ instr
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
    outTypeRep <- typeRep $ argType outArg
    let instr' = "call " ++ llvmTypeRep inTypeRep ++ " " ++ instr 
    if inTypeRep == outTypeRep then llvmStoreResult [outArg] instr'
    else do
        tmp <- makeTemp
        -- XXX should call llvmStoreResult, but we don't have a wybe type for
        -- the C function output
        llVar <- varToWrite tmp
        let llVal = llvmLocalName tmp
        llvmPutStrLnIndented $ llVar ++ " = " ++ instr'
        typeConvert outTypeRep varName inTypeRep llVal
marshallCallResult outArg inTypeRep instr =
    shouldnt $ "Can't marshall result into non-variable " ++ show outArg


-- | Write an LLVM instruction to unpack one argument from a tuple.
-- instruction looks like:  %var = extractvalue {i64, i1} %0, 0
unpackArg :: LLVMType -> LLVMLocal -> PrimArg -> Int -> LLVM ()
unpackArg typ tuple ArgVar{argVarName=varName} argNum = do
    llvmPutStrLnIndented $ llvmLocalName varName ++ " = extractvalue " ++ typ
                            ++ tuple ++ ", " ++ show argNum
unpackArg _ _ outArg _ =
    shouldnt $ "non-variable output argument " ++ show outArg


-- | Marshall data being passed to C code.  Emits code to transform the argument
-- to the expected format for C code, and returns the llvm argument to actually
-- pass to the C function.
marshallArgument :: PrimArg -> String -> LLVM String
marshallArgument arg cType = do
    let outTypeRep = trustFromJust
            ("marshalling argument with unknown C type " ++ cType)
            $ cTypeRepresentation cType
    inTypeRep <- typeRep $ argType arg
    if inTypeRep == outTypeRep then llvmArgument arg
    else do
        tmp <- makeTemp
        llVal <- llvmValue arg
        typeConvert outTypeRep tmp inTypeRep llVal
        return $ llvmTypeRep outTypeRep ++ " " ++ llvmLocalName tmp


-- | The LLVM argument for the specified PrimArg as an LLVM type and value
llvmArgument :: PrimArg -> LLVM String
llvmArgument arg = do
    lltype <- llvmTypeRep <$> typeRep (argType arg)
    llVal <- llvmValue arg
    return $ lltype ++ " " ++ llVal


-- | A PrimArg as portrayed in LLVM code
llvmValue :: PrimArg -> LLVM String
llvmValue ArgVar{argVarName=var} = varToRead var
llvmValue (ArgInt val _) = return $ show val
llvmValue (ArgFloat val _) = return $ show val
llvmValue (ArgString _ val _) = return $ show val -- XXX need to make a global constant
llvmValue (ArgChar val _) = return $ show val
llvmValue (ArgClosure _ val _) = return $ show val -- XXX not sure what to do
llvmValue (ArgGlobal val _) = return $ show val    -- XXX not sure what to do
llvmValue (ArgUnneeded val _) = return $ show val  -- XXX not sure what to do
llvmValue (ArgUndef _) = return "undef"


-- | Emit an instruction to convert the specified input argument with the
-- specified input type representation to the specified output variable with its
-- specified type representation.
typeConvert :: TypeRepresentation -> PrimVarName
            -> TypeRepresentation -> String -> LLVM ()
typeConvert outTypeRep outVar inTypeRep llVal = do
    llVar <- varToWrite outVar
    let op = typeConvertOp inTypeRep outTypeRep
    writeConvertOp op inTypeRep llVal outTypeRep llVar


-- | Same as typeConvert, except that the input and output are already converted
-- to LLVM representation ready to be written out.
typeConvertOp inTypeRep outTypeRep
    | outTypeRep == inTypeRep = 
        shouldnt $ "no-op type conversion to and from " ++ show inTypeRep
typeConvertOp (Bits n) Address = "inttoptr"
typeConvertOp (Signed n) Address = "inttoptr"
typeConvertOp rep Address =
    shouldnt $ "can't convert from " ++ show rep ++ " to address"
typeConvertOp Address (Bits n) = "ptrtoint"
typeConvertOp Address (Signed n) = "ptrtoint"
typeConvertOp Address rep =
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
typeConvertOp repIn repOut =
    shouldnt $ "Don't know how to convert from " ++ show repIn
                 ++ " to " ++ show repOut


-- | Write out an LLVM instruction to convert the specified value with its type
-- to the specified variable with its type.  The required conversion operator is
-- provided.
writeConvertOp :: String -> TypeRepresentation -> String
               -> TypeRepresentation -> String -> LLVM ()
writeConvertOp opName fromTy fromVal repOut toVar =
    llvmPutStrLnIndented $ toVar ++ " = " ++ opName ++ " "
                            ++ llvmTypeRep fromTy ++ " "++ fromVal
                            ++ " to " ++ llvmTypeRep repOut


-- | The LLVM name for a Wybe proc.
llvmProcName :: ProcSpec -> LLVMName
llvmProcName pspec = llvmGlobalName $ show pspec


-- | Make a suitable LLVM name for a global variable or constant.  We prefix it
-- with @, enclose the rest in quotes, and escape any special characters.
llvmGlobalName :: String -> LLVMName
llvmGlobalName s = '@' : show s


-- | Make a suitable LLVM name for a local variable.  We prefix it
-- with %, enclose the rest in quotes, and escape any special characters.
llvmLocalName :: PrimVarName -> LLVMLocal
llvmLocalName varName =
    "%\"" ++ show varName ++ "\""


-- | Make an LLVM reference to the specified label.
llvmLableName :: String -> String
llvmLableName varName = "label %\"" ++ varName ++ "\""


-- | Split parameter list into separate list of inputs and outputs, ignoring
--   any phantom parameters
-- XXX This ignores FlowOutByReference and FlowTakeReference PrimFlows.
partitionParams :: [PrimParam] -> LLVM ([PrimParam],[PrimParam])
partitionParams params = do
    realParams <- lift $ filterM (notM . typeIsPhantom . primParamType) params
    return ( List.filter ((==FlowIn) . primParamFlow) realParams
           , List.filter ((==FlowOut) . primParamFlow) realParams)


-- | Split argument list into separate list of inputs and outputs
-- XXX This ignores FlowOutByReference and FlowTakeReference PrimFlows.
partitionArgs :: [PrimArg] -> LLVM ([PrimArg],[PrimArg])
partitionArgs args = do
    realArgs <- lift $ filterM (notM . argIsPhantom) args
    return ( List.filter ((==FlowIn) . argFlowDirection) realArgs
           , List.filter ((==FlowOut) . argFlowDirection) realArgs)


-- | Split argument list into separate list of inputs and outputs
-- XXX This ignores FlowOutByReference and FlowTakeReference PrimFlows.
partitionArgsWithTypes :: [(PrimArg,a)] -> LLVM ([(PrimArg,a)],[(PrimArg,a)])
partitionArgsWithTypes args = do
    realArgs <- lift $ filterM (notM . argIsPhantom . fst) args
    return ( List.filter ((==FlowIn) . argFlowDirection . fst) realArgs
           , List.filter ((==FlowOut) . argFlowDirection . fst) realArgs)

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
