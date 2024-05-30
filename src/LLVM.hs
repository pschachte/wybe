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
import           System.IO
import           Data.Map                        as Map
import           Data.List                       as List
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
        labelCounter :: Int         -- ^ Next label number to use
}


initLLVMState :: Handle -> LLVMState
initLLVMState h = LLVMState h 0 0

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


-- | Generate LLVM code for the specified module, based on its LPVM code, and
-- write it to the specified file handle.
writeLLVM :: Handle -> ModSpec -> Bool -> Compiler ()
writeLLVM handle modSpec withLPVM = do
    reenterModule modSpec
    logLLVM $ "*** Generating LLVM for module " ++ showModSpec modSpec
    logWrapWith '-' . show <$> getModule id
    flip execStateT (initLLVMState handle) $ do
        writeAssemblyPrologue
        writeAssemblyConstants
        writeAssemblyGlobals
        writeAssemblyExterns
        writeAssemblyProcs
        when withLPVM writeAssemblyExports
    logLLVM $ "*** Finished generating LLVM for " ++ showModSpec modSpec
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
    llvmPutStrLnIndented $ "ret " ++ llty ++ " " ++ llvmLocalName v
writeAssemblyReturn params = do
    -- XXX not right:  need to pack a tuple and return that
    retType <- llvmReturnType $ List.map primParamType params
    llvmPutStrLnIndented $ "ret " ++ retType
                           ++ show (List.map primParamName params)



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
                (Bits n, _, _) -> llvmPutStrLn $ "Switch " ++ show n ++ " bits"
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
    [thnlbl,elslbl] <- freshLables ["if.then.","if.else."]
    llvmPutStrLnIndented $ "br i1 " ++ llvmLocalName v
                    ++ ", " ++ llvmLableName thnlbl
                    ++ ", " ++ llvmLableName elslbl
    llvmPutStrLn $ thnlbl ++ ":"
    writeAssemblyBody outs thn
    llvmPutStrLn $ elslbl ++ ":"
    writeAssemblyBody outs els


-- | Generate a Wybe proc call instruction
writeWybeCall :: ProcSpec -> [PrimArg] -> OptPos -> LLVM ()
writeWybeCall wybeProc args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    outTy <- llvmReturnType $ List.map argType outs
    llvmPutStrLnIndented $ llvmStoreResult outs ++ "tail call fastcc "
                    ++ outTy ++ " " ++ llvmProcName wybeProc ++ argList


-- | Generate a native LLVM instruction
writeLLVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLLVMCall op flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmInstrArgumentList ins
    case ins of
        [_] ->
            if op == "move" then do
                outTy <- llvmTypeRep <$> typeRep (argVarType $ head outs)
                llvmPutStrLnIndented $ llvmStoreResult outs ++
                    "bitcast " ++ argList ++ " to " ++ outTy
            else if op `member` llvmMapUnop && not (List.null outs) then do
                outTy <- llvmTypeRep <$> typeRep (argVarType $ head outs)
                llvmPutStrLnIndented $ llvmStoreResult outs ++ op ++ " "
                                        ++ argList ++ "to " ++ outTy
            else shouldnt $ "unknown unary llvm op " ++ op
        [arg1,_] -> do
            let instr =
                    fst3 $ trustFromJust ("unknown binary llvm op " ++ op)
                    $ Map.lookup op llvmMapBinop
            llvmPutStrLnIndented $ llvmStoreResult outs ++ instr ++ " "
                                    ++ argList
        args -> shouldnt $ "unknown llvm op " ++ op ++ " (arity "
                         ++ show (length ins) ++ ")"


-- | Generate LPVM (memory management) instruction
writeLPVMCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeLPVMCall op flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    llvmPutStrLnIndented $ "LPVM: " ++ llvmStoreResult outs ++ op ++ argList

-- | Generate C function call
writeCCall :: ProcName -> [Ident] -> [PrimArg] -> OptPos -> LLVM ()
writeCCall cfn flags args pos = do
    (ins,outs) <- partitionArgs args
    argList <- llvmArgumentList ins
    outTy <- llvmReturnType $ List.map argType outs
    llvmPutStrLnIndented $ llvmStoreResult outs ++ "call " ++ outTy ++ " "
                            ++ llvmGlobalName cfn ++ argList


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
llvmArgumentList inputs =
    ('(':). (++")") . intercalate ", " <$> mapM llvmArgument inputs


-- | The LLVM translation of the specified LLVM instruction argument list
llvmInstrArgumentList :: [PrimArg] -> LLVM String
llvmInstrArgumentList [] = return ""
llvmInstrArgumentList inputs@(in1:_) = do
    lltype <- llvmTypeRep <$> typeRep (argType in1)
    let argsString = intercalate ", " $ List.map llvmValue inputs
    return $ lltype ++ " " ++ argsString


-- | The LLVM translation of the specified output argument list
llvmStoreResult :: [PrimArg] -> String
llvmStoreResult [] = ""
llvmStoreResult [ArgVar{argVarName=varName}] =
    llvmLocalName varName ++ " = "
llvmStoreResult multiOuts =
    "(" ++ intercalate ", " (show <$> multiOuts) ++ ") = "

-- | The LLVM argument for the specified PrimArg as an LLVM type and value
llvmArgument :: PrimArg -> LLVM String
llvmArgument arg = do
    lltype <- llvmTypeRep <$> typeRep (argType arg)
    return $ lltype ++ " " ++ llvmValue arg


-- | A PrimArg as portrayed in LLVM code
llvmValue :: PrimArg -> String
llvmValue ArgVar{argVarName=var} = llvmLocalName var
llvmValue (ArgInt val _) = show val
llvmValue (ArgFloat val _) = show val
llvmValue (ArgString _ val _) = show val -- XXX need to make a global constant
llvmValue (ArgChar val _) = show val
llvmValue (ArgClosure _ val _) = show val -- XXX not sure what to do
llvmValue (ArgGlobal val _) = show val    -- XXX not sure what to do
llvmValue (ArgUnneeded val _) = show val  -- XXX not sure what to do
llvmValue (ArgUndef _) = "undef"


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

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the Compiler monad to LLVM.
logLLVM :: String -> Compiler ()
logLLVM = logMsg LLVM


-- | Log with a wrapping line of replicated characters above and below.
logWrapWith :: Char -> String -> Compiler ()
logWrapWith ch s = do
    logMsg LLVM (replicate 65 ch)
    logMsg LLVM s
    logMsg LLVM (replicate 65 ch)
