--  File     : LLVM.hs
--  Author   : Peter Schachte, based on work by Ashutosh Rishi Ranjan
--  Purpose  : Generate LLVM code from LPVM form
--  Copyright: (c) 2024 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

-- {-# LANGUAGE TupleSections #-}

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
llvmMapBinop :: Map String
                (TypeFamily, TypeRepresentation -> TypeRepresentation)
llvmMapBinop =
    Map.fromList [
            -- Integer arithmetic
            ("add",  (IntFamily, id)),
            ("sub",  (IntFamily, id)),
            ("mul",  (IntFamily, id)),
            ("udiv", (IntFamily, id)),
            ("sdiv", (IntFamily, id)),
            ("urem", (IntFamily, id)),
            ("srem", (IntFamily, id)),
            -- Integer comparisions
            ("icmp_eq",  (IntFamily, const $ Bits 1)),
            ("icmp_ne",  (IntFamily, const $ Bits 1)),
            ("icmp_ugt", (IntFamily, const $ Bits 1)),
            ("icmp_uge", (IntFamily, const $ Bits 1)),
            ("icmp_ult", (IntFamily, const $ Bits 1)),
            ("icmp_ule", (IntFamily, const $ Bits 1)),
            ("icmp_sgt", (IntFamily, const $ Bits 1)),
            ("icmp_sge", (IntFamily, const $ Bits 1)),
            ("icmp_slt", (IntFamily, const $ Bits 1)),
            ("icmp_sle", (IntFamily, const $ Bits 1)),
            -- Bitwise operations
            ("shl",  (IntFamily, id)),
            ("lshr", (IntFamily, id)),
            ("ashr", (IntFamily, id)),
            ("or",   (IntFamily, id)),
            ("and",  (IntFamily, id)),
            ("xor",  (IntFamily, id)),

            -- Floating point arithmetic
            ("fadd", (FloatFamily, id)),
            ("fsub", (FloatFamily, id)),
            ("fmul", (FloatFamily, id)),
            ("fdiv", (FloatFamily, id)),
            ("frem", (FloatFamily, id)),
            -- Floating point comparisions
            ("fcmp_eq",  (FloatFamily, const $ Bits 1)),
            ("fcmp_ne",  (FloatFamily, const $ Bits 1)),
            ("fcmp_slt", (FloatFamily, const $ Bits 1)),
            ("fcmp_sle", (FloatFamily, const $ Bits 1)),
            ("fcmp_sgt", (FloatFamily, const $ Bits 1)),
            ("fcmp_sge", (FloatFamily, const $ Bits 1))
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
        tmpCounter :: Int           -- ^ Next temp var to make for current proc
}


initLLVMState :: Handle -> LLVMState
initLLVMState h = LLVMState h 0

type LLVM = StateT LLVMState Compiler


-- | Apply some function to (access some member of) the current module from
-- within the LLVM monad.
llvmGetModule :: (Module -> a) -> LLVM a
llvmGetModule fn = lift $ getModule fn


-- | Write a newline-terminated string to the current LLVM output file handle.
llvmPutStrLn :: String -> LLVM ()
llvmPutStrLn str = do
    h <- gets fileHandle
    liftIO $ hPutStrLn h str


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
    llvmPutStrLn ""
    llvmPutStrLn $ "source_filename = \"" ++ srcFile ++ "\""
    llvmPutStrLn $ "target triple   = \"" ++ Version.defaultTriple ++ "\""
    llvmPutStrLn ""
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
writeAssemblyProc mod def procNum = do
    let name = llvmProcName mod (procName def) procNum
    let params = (content <$>) <$> procProtoParams $ procProto def
    realParams <- lift $ filterM (notM . typeIsPhantom . paramType) params
    let ins = List.filter (flowsIn . paramFlow) params
    let outs = List.filter (flowsOut . paramFlow) params
    returnType <- llvmReturnType $ List.map paramType outs
    llParams <- mapM llvmParameter ins
    modify $ \s -> s {tmpCounter = procTmpCount def}
    llvmPutStrLn ""
    llvmPutStrLn $
        "define external fastcc " ++ returnType ++ " "
            ++ name ++ "(" ++ intercalate ", " llParams ++ ")"
            ++ " alwaysinline {"
    llvmPutStrLn "}"


----------------------------------------------------------------------------
-- Writing the export information ("header" file equivalent)
----------------------------------------------------------------------------

-- | Write out data needed for wybemk to compile users of this module.  This
-- includes all the declared types and other submodules, resources, interfaces
-- of all public procs, and definitions of inline public procs, written as a
-- large constant string in the LPVM section of the file.
writeAssemblyExports :: LLVM ()
writeAssemblyExports = do
    llvmPutStrLn ""
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
llvmParameter :: Param -> LLVM String
llvmParameter Param{paramName=name, paramType=ty} = do
    let llname = llvmLocalName name
    lltype <- llvmTypeRep <$> typeRep ty
    return $ lltype ++ " " ++ llname


-- | The LLVM name for a Wybe proc.
llvmProcName :: ModSpec -> ProcName -> Int -> LLVMName
llvmProcName mod procName procNum =
    showModSpec mod ++ "." ++ procName ++ "<" ++ show procNum ++ ">"


-- | Make a suitable LLVM name for a global variable or constant.  We prefix it
-- with @, enclose the rest in quotes, and escape any special characters.
llvmGlobalName :: String -> LLVMName
llvmGlobalName s = '@' : show s


-- | Make a suitable LLVM name for a local variable.  We prefix it
-- with %, enclose the rest in quotes, and escape any special characters.
llvmLocalName :: String -> LLVMLocal
llvmLocalName s = '%' : show s

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
