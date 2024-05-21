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
import           Config
import           Options
import           Version
import           System.IO
import           Data.Map                        as Map
import           Control.Exception               (handle)
import           Control.Monad.Trans.State
import           Control.Monad.Extra
import           Control.Monad.IO.Class
import           Data.Tuple.HT

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

type LLVMType = String

-- | Generate LLVM code for the specified module, based on its LPVM code, and
-- write it to the specified file handle.
writeLLVM :: Handle -> ModSpec -> Compiler ()
writeLLVM handle modSpec = do
    reenterModule modSpec
    logLLVM $ "*** Generating LLVM for module " ++ showModSpec modSpec
    logWrapWith '-' . show <$> getModule id
    writeAssemblyPrologue handle
    writeAssemblyConstants handle
    writeAssemblyGlobals handle
    writeAssemblyExterns handle
    writeAssemblyProcs handle
    writeAssemblyExports handle
    logLLVM $ "*** Finished generating LLVM for " ++ showModSpec modSpec
    reexitModule


-- | Write out some boilerplate at the beginning of a generated .ll file.
-- Included are a comment identifying the source of the file and the information
-- required for the file to be compilable.
writeAssemblyPrologue :: Handle -> Compiler ()
writeAssemblyPrologue h = do
    mod <- getModule modSpec
    srcFile <- getModule modOrigin
    liftIO $ do
        hPutStrLn h $
            ";; FILE GENERATED BY wybemk "
                ++ Version.version
                ++ " (" ++ Version.gitHash
                ++ ") -- see https://github.com/pschachte/wybe"
        hPutStrLn h $ ";; Module " ++ showModSpec mod
        hPutStrLn h ""
        hPutStrLn h $ "source_filename = \"" ++ srcFile ++ "\""
        hPutStrLn h $ "target triple   = \"" ++ Version.defaultTriple ++ "\""
        hPutStrLn h ""
    return ()


-- | Write out definitions of manifest constants used in generated code for this
-- module.
writeAssemblyConstants :: Handle -> Compiler ()
writeAssemblyConstants h = return ()


-- | Write out definitions of global variables to implement the resources of
-- this module.
writeAssemblyGlobals :: Handle -> Compiler ()
writeAssemblyGlobals h = do
    resDefs <- modResources . trustFromJust "blockTransformModule"
                <$> getModule modImplementation
    let ress = concatMap Map.keys (Map.elems resDefs)
    mapM_ (globalResourceExtern h) ress


-- | Write out extern declarations for all procs and resources imported from
-- other modules and used by this one.
writeAssemblyExterns :: Handle -> Compiler ()
writeAssemblyExterns h = return ()


-- | Generate and write out the LLVM code for all the procs defined in this
-- module.
writeAssemblyProcs :: Handle -> Compiler ()
writeAssemblyProcs h = return ()


-- | Write out data needed for wybemk to compile users of this module.  This
-- includes all the declared types and other submodules, resources, interfaces
-- of all public procs, and definitions of inline public procs.
writeAssemblyExports :: Handle -> Compiler ()
writeAssemblyExports h = return ()


-- | Generate a global declaration for a resource, if necessary.
globalResourceExtern :: Handle -> ResourceSpec -> Compiler ()
globalResourceExtern h res = do
    (res', ty) <-
        mapSnd (trustFromJust $ "globalResourceExtern " ++ show res)
        <$> canonicaliseResourceSpec Nothing "newLLVMModule" res
    let global = makeGlobalResourceName res'
    ifM (typeIsPhantom ty)
        (return ())
        (declareGlobalResource h res' ty)


declareGlobalResource :: Handle -> ResourceSpec -> TypeSpec -> Compiler ()
declareGlobalResource h spec@(ResourceSpec mod nm) ty = do
    rootMod <- getModule modRootModSpec
    resRoot <- (>>= modRootModSpec) <$> getLoadingModule mod
    rep <- llvmTypeRep <$> typeRep ty
    liftIO $ hPutStrLn h $ "@\"" ++ makeGlobalResourceName spec
            ++ "\" = external global " ++ rep
    -- XXX this may be affected by multiprocessing


typeRep :: TypeSpec -> Compiler TypeRepresentation
typeRep ty =
    trustFromJust ("llvmType applied to InvalidType or unknown type ("
                    ++ show ty ++ ")")
      <$> lookupTypeRepresentation ty


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


-- |Affix its id number to the end of each proc name
mangleProcs :: [ProcDef] -> [ProcDef]
mangleProcs ps = zipWith mangleProc ps [0..]


mangleProc :: ProcDef -> Int -> ProcDef
mangleProc def i =
    let proto = procImplnProto $ procImpln def
        s = primProtoName proto
        pname = s ++ "<" ++ show i ++ ">"
        newProto = proto {primProtoName = pname}
    in
    def {procImpln = (procImpln def){procImplnProto = newProto}}


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
