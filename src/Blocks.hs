{-# OPTIONS -XTupleSections #-}
--  File     : Blocks.hs
--  RCS      : $Id$
--  author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

module Blocks (concatLLVMASTModules, blockTransformModule
                -- newMainModule
              ) where

import           AST
import           ASTShow
import           BinaryFactory                   ()
import           Codegen
import           Config                          (wordSize, wordSizeBytes)
import           Util                            (maybeNth)
import           Control.Monad
import           Control.Monad.Trans             (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Data.Char                       (ord)
import           Data.List                       as List
import           Data.Map                        as Map
import qualified Data.Set                        as Set
import           Data.Word                       (Word32)
import           Data.Maybe                      (fromJust)
import qualified LLVM.AST                        as LLVMAST
import qualified LLVM.AST.Constant               as C
import qualified LLVM.AST.Float                  as F
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Global                 as G
import           LLVM.AST.Instruction
import qualified LLVM.AST.IntegerPredicate       as IP
import           LLVM.AST.Operand                hiding (PointerType)
import           LLVM.AST.Type
import           LLVM.AST.Typed

-- import           LLVM.PrettyPrint
import qualified Data.ByteString                 as BS
import qualified Data.ByteString.Char8           as B8
import qualified Data.ByteString.Lazy            as BL
import qualified Data.ByteString.Short           as BSS
import           Options                         (LogSelection (Blocks))
import           Unsafe.Coerce

-- | Holds information on the LLVM representation of the LPVM procedure.
data ProcDefBlock =
    ProcDefBlock { blockProto   :: PrimProto
                 , blockDef     :: LLVMAST.Definition
                 , blockExterns :: [LLVMAST.Definition]
                 } deriving (Show, Eq)


-- | Transofrorm the module's procedures (in LPVM by now) into LLVM function
-- definitions. A LLVMAST.Module is built up using these global definitions
-- and then stored in the modLLVM field of 'ModuleImplementation'.
-- Before translation of ProcDefs, all the prototypes of the ProcDef's LPVM
-- form is collected, along with the same for all the imported modules.
-- This is passed along to the codegen monad so that Primitive calls to these
-- procedures can the prototype checked (match and eliminate unneeded
-- arguments in cgen.)
blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule thisMod =
    do reenterModule thisMod
       logBlocks $ "*** Translating Module: " ++ showModSpec thisMod
       modRec <- getModule id
       modFile <- getModule modSourceFile
       logWrapWith '-' $ show modRec
       procs <- getModuleImplementationField (Map.elems . modProcs)
       -- Collect all procedure prototypes in the module
       let protos = List.map extractLPVMProto (concat procs)
       --------------------------------------------------
       -- Collect prototypes of imported modules
       imports <- getModuleImplementationField (keys . modImports)
       importProtos <- mapM getPrimProtos
                         (List.filter (not . isStdLib) imports)
       let allProtos = protos ++ concat importProtos

       logBlocks $ "Prototypes:\n\t"
                         ++ intercalate "\n\t" (List.map show allProtos)
       --------------------------------------------------
       -- Listing all known types
       knownTypesSet <- Map.elems <$>
                         getModuleImplementationField modKnownTypes
       let knownTypes = concatMap Set.toList knownTypesSet
       trs <- mapM llvmType knownTypes
       -- typeList :: [(TypeSpec, LLVMAST.Type)]
       let typeList = zip knownTypes trs
       -- log the assoc list typeList
       logWrapWith '.' $ "Known Types:\n" ++ (intercalate "\n" $
           List.map (\(a,b) -> show a ++ ": " ++ show b) typeList)

       --------------------------------------------------
       -- Name mangling
       let emptyFilter = List.filter (not . emptyProc)
       let mangledProcs = concat $ mangleProcs <$> procs

       --------------------------------------------------
       -- Translate
       procBlocks <- evalTranslation 0 $
         mapM (translateProc allProtos) $ emptyFilter mangledProcs
       --------------------------------------------------
       -- Init LLVM Module and fill it
       let llmod = newLLVMModule (showModSpec thisMod) modFile procBlocks
       updateImplementation (\imp -> imp { modLLVM = Just llmod })
       logBlocks $ "*** Translated Module: " ++ showModSpec thisMod
       modRec' <- getModule id
       logWrapWith '-' $ show modRec'
       _ <- reexitModule
       logBlocks $ "*** Exiting Module " ++ showModSpec thisMod ++ " ***"


-- -- |Affix its id number to the end of each proc name
mangleProcs :: [ProcDef] -> [ProcDef]
mangleProcs ps = zipWith mangleProc ps [0..]


mangleProc :: ProcDef -> Int -> ProcDef
mangleProc def i =
    let (ProcDefPrim proto body analysis) = procImpln def
        s = primProtoName proto
        pname = s ++ "<" ++ show i ++ ">"
        newProto = proto {primProtoName = pname}
    in  def {procImpln = ProcDefPrim newProto body analysis}



-- mangleProcs :: [ProcDef] -> [ProcDef]
-- mangleProcs ps = changeNameWith nameMap ps
--   where
--     nameMap = buildNameMap ps


-- changeNameWith :: [(String, Int)] -> [ProcDef] -> [ProcDef]
-- changeNameWith [] [] = []
-- changeNameWith ((s,i):ns) (p:ps) =
--     let (ProcDefPrim proto body) = procImpln p
--         pname = s ++ "<" ++ show i ++ ">"
--         newProto = proto {primProtoName = pname}
--         newImpln = ProcDefPrim newProto body
--     in p {procImpln = newImpln} : changeNameWith ns ps
-- changeNameWith _ _ = shouldnt "Incorrect name map used for mangling."

-- buildNameMap :: [ProcDef] -> [(String, Int)]
-- buildNameMap ps = List.foldl reduceNameMap [] procNames
--     where
--       procNames = List.map pullDefName ps

-- reduceNameMap :: [(String, Int)] -> String -> [(String, Int)]
-- reduceNameMap namemap name =
--     case List.lookup name namemap of
--         Just val -> namemap ++ [(name, val + 1)]
--         Nothing  -> namemap ++ [(name, 0)]


-- pullDefName :: ProcDef -> String
-- pullDefName p =
--     let (ProcDefPrim proto _) = procImpln p
--     in primProtoName proto


-- | Extract the LPVM compiled primitive from the procedure definition.
extractLPVMProto :: ProcDef -> PrimProto
extractLPVMProto procdef =
    case procImpln procdef of
       (ProcDefPrim proto _ _) -> proto
       uncompiled ->
         shouldnt $ "Proc reached backend uncompiled: " ++ show uncompiled

-- | Go into a (compiled) Module and pull out the PrimProto implementation
-- of all ProcDefs in the module implementation.
getPrimProtos :: ModSpec -> Compiler [PrimProto]
getPrimProtos modspec = do
    (_, procs) <- (unzip . Map.toList . modProcs) <$>
                  getLoadedModuleImpln modspec
    let protos = List.map extractLPVMProto (concat procs)
    return protos

-- | Filter for avoiding the standard library modules
isStdLib :: ModSpec -> Bool
isStdLib []    = False
isStdLib (m:_) = m == "wybe"



-- | Predicate to test for procedure definition with an empty body.
emptyProc :: ProcDef -> Bool
emptyProc p = case procImpln p of
  ProcDefSrc pps       -> List.null pps
  ProcDefPrim _ body _ -> List.null $ bodyPrims body



-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). Each ProcDef is converted into a Global
-- Definition in a LLVM Module by translating it's primitives.  Translated
-- procedures (ProcDefBlocks ...) can optionally have a list of extern
-- declarations (which are also global definitions) if any primitive is going
-- to call some foreign function (mostly C).  Translated procedures will also
-- require some global variable/constant declarations which is represented as
-- G.Global values in the neededGlobalVars field of LLVMCompstate. All in all,
-- externs and globals go on the top of the module.
translateProc :: [PrimProto] -> ProcDef -> Translation ProcDefBlock
translateProc modProtos proc = do
  startCount <- getCount
  (block, endCount) <- lift $ do
    modspec <- getModuleSpec
    let def@(ProcDefPrim proto body _) = procImpln proc
    logBlocks $ "\n" ++ replicate 70 '=' ++ "\n"
    logBlocks $ "In Module: " ++ showModSpec modspec
      ++ ", creating definition of: "
    logBlocks $ show def ++ "\n" ++ replicate 50 '-' ++ "\n"
    -- Codegen
    codestate <- execCodegen startCount modProtos (doCodegenBody proto body)
    let pname = primProtoName proto
    logBlocks $ show $ externs codestate
    exs <- mapM declareExtern $ externs codestate
    let globals = List.map LLVMAST.GlobalDefinition $ globalVars codestate
    let body' = createBlocks codestate
    lldef <- makeGlobalDefinition pname proto body'
    logBlocks $ show lldef
    let block = ProcDefBlock proto lldef (exs ++ globals)
    let endCount = Codegen.count codestate
    return (block, endCount)
  putCount endCount
  return block


-- | Create LLVM's module level Function Definition from the LPVM procedure
-- prototype and its body as a list of BasicBlock(s). The return type of such
-- a definition is decided based on the Ouput parameter of the procedure, or
-- is made to be phantom.
makeGlobalDefinition :: String -> PrimProto
                     -> [LLVMAST.BasicBlock]
                     -> Compiler LLVMAST.Definition
makeGlobalDefinition pname proto bls = do
    modName <- fmap showModSpec getModuleSpec
    let params = List.filter (not . paramIsPhantom) (primProtoParams proto)
        label0 = modName ++ "." ++ pname
        -- For the top-level main program
        isMain = label0 == ".<0>"
        label  = if isMain then "main" else label0
        inputs = List.filter isInputParam params
    fnargs <- mapM makeFnArg inputs
    retty <- if isMain then return int_t else primOutputType params
    return $ globalDefine retty label fnargs bls


-- | Predicate to check if a primitive's parameter is of input flow (input)
-- and the param is needed (inferred by it's param info field)
isInputParam :: PrimParam -> Bool
isInputParam p = primParamFlow p == FlowIn && paramNeeded p


-- | Convert a primitive's input parameter to LLVM's Definition parameter.
makeFnArg :: PrimParam -> Compiler (Type, LLVMAST.Name)
makeFnArg param = do
    ty <- llvmType $ primParamType param
    let nm = LLVMAST.Name $ toSBString $ show $ primParamName param
    return (ty, nm)

-- | Open the Out parameter of a primitive (if there is one) into it's
-- inferred 'Type' and name.
primOutputType :: [PrimParam] -> Compiler Type
primOutputType params = do
    let outputs = List.filter isOutputParam params
    case outputs of
        [] -> return void_t
        [o] -> llvmType $ primParamType o
        _ -> struct_t <$> mapM (llvmType . primParamType) outputs


isOutputParam :: PrimParam -> Bool
isOutputParam p = not (isInputParam p || paramIsPhantom p) &&
    paramNeeded p


paramNeeded :: PrimParam -> Bool
paramNeeded = not . paramInfoUnneeded . primParamInfo

----------------------------------------------------------------------------
-- Body Compilation                                                       --
----------------------------------------------------------------------------

-- | Compile a Procedure Body containing primitives to a list of llvm basic
-- blocks, the operand generated by the last block will be the terminitor's
-- emitted value. The parameters of the procedure will all enter the local
-- scope by being referenced on the symbol table (including the output
-- parameter). This is useful in leveraging the existing SSA form in the LPVM
-- rather than generating more unique names. Mostly all primitive's variable
-- arguments can be resolved from the symbol table.  Each procedure might also
-- need some module level extern declarations and global constants which are
-- pulled and recorded, to be defined later when the whole module is built.
-- | Generate LLVM instructions for a procedure.
doCodegenBody :: PrimProto -> ProcBody -> Codegen ()
doCodegenBody proto body =
    do let params = primProtoParams proto
       entry <- addBlock entryBlockName
       -- Start with creation of blocks and adding instructions to it
       setBlock entry
       mapM_ assignParam $ List.filter (not . isOutputParam) params
       mapM_ preassignOutput $ List.filter isOutputParam params
       codegenBody proto body   -- Codegen on body prims
       return ()


-- XXX not using
-- | Generate code for returning integer exit code at the end main
-- function.
-- mainReturnCodegen :: Codegen ()
-- mainReturnCodegen = do
--     ptr <- instr (ptr_t int_t) (alloca int_t)
--     let retcons = cons (C.Int 32 0)
--     store ptr retcons
--     ret (Just retcons)
--     return ()


-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table. Don't assign if phantom.
assignParam :: PrimParam -> Codegen ()
assignParam p =
    do let ty = primParamType p
       unless (typeIsPhantom ty || paramInfoUnneeded (primParamInfo p))
         $ do let nm = show (primParamName p)
              llty <- lift $ llvmType ty
              assign nm (localVar llty nm)


-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table. Don't assign if phantom.
preassignOutput :: PrimParam -> Codegen ()
preassignOutput p =
    do let ty = primParamType p
       let nm = show (primParamName p)
       llty <- lift $ llvmType ty
       assign nm $ cons $ C.Undef llty


-- | Retrive or build the output operand from the given parameters.
-- For no valid ouputs, return Nothing
-- For 1 single output, retrieve it's assigned operand from the symbol
-- table, and for multiple ouputs, generate code for creating an valid
-- structure, pack the operands into it and return it.
buildOutputOp :: [PrimParam] -> Codegen (Maybe Operand)
buildOutputOp params = do
    let outParams = List.filter isOutputParam params
    -- outputsMaybe <- mapM (getVarMaybe . show . primParamName) outParams
    -- let outputs = catMaybes outputsMaybe
    logCodegen $ "OutParams: " ++ show outParams
    outputs <- mapM (getVar . show . primParamName) outParams
    logCodegen $ "Built outputs from symbol table: " ++ show outputs

    case outputs of
        -- * No valid output
        []       -> return Nothing
        -- * single output case
        [single] -> return $ Just single
        -- * multiple output case
        _        -> Just <$> structPack outputs

-- | Pack operands into a structure through a sequence of insertvalue
-- instructions.
structPack :: [Operand] -> Codegen Operand
structPack ops = do
    let opTypes = List.map operandType ops
    let strType = struct_t opTypes
    let strCons = cons $ C.Undef strType
    sequentialInsert ops strType strCons 0

-- | Helper for structInsert to properly and sequentially index each
-- operand into the structure.
-- | Sequentially call the insertvalue instruction to add each
-- of the given operand into a new structure type. Each call to the
-- insertvalue instruction would return a new structure which should be
-- used for the next insertion at the next index.
sequentialInsert :: [Operand] -> Type ->
                    Operand -> Word32 -> Codegen Operand
sequentialInsert [] _ finalStruct _ = return finalStruct
sequentialInsert (op:ops) ty struct i = do
    newStruct <- instr ty $ insertvalue struct op i
    sequentialInsert ops ty newStruct (i + 1)


structUnPack :: Operand -> [Type] -> Codegen [Operand]
structUnPack st tys = do
    let n = (fromIntegral $ length tys) :: Word32
    let ins = List.map (extractvalue st) [0..n-1]
    zipWithM instr tys ins


-- | Generate basic blocks for a procedure body. The first block is named
-- 'entry' by default. All parameters go on the symbol table (output too).
codegenBody :: PrimProto -> ProcBody -> Codegen (Maybe Operand)
codegenBody proto body =
    do let ps = List.map content (bodyPrims body)
       -- Filter out prims which contain only phantom arguments
       -- ops <- mapM cgen $ List.filter (not . phantomPrim) ps
       ops <- mapM cgen ps
       let params = primProtoParams proto
       case bodyFork body of
         NoFork -> do retOp <- buildOutputOp params
                      ret retOp
                      return ()
         -- NoFork -> if (primProtoName proto) == "<0>"
         --           -- Empty primitive prototype is the main function in LLVM
         --           then mainReturnCodegen
         --           else do retOp <- buildOutputOp params
         --                   ret retOp
         --                   return ()
         (PrimFork var ty _ fbody) -> codegenForkBody var fbody proto
       if List.null ops
           then return Nothing
           else return $ last ops

-- | Predicate to check whether a Prim is a phantom prim i.e Contains only
-- phantom arguments.
-- phantomPrim :: Prim -> Bool
-- phantomPrim (PrimCall _ args) = List.null $ List.filter notPhantom args
-- phantomPrim (PrimForeign _ _ _ args) =
--   List.null $ List.filter notPhantom args
-- phantomPrim (PrimTest _) = False


-- | Code generation for a conditional branch. Currently a binary split
-- is handled, which each branch returning the left value of their last
-- instruction.
codegenForkBody :: PrimVarName -> [ProcBody] -> PrimProto -> Codegen ()
-- XXX Revise this to handle forks with more than two branches using
--     computed gotos
codegenForkBody var (b1:b2:[]) proto =
    do ifthen <- addBlock "if.then"
       ifelse <- addBlock "if.else"
       testop <- getVar (show var)
       cbr testop ifthen ifelse
       let params = primProtoParams proto

       -- if.then
       preservingSymtab $ do
           setBlock ifthen
           retop <- codegenBody proto b2
           return ()

       -- if.else
       preservingSymtab $ do
           setBlock ifelse
           retop <- codegenBody proto b1
           return ()
       return ()

       -- -- if.exit
       -- setBlock ifexit
       -- phi int_t [(trueval, ifthen), (falseval, ifelse)]
codegenForkBody var _ _ =
    nyi $ "Fork on non-Boolean variable " ++ show var


-- | Translate a Primitive statement (in clausal form) to a LLVM instruction.
-- Foreign calls are resolved through numerous instruction maps which map
-- function name to a correspoinding LLVM instruction wrapper defined in
-- 'Codegen'. Two main maps are the ones containing Binary and Unary
-- instructions respectively. Adding each matched instruction to the
-- BasicBlock creates a resulting Operand.
--
-- PrimCall: CodegenState contains the list of all the Prim prototypes defined
-- in the current module and imported modules. All primitive calls' arguments
-- are position checked with the respective prototype, eliminating arguments
-- which do not eventually appear in the prototype.
cgen :: Prim -> Codegen (Maybe Operand)
cgen prim@(PrimCall pspec args) = do
    logCodegen $ "Compiling " ++ show prim
    thisMod <- lift getModuleSpec
    fileMod <- lift $ getModule modRootModSpec
    let (ProcSpec mod name _) = pspec
    -- let nm = LLVMAST.Name (showModSpec mod ++ "." ++ name)
    let nm = LLVMAST.Name $ toSBString $ show pspec
    -- Find the prototype of the pspec being called
    -- and match it's parameters with the args here
    -- and remove the unneeded ones.
    proto <- lift $ getProcPrimProto pspec
    logCodegen $ "Proto = " ++ show proto
    let filteredArgs = filterUnneededArgs proto args
    logCodegen $ "Filtered args = " ++ show filteredArgs

    -- if the call is to an external module, declare it
    unless (thisMod == mod || maybe False (`List.isPrefixOf` mod) fileMod)
        (addExtern $ PrimCall pspec filteredArgs)

    let inArgs = primInputs filteredArgs
    logCodegen $ "In args = " ++ show inArgs
    outTy <- lift $ primReturnType filteredArgs
    logCodegen $ "Out Type = " ++ show outTy
    inops <- mapM cgenArg inArgs
    logCodegen $ "Translated inputs = " ++ show inops
    let ins =
          call
          (externf (ptr_t (FunctionType outTy (typeOf <$> inops) False)) nm)
          inops
    logCodegen $ "Translated ins = " ++ show ins
    addInstruction ins filteredArgs

cgen prim@(PrimForeign "llvm" name flags args) = do
    logCodegen $ "Compiling " ++ show prim
    case (length args) of
       2 -> cgenLLVMUnop name flags args
       3 -> cgenLLVMBinop name flags args
       _ -> shouldnt $ "Instruction " ++ name ++ " not found!"

cgen prim@(PrimForeign "lpvm" name flags args) = do
    logCodegen $ "Compiling " ++ show prim
    cgenLPVM name flags args

cgen prim@(PrimForeign lang name flags args) = do
    logCodegen $ "Compiling " ++ show prim
    addExtern prim
    let inArgs = primInputs args
    let nm = LLVMAST.Name $ toSBString name
    inops <- mapM cgenArg inArgs
    -- alignedOps <- mapM makeCIntOp inops
    outty <- lift $ primReturnType args
    -- XXX this ignores lang and just uses C calling conventions for all calls
    let ins =
          call
          (externf (ptr_t (FunctionType outty (typeOf <$> inops) False)) nm)
          inops
    addInstruction ins args

cgen (PrimTest _) = shouldnt "PrimTest should have been removed before code gen"


makeCIntOp :: Operand -> Codegen Operand
makeCIntOp op
    | isIntOp op == True = do
          let opTy = operandType op
          let inBits = getBits opTy
          if inBits > 32
              then trunc op (int_c 32)
              else if inBits < 32
                   then sext op (int_c 32)
                   else return op
    | otherwise = return op

isIntOp :: Operand -> Bool
isIntOp (LocalReference (LLVMAST.IntegerType _) _) = True
isIntOp (ConstantOperand (C.Int _ _))              = True
isIntOp _                                          = False





-- | Translate a Binary primitive procedure into a binary llvm instruction,
-- add the instruction to the current BasicBlock's instruction stack and emit
-- the resulting Operand. Reads the 'llvmMapBinop' Map.  The primitive
-- arguments are split into inputs and outputs (according to their flow
-- type). The output argument is used to name and reference the resulting
-- Operand of the instruction.
cgenLLVMBinop :: ProcName -> [Ident] -> [PrimArg] -> Codegen (Maybe Operand)
cgenLLVMBinop name flags args =
    do let inArgs = primInputs args
       inOps <- mapM cgenArg inArgs
       case Map.lookup (withFlags name flags) llvmMapBinop of
         (Just f) -> let ins = (apply2 f inOps)
                     in addInstruction ins args
         Nothing -> shouldnt $ "LLVM Instruction not found: " ++ name


-- | Similar to 'cgenLLVMBinop', but for unary operations on the
-- 'llvmMapUnary'.  There is no LLVM move instruction, a special case has to
-- be made for it. The special move instruction takes one input const/var
-- param, one output variable, and assigns the output variable operand the
-- input operant at the front of the symbol table. The next time the output
-- name is referenced, the symbol table will return the latest assignment to
-- it.
cgenLLVMUnop :: ProcName -> [Ident] -> [PrimArg] -> Codegen (Maybe Operand)
cgenLLVMUnop name flags args
    | name == "move" =
        do let inArgs = primInputs args
           let outputs = primOutputs args
           case (outputs,inArgs) of
             ([output],[input]) -> do
               (outTy, outNm) <- openPrimArg output
               inop <- cgenArg input
               assign outNm inop
               return $ Just inop
             _ ->
               return Nothing

    | otherwise =
        do let inArgs = primInputs args
           inOps <- mapM cgenArg inArgs
           case (Map.lookup name llvmMapUnop,inOps) of
             (Just f,[inOp]) -> addInstruction (f inOp) args
             (Nothing,_)     -> shouldnt $ "LLVM Instruction not found : "
                                           ++ name
             (_,_)           -> shouldnt $ "unary LLVM Instruction " ++ name
                                           ++ " with " ++ show (length inArgs)
                                           ++ " inputs"


-- | Look inside the Prototype list stored in the CodegenState monad and
-- find a matching ProcSpec.
findProto :: ProcSpec -> Codegen (Maybe PrimProto)
findProto (ProcSpec _ nm i) = do
    allProtos <- gets Codegen.modProtos
    let procNm = nm
    let matchingProtos = List.filter ((== nm) . primProtoName) allProtos
    return $ maybeNth i matchingProtos


-- | Match PrimArgs with the paramaters in the given prototype. If a PrimArg's
-- counterpart in the prototype is unneeded, filtered out. Positional matching
-- is used for this.
filterUnneededArgs :: PrimProto -> [PrimArg] -> [PrimArg]
filterUnneededArgs proto args = argsNeeded args (primProtoParams proto)

argsNeeded :: [PrimArg] -> [PrimParam] -> [PrimArg]
argsNeeded [] [] = []
argsNeeded [] (_:_) = shouldnt "more parameters than arguments"
argsNeeded (_:_) [] = shouldnt "more arguments than parameters"
argsNeeded (ArgUnneeded _ _:as) (p:ps)
    | paramNeeded p = shouldnt $ "unneeded arg for needed param " ++ show p
    | otherwise     = argsNeeded as ps
argsNeeded (a:as) (p:ps)
    | paramNeeded p = a : argsNeeded as ps
    | otherwise     = argsNeeded as ps


-- |Return the integer constant from an argument; error if it's not one
trustArgInt :: PrimArg -> Integer
trustArgInt arg = trustFromJust
                  "LPVM instruction argument must be an integer constant."
                  $ argIntVal arg


-- | Code generation for LPVM instructions.
cgenLPVM :: ProcName -> [Ident] -> [PrimArg] -> Codegen (Maybe Operand)
cgenLPVM "alloc" [] args@[sizeArg,addrArg] = do
          logCodegen $ "lpvm alloc " ++ show sizeArg ++ " " ++ show addrArg
          let inputs = primInputs args
          case inputs of
            [input] -> do
                outTy <- lift $ llvmType $ argType addrArg
                op <- gcAllocate sizeArg outTy
                assign (pullName addrArg) op
                return $ Just op
            _ ->
              shouldnt $ "alloc instruction with " ++ show (length inputs)
                         ++ " inputs"

cgenLPVM "access" [] args@[addrArg,offsetArg,val] = do
          logCodegen $ "lpvm access " ++ show addrArg ++ " " ++ show offsetArg
                 ++ " " ++ show val
          baseAddr <- cgenArg addrArg
          finalAddr <- offsetAddr baseAddr iadd offsetArg
          outTy <- lift $ llvmType $ argType val
          logCodegen $ "outTy = " ++ show outTy
          op <- gcAccess finalAddr outTy
          assign (pullName val) op
          return $ Just op

cgenLPVM "mutate" flags
    [addrArg, outArg, offsetArg, ArgInt 0 intTy, sizeArg, tagArg, valArg] = do
         -- Non-destructive case:  copy structure before mutating
          logCodegen $ "lpvm mutate " ++ show addrArg
                       ++ " " ++ show outArg
                       ++ " " ++ show offsetArg ++ " *nondestructive*"
                       ++ " " ++ show sizeArg
                       ++ " " ++ show tagArg
                       ++ " " ++ show valArg
          -- First copy the structure
          outTy <- lift $ llvmType $ argType addrArg
          op <- gcAllocate sizeArg outTy
          assign (pullName outArg) op
          taggedAddr <- cgenArg addrArg
          baseAddr <- offsetAddr taggedAddr isub tagArg
          callMemCpy op baseAddr sizeArg
          -- Now destructively mutate the copy
          cgenLPVM "mutate" flags
            [outArg, addrArg, offsetArg, ArgInt 1 intTy, sizeArg, tagArg,
             valArg]
cgenLPVM "mutate" _
    [addrArg, outArg, offsetArg, (ArgInt 1 _), sizeArg, tagArg, valArg] = do
         -- Destructive case:  just mutate
          logCodegen $ "lpvm mutate " ++ show addrArg
                       ++ " " ++ show outArg
                       ++ " " ++ show offsetArg ++ " *destructive*"
                       ++ " " ++ show sizeArg
                       ++ " " ++ show tagArg
                       ++ " " ++ show valArg
          baseAddr <- cgenArg addrArg
          gcMutate baseAddr offsetArg valArg
          assign (pullName outArg) baseAddr
          return $ Just baseAddr

cgenLPVM "mutate" _ [_, _, _, destructiveArg, _, _, _] =
      nyi "lpvm mutate instruction with non-constant destructive flag"


cgenLPVM "cast" [] args@[inArg,outArg] = do
    let inputs = primInputs args
    let outputs = primOutputs args
    case (inputs,outputs) of
        ([inArg],[outArg]) -> do
            outTy <- lift $ llvmType (argType outArg)
            inOp <- cgenArg inArg
            let inTy = operandType inOp

            lift $ logBlocks $ "CAST IN : " ++ show inArg ++ " -> "
                                ++ show (argType inArg)
            lift $ logBlocks $ " CAST IN OP " ++ show inOp
            lift $ logBlocks $ "CAST OUT : " ++ show outArg ++ " -> "
                                ++ show (argType outArg)
            castOp <- case inOp of
                (ConstantOperand c) ->
                    if isPtr outTy
                    then return $ constInttoptr c outTy
                    else do
                        let consTy = constantType c
                        ptr <- doAlloca consTy
                        store ptr inOp
                        loaded <- doLoad consTy ptr
                        doCast loaded consTy outTy
                _ -> doCast inOp inTy outTy

            assign (pullName outArg) castOp
            return $ Just castOp

        -- A cast with no outputs:  do nothing
        (_, []) -> return Nothing
        _ -> shouldnt $ "cast instruction with " ++ show (length inputs)
                            ++ " inputs and " ++ show (length outputs)
                            ++ " outputs"


cgenLPVM pname flags args = do
    shouldnt $ "Instruction " ++ pname ++ " not imlemented."


-- | Generate code to add an offset to an address

offsetAddr :: Operand -> (Operand -> Operand -> Instruction) -> PrimArg
           -> Codegen Operand
offsetAddr baseAddr offsetFn offset = do
    offsetOp <- cgenArg offset
    case argIntVal offset of
      Just 0 -> return baseAddr
      _      -> do
          offsetArg <- cgenArg offset
          instr address_t (offsetFn baseAddr offsetArg)






isNullCons :: C.Constant -> Bool
isNullCons (C.Int _ val) = val == 0
isNullCons _             = False


isPtr :: LLVMAST.Type -> Bool
isPtr (PointerType _ _) = True
isPtr _                 = False


doCast :: Operand -> LLVMAST.Type -> LLVMAST.Type -> Codegen Operand
doCast op ty1 ty2 = do
    (op,caseStr) <- doCast' op ty1 ty2
    logCodegen $ "doCast from " ++ show op ++ " to " ++ show ty2
                 ++ ":  " ++ caseStr
    return op


doCast' :: Operand -> LLVMAST.Type -> LLVMAST.Type -> Codegen (Operand,String)
doCast' op (IntegerType _) ty2@(PointerType _ _) =
    (,"inttoptr") <$> inttoptr op ty2
doCast' op (PointerType _ _) ty2@(IntegerType _) =
    (,"ptrtoint") <$> ptrtoint op ty2
doCast' op (IntegerType bs1) ty2@(IntegerType bs2)
    | bs1 == bs2 = (,"bitcast no-op") <$> bitcast op ty2
    | bs2 > bs1 = (,"zext") <$> zext op ty2
    | bs1 > bs2 = (,"trunc") <$> trunc op ty2
doCast' op ty1 ty2 =
    (,"bitcast from " ++ show ty1 ++ " case") <$> bitcast op ty2



-- | Predicate to check if an operand is a constant
constantType :: C.Constant -> LLVMAST.Type
constantType (C.Int bs _) = int_c bs
constantType (C.Float _)  = float_t
constantType (C.Null ty)  = ty
constantType (C.Undef ty) = ty
constantType _            = shouldnt "Cannot determine constant type."


----------------------------------------------------------------------------
-- Helpers for dealing with instructions                                  --
----------------------------------------------------------------------------


-- | Append an 'Instruction' to the current basic block's instruction stack.
-- The return type of the operand value generated by the instruction call is
-- inferred depending on the primitive arguments. The name is inferred from
-- the output argument's name (LPVM is in SSA form).
addInstruction :: Instruction -> [PrimArg] -> Codegen (Maybe Operand)
addInstruction ins args = do
    logCodegen $ "addInstruction " ++ show ins ++ " " ++ show args
    let outArgs = primOutputs args
    outTy <- lift $ primReturnType args
    logCodegen $ "outTy = " ++ show outTy
    case outArgs of
          [] -> case outTy of
            VoidType -> voidInstr ins >> return Nothing
            _        -> Just <$> instr outTy ins
          [outArg] -> do
            let outName = pullName outArg
            outop <- namedInstr outTy outName ins
            assign outName outop
            return (Just outop)
          _ -> do
            outOp <- instr outTy ins
            outTys <- lift $ mapM (llvmType . argType) outArgs
            fields <- structUnPack outOp outTys
            let outNames = List.map pullName outArgs
            -- lift $ logBlocks $ "-=-=-=-= Structure names:" ++ show outNames
            zipWithM_ assign outNames fields
            return $ Just $ last fields


pullName (ArgVar var _ _ _ _) = show var
pullName _                    = shouldnt $ "Expected variable as output."

-- | Generate an expanding instruction name using the passed flags. This is
-- useful to augment a simple instruction. (Ex: compare instructions can have
-- the comparision type specified as a flag).
withFlags :: ProcName -> [Ident] -> String
withFlags p [] = p
withFlags p f  = p ++ " " ++ (List.intercalate " " f)

-- | Apply Operands from the operand list (2 items) to the wrapped LLVM
-- instruction from 'Codegen' Module.
apply2 :: (Operand -> Operand -> Instruction) -> [Operand] -> Instruction
apply2 f (a:b:[]) = f a b
apply2 _ _        = shouldnt $ "Not a binary operation."


----------------------------------------------------------------------------
-- Helpers for primitive arguments                                        --
----------------------------------------------------------------------------

-- | Filter valid inputs from given primitive argument list.
-- A valid input flows in and is not phantom.
primInputs :: [PrimArg] -> [PrimArg]
primInputs ps = List.filter isValidInput ps
    where
      isValidInput p = (goesIn p) && (notPhantom p)


-- | If it exists, return the valid primitive output argument.
primOutputs :: [PrimArg] -> [PrimArg]
primOutputs ps = List.filter isValidOutput ps
    where
      isValidOutput p = (not $ goesIn p) && (notPhantom p)

-- | Get the 'Type' of the valid output from the given primitive argument
-- list. If there is no output arg, return void_t.
primReturnType :: [PrimArg] -> Compiler Type
primReturnType ps = do
    let outputs = primOutputs ps
    case outputs of
      [] -> return void_t
      [output] -> llvmType $ argType output
      _ -> fmap struct_t (mapM (llvmType . argType) outputs)


goesIn :: PrimArg -> Bool
goesIn p = (argFlowDirection p) == FlowIn

notPhantom :: PrimArg -> Bool
notPhantom = not . argIsPhantom

-- | Pull out the name of a primitive argument if it is a variable.
argName :: PrimArg -> Maybe String
argName (ArgVar var _ _ _ _) = Just $ show var
argName _                    = Nothing


argIntVal :: PrimArg -> Maybe Integer
argIntVal (ArgInt val _) = Just val
argIntVal _              = Nothing


-- | Open a PrimArg into it's inferred type and string name.
openPrimArg :: PrimArg -> Codegen (Type, String)
openPrimArg (ArgVar nm ty _ _ _) = do
    lltype <- lift $ llvmType ty
    return (lltype, show nm)
openPrimArg a = shouldnt $ "Can't Open!: "
                ++ argDescription a
                ++ (show $ argFlowDirection a)


-- | Assigns the primitive argument on the symbol table
assignPrim :: Operand -> PrimArg -> Codegen ()
assignPrim op (ArgVar var _ _ _ _) = assign (show var) op
assignPrim _ _                     = return ()


localOperandType :: Operand -> Type
localOperandType (LocalReference ty _) = ty
localOperandType _                     = void_t


-- | 'cgenArg' makes an Operand of the input argument. The argument may be:
-- o input variable - lookup the symbol table to get it's Operand value.
-- o Constant - Make a constant Operand according to the type: o String
-- constants: A string constant is an constant Array Type of [N x i8].  This
-- will have to be declared as a global constant to get implicit memory
-- allocation and then be referenced with a pointer (GetElementPtr). To make
-- it a global declaration 'addGlobalConstant' creates a G.Global Value for
-- it, generating a UnName name for it.
cgenArg :: PrimArg -> Codegen LLVMAST.Operand
cgenArg (ArgVar nm _ _ _ _) = getVar (show nm)
cgenArg (ArgInt val ty) = do
    reprTy <- lift $ llvmType ty
    lift $ logBlocks $ show val ++ " :: " ++ show ty
        ++ " -> " ++ show reprTy
    let bs = getBits reprTy
    let intCons = cons $ C.Int bs val
    return intCons
cgenArg (ArgFloat val ty) = return $ cons $ C.Float (F.Double val)
cgenArg (ArgString s _) =
    do let conStr = makeStringConstant s
       let len = length s + 1
       let conType = array_t (fromIntegral len) char_t
       conName <- addGlobalConstant conType conStr
       let conPtr = C.GlobalReference (ptr_t conType) conName
       let conElem = C.GetElementPtr True conPtr [C.Int 32 0, C.Int 32 0]
       -- return $ cons conElem
       -- ptrtoint (cons conElem) $ ptr_t (int_c 8)
       -- We return integer address for strings
       ptrtoint (cons conElem) address_t
cgenArg (ArgChar c ty) = do t <- lift $ llvmType ty
                            let bs = getBits t
                            return $ cons $ C.Int bs $ integerOrd c
cgenArg (ArgUnneeded _ _) = shouldnt "Trying to generate LLVM for unneeded arg"

getBits :: LLVMAST.Type -> Word32
getBits (IntegerType bs)                = bs
getBits (PointerType ty _)              = getBits ty
getBits (FloatingPointType HalfFP)      = 16
getBits (FloatingPointType FloatFP)     = 32
getBits (FloatingPointType DoubleFP)    = 64
getBits (FloatingPointType FP128FP)     = 128
getBits (FloatingPointType X86_FP80FP)  = 80
getBits (FloatingPointType PPC_FP128FP) = 128
getBits ty                              = fromIntegral wordSize

-- | Convert a string into a constant array of constant integers.
makeStringConstant :: String ->  C.Constant
makeStringConstant s = C.Array char_t cs
    where ns = List.map integerOrd (s ++ "\00")
          cs = List.map (C.Int 8) ns


-- | 'integerOrd' performs ord but returns an Integer type
integerOrd :: Char -> Integer
integerOrd = toInteger . ord

----------------------------------------------------------------------------
-- Instruction maps                                                       --
----------------------------------------------------------------------------


-- | A map of arithmetic binary operations supported through LLVM to
-- their Codegen module counterpart.
llvmMapBinop =
    Map.fromList [
            ("add", iadd),
            ("sub", isub),
            ("mul", imul),
            ("div", idiv),
            ("sdiv", sdiv),
            ("urem", urem),
            ("srem", srem),
            -- * Floating point instruction
            ("fadd", fadd),
            ("fsub", fsub),
            ("fmul", fmul),
            ("fdiv", fdiv),
            ("frem", frem),
            -- * Comparisions
            ("icmp eq", icmp IP.EQ),
            ("icmp ne", icmp IP.NE),
            ("icmp ugt", icmp IP.UGT),
            ("icmp uge", icmp IP.UGE),
            ("icmp ult", icmp IP.ULT),
            ("icmp ule", icmp IP.ULE),
            ("icmp sgt", icmp IP.SGT),
            ("icmp sge", icmp IP.SGE),
            ("icmp slt", icmp IP.SLT),
            ("icmp sle", icmp IP.SLE),

            -- * Floating point comparisions
            ("fcmp eq", fcmp FP.OEQ),
            ("fcmp ne", fcmp FP.ONE),
            ("fcmp slt", fcmp FP.OLT),
            ("fcmp sle", fcmp FP.OLE),
            ("fcmp sgt", fcmp FP.OGT),
            ("fcmp sge", fcmp FP.OGE),
            -- * Bitwise operations
            ("shl", shl),
            ("lshr", lshr),
            ("ashr", ashr),
            ("or", lOr),
            ("and", lAnd),
            ("xor", lXor)
           ]

-- | A map of unary llvm operations wrapped in the 'Codegen' module.
llvmMapUnop =
    Map.fromList [
            ("uitofp", uitofp),
            ("fptoui", fptoui)
           ]



----------------------------------------------------------------------------
-- Helpers                                                                --
----------------------------------------------------------------------------
-- XXX unused?
-- typed :: TypeSpec -> LLVMAST.Type
-- typed AnyType                      = ptr_t char_t -- XXX should be a word type
-- typed TypeSpec{typeName="int"}     = int_t
-- typed TypeSpec{typeName="char"}    = char_t
-- typed TypeSpec{typeName="float"}   = float_t
-- typed TypeSpec{typeName="double"}  = float_t
-- typed TypeSpec{typeName="bool"}    = int_c 1
-- typed TypeSpec{typeName="string"}  = ptr_t char_t
-- typed TypeSpec{typeName="phantom"} = void_t
-- typed _                            = void_t


llvmType :: TypeSpec -> Compiler LLVMAST.Type
llvmType ty = do
    repr <- lookupTypeRepresentation ty
    case repr of
        Just typeStr -> return $ typeStrToType typeStr
        Nothing ->
            shouldnt $ "llvmType applied to InvalidType or unknown type ("
            ++ show ty
            ++ ")"


typeStrToType :: String -> LLVMAST.Type
typeStrToType []        = void_t
typeStrToType "int"     = address_t
typeStrToType "bool"    = int_c 1
typeStrToType "float"   = float_t
typeStrToType "double"  = float_t
typeStrToType "address" = address_t
typeStrToType "word"    = address_t
typeStrToType "phantom" = int_t
typeStrToType ('i':cs)  = int_c (read cs)
typeStrToType ('f':cs)  = float_c (read cs)
typeStrToType typename  = shouldnt $ "Unrecognised type string '" ++ typename
                                     ++ "'"

------------------------------------------------------------------------------
-- -- * Creating LLVM AST module from global definitions                    --
------------------------------------------------------------------------------

-- | Initialize and fill a new LLVMAST.Module with the translated
-- global definitions (extern declarations and defined functions)
-- of LPVM procedures in a module.
newLLVMModule :: String -> String -> [ProcDefBlock] -> LLVMAST.Module
newLLVMModule name fname blocks
    = let defs = List.map blockDef blocks
          exs  = concat $ List.map blockExterns blocks
          exs' = uniqueExterns exs ++ [mallocExtern] ++ intrinsicExterns
      in modWithDefinitions name fname $ exs' ++ defs


-- | Filter out non-unique externs
uniqueExterns :: [LLVMAST.Definition] -> [LLVMAST.Definition]
uniqueExterns exs = List.nubBy sameDef exs
  where
    sameDef (LLVMAST.GlobalDefinition g1) (LLVMAST.GlobalDefinition g2)
      = (G.name g1) == (G.name g2)
    sameDef _ _ = False


-- | Create a new LLVMAST.Module with the given name, and fill it with the
-- given global definitions.
modWithDefinitions :: String -> String -> [LLVMAST.Definition] -> LLVMAST.Module
modWithDefinitions nm filename defs =
    LLVMAST.Module (toSBString nm) (toSBString filename) Nothing Nothing defs


-- | Build an extern declaration definition from a given LPVM primitive.
declareExtern :: Prim -> Compiler LLVMAST.Definition
declareExtern (PrimForeign _ name _ args) = do
    fnargs <- mapM makeExArg $ zip [1..] (primInputs args)
    retty <- primReturnType args
    let ex = external retty name fnargs
    return ex

declareExtern (PrimCall pspec@(ProcSpec m n _) args) = do
    retty <- primReturnType args
    fnargs <- mapM makeExArg $ zip [1..] (primInputs args)
    return $ external retty (show pspec) fnargs

declareExtern (PrimTest _) = shouldnt "Can't declare extern for PrimNop."

-- | Helper to make arguments for an extern declaration.
makeExArg :: (Word, PrimArg) -> Compiler (Type, LLVMAST.Name)
makeExArg (index,arg) = do
    ty <- (llvmType . argType) arg
    let nm = LLVMAST.UnName index
    return (ty, nm)


-- | An extern for wybe_malloc
mallocExtern :: LLVMAST.Definition
mallocExtern =
    let ext_arg = [(LLVMAST.IntegerType 32, LLVMAST.Name $ toSBString "size")]
    in external (ptr_t (int_c 8)) "wybe_malloc" ext_arg


-- | Externs for any intrinsics we might need.  For now, just memcpy.
-- Intrinsics are built in to LLVM, so they're always available.
intrinsicExterns :: [LLVMAST.Definition]
intrinsicExterns =
    [external void_t "llvm.memcpy.p0i8.p0i8.i32" [
        (ptr_t (int_c 8), LLVMAST.Name $ toSBString "dest"),
        (ptr_t (int_c 8), LLVMAST.Name $ toSBString "src"),
        (LLVMAST.IntegerType 32, LLVMAST.Name $ toSBString "len"),
        (LLVMAST.IntegerType 32, LLVMAST.Name $ toSBString "alignment"),
        (LLVMAST.IntegerType 1, LLVMAST.Name $ toSBString "isvolatile")]
    ]


----------------------------------------------------------------------------
-- Block Modification                                                     --
----------------------------------------------------------------------------

-- -- | Create a new LLVMAST.Module with in-order calls to the
-- -- given modules' mains.
-- -- A module's main would look like: 'module.main'
-- -- For each call, an external declaration to that main function is needed.
-- newMainModule :: [ModSpec] -> Compiler LLVMAST.Module
-- newMainModule depends = do
--     blstate <- execCodegen 0 [] $ mainCodegen depends
--     let bls = createBlocks blstate
--     let mainDef = globalDefine int_t "main" [] bls
--     let externsForMain = [(external (void_t) "gc_init" [])]
--             ++ (mainExterns depends)
--     let newDefs = externsForMain ++ [mainDef]
--     -- XXX Use empty string as source file name; should be main file name
--     return $ modWithDefinitions "tmpMain" "" newDefs


-- -- | Run the Codegen monad collecting the instructions needed to call
-- -- the given modules' main(s). This main function returns 0.
-- mainCodegen :: [ModSpec] -> Codegen ()
-- mainCodegen mods = do
--     entry <- addBlock entryBlockName
--     setBlock entry
--     -- Temp Boehm GC init call
--     voidInstr $
--         call (externf (ptr_t $ FunctionType void_t [] False)
--               (LLVMAST.Name $ toSBString "gc_init")) []
--     -- Call the mods mains in order
--     let mainName m = LLVMAST.Name $ toSBString $ showModSpec m ++ ".main"
--     forM_ mods $ \m -> instr int_t $
--                        call (externf (ptr_t $ FunctionType int_t [] False) (mainName m)) []
--     -- int main returns 0
--     ptr <- instr (ptr_t int_t) (alloca int_t)
--     let retcons = cons (C.Int 32 0)
--     store ptr retcons
--     ret (Just retcons)
--     return ()

-- -- | Create a list of extern declarations for each call to a foreign
-- -- module's main.
-- mainExterns :: [ModSpec] -> [LLVMAST.Definition]
-- mainExterns mods = List.map externalMain mods
--     where
--       mainName m = showModSpec m ++ "."
--       externalMain m = external int_t (mainName m) []


-- | Concat the LLVMAST.Module implementations of a list of loaded modules
-- to the LLVMAST.Module implementation ModSpec passed as the first
-- parameter.
-- It is assumed and required that all these modules are loaded and compiled
-- to their LLVM stage (so that the modLLVM field will exist)
-- Concatenation involves uniquely appending the LLVMAST.Definition lists.
concatLLVMASTModules :: ModSpec      -- ^ Module to append to
                     -> [ModSpec]    -- ^ Modules to append
                     -> Compiler LLVMAST.Module
concatLLVMASTModules thisMod mspecs = do
    -- pull LLVMAST.Module implementations of appending modspecs
    maybeLLMods <- mapM ((fmap modLLVM) . getLoadedModuleImpln) mspecs
    let trustMsg = "LLVMAST.Module implementation not generated."
    let llmods = List.map (trustFromJust trustMsg) maybeLLMods
    let defs = List.map LLVMAST.moduleDefinitions llmods
    -- pull LLVMAST.Module implementation of the modspec to append to
    thisLLMod <- trustFromJustM trustMsg $
        fmap modLLVM $ getLoadedModuleImpln thisMod
    let updatedLLMod = List.foldl addUniqueDefinitions thisLLMod defs
    -- updateLoadedModuleImpln (\imp -> imp { modLLVM = Just updatedLLMod })
    --     thisMod
    return updatedLLMod


-- | Extend the LLVMAST.Definition list of the first module with the
-- LLVMAST.Definition list passed as the second parameter. The concatenation
-- must be unique.
addUniqueDefinitions :: LLVMAST.Module -> [LLVMAST.Definition]
                     -> LLVMAST.Module
addUniqueDefinitions (LLVMAST.Module n fn l t ds) defs =
    LLVMAST.Module n fn l t newDefs
  where
    newDefs = List.nub $ ds ++ defs


-------------------------------------------------------------------------------
-- Memory Interface                                                          --
-------------------------------------------------------------------------------

-- * $ functions

-- | Call "wybe_malloc" from external C shared lib. Returns an i8* pointer.
-- XXX What will be the type of 'size' we pass to extern C's malloc?
callWybeMalloc :: PrimArg -> Codegen Operand
callWybeMalloc size = do
    let outTy = (ptr_t (int_c 8))
    let fnName = LLVMAST.Name $ toSBString "wybe_malloc"
    sizeOp <- cgenArg size
    sizeTy <- lift $ llvmType $ argType size
    logCodegen $ "callWybeMalloc casting size " ++ show sizeOp
                 ++ " to " ++ show int_t
    inops <- (:[]) <$> doCast sizeOp sizeTy int_t
    let ins =
          call
          (externf (ptr_t (FunctionType outTy (typeOf <$> inops) False)) fnName)
          inops
    instr outTy ins


-- | Invoke the LLVM memcpy intrinsic to copy a specified number of bytes of
-- memory from a source address to a non-overlapping destination address.
callMemCpy :: Operand -> Operand -> PrimArg -> Codegen ()
callMemCpy dst src bytes = do
    let fnName = LLVMAST.Name $ toSBString "llvm.memcpy.p0i8.p0i8.i32"
    let charptr_t = ptr_t (int_c 8)
    dstCast <- doCast dst address_t charptr_t
    srcCast <- doCast src address_t charptr_t
    bytesOp <- cgenArg bytes
    bytesCast <- doCast bytesOp address_t int_t
    -- dstCast <- instr charptr_t $ LLVMAST.BitCast dst charptr_t []
    -- srcCast <- instr charptr_t $ LLVMAST.BitCast src charptr_t []
    -- bytesOp <- cgenArg bytes
    -- bytesCast <- instr int_t   $ LLVMAST.BitCast bytesOp int_t []
    let inops = [dstCast, srcCast, bytesCast,
                 cons (C.Int 32 $ fromIntegral wordSizeBytes),
                 cons (C.Int 1 0)]
    let ins =
          call
          (externf (ptr_t (FunctionType void_t (typeOf <$> inops) False))
           fnName)
          inops
    voidInstr ins


-- | Call the external C-library function for malloc and return
-- the bitcasted pointer to that location.
gcAllocate :: PrimArg -> LLVMAST.Type -> Codegen Operand
gcAllocate size castTy = do
    voidPtr <- callWybeMalloc size
    ptrtoint voidPtr address_t



-- | Index and return the value in the memory field referenced by the pointer
-- at the given offset.
-- If expected return type/value at that location is a pointer, then
-- the instruction inttoptr should precede the load instruction.
gcAccess :: Operand -> LLVMAST.Type -> Codegen Operand
gcAccess ptr outTy = do
    logCodegen $ "gcAccess " ++ show ptr ++ " " ++ show outTy
    let ptrTy = ptr_t outTy
    ptr' <- inttoptr ptr ptrTy
    logCodegen $ "inttoptr " ++ show ptr ++ " " ++ show (ptr_t outTy)
    logCodegen $ "inttoptr produced " ++ show ptr'

    let indices = [cons $ C.Int (fromIntegral wordSize) 0]
    let getel = LLVMAST.GetElementPtr False ptr' indices []
    logCodegen $ "getel = " ++ show getel
    accessPtr <- instr ptrTy getel
    logCodegen $ "accessPtr = " ++ show accessPtr
    let loadInstr = load accessPtr
    logCodegen $ "loadInstr = " ++ show loadInstr
    instr outTy $ load accessPtr


    -- inttoptr loadedOp outTy
    -- case outTy of
    --     (PointerType ty _) -> do
    --         loadedOp <- instr opType $ load accessPtr
    --         inttoptr loadedOp outTy
    --     _ -> instr opType $ load accessPtr


-- | Index the pointer at the given offset and store the given operand value
-- in that indexed location.
-- If the operand to be stored is a pointer, the ptrtoint instruction should
-- precede the store instruction, with the int value of the pointer stored.
gcMutate :: Operand -> PrimArg -> PrimArg -> Codegen ()
gcMutate baseAddr offsetArg valArg = do
    logCodegen $ "gcMutate " ++ show baseAddr ++ " " ++ show offsetArg
                 ++ " " ++ show valArg
    finalAddr <- offsetAddr baseAddr iadd offsetArg
    valTy <- lift $ llvmType $ argType valArg
    let ptrTy = ptr_t valTy
    ptr' <- inttoptr finalAddr ptrTy
    logCodegen $ "inttoptr " ++ show finalAddr ++ " " ++ show ptrTy
    logCodegen $ "inttoptr produced " ++ show ptr'
    let indices = [cons $ C.Int (fromIntegral wordSize) 0]
    let getel = LLVMAST.GetElementPtr False ptr' indices []
    logCodegen $ "getel = " ++ show getel
    accessPtr <- instr ptrTy getel
    logCodegen $ "accessPtr = " ++ show accessPtr
    val <- cgenArg valArg
    store accessPtr val
    return ()


-- | Get the LLVMAST.Type the given pointer type points to.
pullFromPointer :: LLVMAST.Type -> LLVMAST.Type
pullFromPointer (PointerType ty _) = ty
pullFromPointer pty                = shouldnt $ "Not a pointer: " ++ show pty


-- | Compute the index given the size of the fields the pointer
-- points to and an offset in bytes.
getIndex :: LLVMAST.Type -> Integer -> Integer
getIndex (PointerType ty _) bytes =
    let ptrBits = toInteger $ getBits ty
    in quot (bytes * 8) ptrBits
getIndex _ _ = shouldnt "Can't compute index from a non-pointer."


-- Convert string to ShortByteString
toSBString :: [Char] -> BSS.ShortByteString
toSBString string = BSS.pack $ unsafeCoerce <$> string

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the Compiler monad to Blocks.
logBlocks :: String -> Compiler ()
logBlocks = logMsg Blocks


-- | Log with a wrapping line of replicated characters above and below.
logWrapWith :: Char -> String -> Compiler ()
logWrapWith ch s = do
    logMsg Blocks (replicate 65 ch)
    logMsg Blocks s
    logMsg Blocks (replicate 65 ch)

logCodegen :: String -> Codegen ()
logCodegen s = lift $ logBlocks s
