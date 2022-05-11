--  File     : Blocks.hs
--  Author   : Ashutosh Rishi Ranjan
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE TupleSections #-}

module Blocks (concatLLVMASTModules, blockTransformModule,
               llvmMapBinop, llvmMapUnop
              ) where

import           AST
import           Debug.Trace
import           ASTShow
import           BinaryFactory
import           Codegen
import           Resources
import           Config                          (wordSize, wordSizeBytes)
import           Util                            (maybeNth, lift2,
                                                  (|||), (&&&))
import           Snippets
import           Control.Monad                   as M
import           Control.Monad.Extra             (ifM)
import           Control.Monad.Trans             (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Data.Char                       (ord)
import           Data.Foldable
import           Data.List                       as List
import           Data.List.Predicate
import           Data.Map                        as Map
import qualified Data.Set                        as Set
import           Data.String
import           Data.Functor                    ((<&>))
import           Data.Word                       (Word32)
import           Data.Maybe                      (fromMaybe, isJust, catMaybes, isNothing)
import           Flow                            ((|>))
import qualified LLVM.AST                        as LLVMAST
import qualified LLVM.AST.Constant               as C
import qualified LLVM.AST.Float                  as F
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Global                 as G
import           LLVM.AST.Instruction
import qualified LLVM.AST.IntegerPredicate       as IP
import           LLVM.AST.Operand                hiding (PointerType, operands)
import           LLVM.AST.Type
import           LLVM.AST.Typed
import           LLVM.Pretty                     (ppllvm)

import qualified Data.ByteString                 as BS
import qualified Data.ByteString.Char8           as B8
import qualified Data.ByteString.Lazy            as BL
import qualified Data.ByteString.Short           as BSS
import           Options                         (LogSelection (Blocks))
import           Unsafe.Coerce
import           System.FilePath
import qualified UnivSet
import Control.Exception (assert)
import Data.Set (Set)

-- | Holds information on the LLVM representation of the LPVM procedure.
data ProcDefBlock =
    ProcDefBlock { blockProto   :: PrimProto
                 , blockDef     :: LLVMAST.Definition
                 } deriving (Show, Eq)


-- | Transform the module's procedures (in LPVM by now) into LLVM function
-- definitions. A LLVMAST.Module is built up using these global definitions
-- and then stored in the modLLVM field of 'ModuleImplementation'.
-- Before translation of ProcDefs, all the prototypes of the ProcDef's LPVM
-- form is collected, along with the same for all the imported modules.
-- This is passed along to the codegen monad so that Primitive calls to these
-- procedures can the prototype checked (match and eliminate unneeded
-- arguments in cgen.)
blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule thisMod = do
    reenterModule thisMod
    logBlocks $ "*** Translating Module: " ++ showModSpec thisMod
    modRec <- getModule id
    modFile <- getSource
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
    trs <- mapM moduleLLVMType knownTypes
    -- typeList :: [(TypeSpec, LLVMAST.Type)]
    let typeList = zip knownTypes trs
    -- log the assoc list typeList
    logWrapWith '.' $ "Known Types:\n" ++ intercalate "\n" (
        List.map (\(a,b) -> show a ++ ": " ++ show b) typeList)

    --------------------------------------------------
    -- Name mangling
    let mangledProcs = concat $ mangleProcs <$> procs

    --------------------------------------------------
    -- Translate
    (procBlocks, txState) <- mapM translateProc mangledProcs
                             `runStateT` emptyTranslation

    let procBlocks' = List.concat procBlocks
    --------------------------------------------------

    let resDefs = modResources $ trustFromJust "blockTransformModule"
                                $ modImplementation modRec
    let ress = concat $ Map.keys <$> Map.elems resDefs
    llmod <- newLLVMModule (showModSpec thisMod) modFile procBlocks' txState ress
    updateImplementation (\imp -> imp { modLLVM = Just llmod })
    logBlocks $ "*** Translated Module: " ++ showModSpec thisMod
    modRec' <- getModule id
    logWrapWith '-' $ show modRec'
    reexitModule
    logBlocks $ "*** Exiting Module " ++ showModSpec thisMod ++ " ***"


-- -- |Affix its id number to the end of each proc name
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
       ProcDefPrim{procImplnProto = proto} -> proto
       uncompiled ->
         shouldnt $ "Proc reached backend uncompiled: " ++ show uncompiled

-- | Go into a (compiled) Module and pull out the PrimProto implementation
-- of all ProcDefs in the module implementation.
getPrimProtos :: ModSpec -> Compiler [PrimProto]
getPrimProtos modspec = do
    (_, procs) <- unzip . Map.toList . modProcs <$>
                  getLoadedModuleImpln modspec
    let protos = List.map extractLPVMProto (concat procs)
    return protos

-- | Filter for avoiding the standard library modules
isStdLib :: ModSpec -> Bool
isStdLib []    = False
isStdLib (m:_) = m == "wybe"



-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). Each ProcDef is converted into a Global
-- Definition in a LLVM Module by translating it's primitives.  Translated
-- procedures (ProcDefBlocks ...) can optionally have a list of extern
-- declarations (which are also global definitions) if any primitive is going
-- to call some foreign function (mostly C).  Translated procedures will also
-- require some global variable/constant declarations which is represented as
-- G.Global values in the neededGlobalVars field of LLVMCompstate. All in all,
-- externs and globals go on the top of the module.
translateProc :: ProcDef -> Translation [ProcDefBlock]
translateProc proc = do
    let proto = procImplnProto $ procImpln proc
    let body = procImplnBody $ procImpln proc
    let isClosure = isClosureVariant $ procVariant proc
    let speczBodies = procImplnSpeczBodies $ procImpln proc
    -- translate the standard version
    block <- _translateProcImpl proto isClosure body
    -- translate the specialized versions
    let speczBodies' = speczBodies
                        |> Map.toList
                        |> List.map (\(ver, body) ->
                            let msg = "Required specialized version should be \
                                      \ generated by now" in
                            (speczVersionToId ver, trustFromJust msg body))
    -- Make sure there aren't collision in specz version id. If such thing
    -- happened, we may consider increasing the length of id (more in AST.hs).
    let hasDuplicates l = List.length l /= (Set.size . Set.fromList) l
    when (hasDuplicates (List.map fst speczBodies'))
            $ shouldnt $ "Specz version id conflicts"
                ++ show (List.map fst speczBodies')
    blocks <- mapM (\(id, currBody) -> do
                    -- rename this version of proc
                    let pname = primProtoName proto ++ "[" ++ id ++ "]"
                    let proto' = proto {primProtoName = pname}
                    _translateProcImpl proto' isClosure currBody
            ) speczBodies'
    return $ block:blocks


-- Helper for `translateProc`. Translate the given `ProcBody`
-- (A specialized version of a procedure).
_translateProcImpl :: PrimProto -> Bool -> ProcBody -> Translation ProcDefBlock
_translateProcImpl proto isClosure body = do
    let (proto', body') = if isClosure then closeClosure proto body
                                       else (proto, body)
    modspec <- lift getModuleSpec
    lift $ do
        logBlocks $ "\n" ++ replicate 70 '=' ++ "\n"
        logBlocks $ "In Module: " ++ showModSpec modspec
                    ++ ", creating definition of:\n\n"
        logBlocks $ show proto'
                    ++ showBlock 4 body'
                    ++ "\n" ++ replicate 50 '-' ++ "\n"
    codestate <- doCodegenBody body'
                    `execStateT` emptyCodegen proto'
    let pname = primProtoName proto
    let body' = createBlocks codestate
    lldef <- lift $ makeGlobalDefinition pname proto' body'
    lift $ logBlocks $ show lldef
    return $ ProcDefBlock proto lldef

-- | Updates a PrimProto and ProcBody as though the Free Params are accessed
-- via the closure environment
closeClosure :: PrimProto -> ProcBody -> (PrimProto, ProcBody)
closeClosure proto@PrimProto{primProtoParams=params}
             body@ProcBody{bodyPrims=prims} =
    (proto{primProtoParams=
            envPrimParam:(setPrimParamType AnyType <$> actualParams)},
     body{bodyPrims=unpacker ++ prims})
  where
    (free, actualParams) = List.partition ((==Free) . primParamFlowType) params
    neededFree = List.filter (not . paramInfoUnneeded
                                  . primParamInfo) free
    unpacker = Unplaced <$>
                [ primAccess (ArgVar envParamName AnyType FlowIn Ordinary False)
                             (ArgInt (i * toInteger wordSizeBytes) intType)
                             (ArgInt (toInteger wordSize) intType)
                             (ArgInt 0 intType)
                             (ArgVar nm ty FlowOut Free False)
                | (i,PrimParam nm ty _ _ _) <- zip [1..] neededFree ]


-- | Create LLVM's module level Function Definition from the LPVM procedure
-- prototype and its body as a list of BasicBlock(s). The return type of such
-- a definition is decided based on the Ouput parameter of the procedure, or
-- is made to be phantom.
makeGlobalDefinition :: String -> PrimProto
                     -> [LLVMAST.BasicBlock]
                     -> Compiler LLVMAST.Definition
makeGlobalDefinition pname proto bls = do
    modName <- showModSpec <$> getModuleSpec
    let label0 = modName ++ "." ++ pname
    -- For the top-level main program
    let isMain = label0 == ".<0>"
    let (label,isForeign) = if isMain then ("main",True) else (label0,False)
    fnargs <- protoLLVMArguments proto
    retty <- protoLLVMOutputType proto
    return $ globalDefine isForeign retty label fnargs bls

-- | Convert a primitive's input parameter to LLVM's Definition parameter.
makeFnArg :: PrimParam -> Compiler (Type, LLVMAST.Name)
makeFnArg param = do
    ty <- primParamLLVMType param
    let nm = LLVMAST.Name $ toSBString $ show $ primParamName param
    return (ty, nm)

type LLVMCallSignature = ([Type], Type)

getLLVMSignature :: PrimProto -> Compiler LLVMCallSignature
getLLVMSignature proto = do
    out <- protoLLVMOutputType proto
    args <- protoLLVMArguments proto
    return (List.map fst args, out)

protoLLVMArguments :: PrimProto -> Compiler [(Type, LLVMAST.Name)]
protoLLVMArguments proto = do
    inputs <- protoRealParamsWhere paramGoesIn proto
    mapM makeFnArg inputs

-- | Open the Out parameter of a primitive (if there is one) into it's
-- inferred 'Type' and name.
protoLLVMOutputType :: PrimProto -> Compiler Type
protoLLVMOutputType proto = do
    outputs <- protoRealParamsWhere paramGoesOut proto
    outTys <- mapM primParamLLVMType outputs
    primReturnLLVMType outTys

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
doCodegenBody :: ProcBody -> Codegen ()
doCodegenBody body = do
    entry <- addBlock entryBlockName
    -- Start with creation of blocks and adding instructions to it
    setBlock entry
    proto <- gets proto
    params <- lift2 $ protoRealParams proto
    let (ins,outs) = List.partition paramGoesIn params
    mapM_ assignParam ins
    -- This handles the fact that some outputs are not defined on failing branches,
    -- by initialising all outputs to `Undef` at the start of the proc.
    mapM_ preassignOutput outs
    -- Codegen on body prims
    codegenBody body

-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table. Don't assign if phantom.
assignParam :: PrimParam -> Codegen ()
assignParam p@PrimParam{primParamType=ty, primParamFlow = paramFlow } = do
    trep <- typeRep' ty
    logCodegen $ "Maybe generating parameter " ++ show p
                 ++ " (" ++ show trep ++ ")"
    unless (repIsPhantom trep || paramInfoUnneeded (primParamInfo p))
      $ do
            let nm = show (primParamName p)
            llty <- lift2 $ primParamLLVMType p
            modifySymtab nm (localVar llty nm)

-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table. Don't assign if phantom
preassignOutput :: PrimParam -> Codegen ()
preassignOutput p = do
    let nm = show (primParamName p)
    llty <- lift2 $ primParamLLVMType p
    modifySymtab nm (cons $ C.Undef llty)


-- | Retrive or build the output operand from the given parameters.
-- For no valid ouputs, return Nothing
-- For 1 single output, retrieve it's assigned operand from the symbol
-- table, and for multiple outputs, generate code for creating an valid
-- structure, pack the operands into it and return it.
buildOutputOp :: PrimProto -> Codegen (Maybe Operand)
buildOutputOp proto = do
    outParams <- lift2 $ protoRealParamsWhere paramGoesOut proto
    logCodegen $ "OutParams: " ++ show outParams
    outputs <- mapM (liftM3 castVar primParamName primParamType primParamFlow) outParams
    logCodegen $ "Built outputs from symbol table: " ++ show outputs
    case outputs of
        -- No valid output
        []       -> return Nothing
        -- single output case
        [single] -> return $ Just single
        -- multiple output case
        _        -> Just <$> structPack outputs


-- | Pack operands into a structure through a sequence of insertvalue
-- instructions.
structPack :: [Operand] -> Codegen Operand
structPack ops = do
    let opTypes = List.map typeOf ops
    let strType = struct_t opTypes
    let strCons = cons $ C.Undef strType
    sequentialInsert ops strType strCons 0


-- | Helper for structInsert to properly and sequentially index each
-- operand into the structure.
-- Sequentially call the insertvalue instruction to add each
-- of the given operand into a new structure type. Each call to the
-- insertvalue instruction would return a new structure which should be
-- used for the next insertion at the next index.
sequentialInsert :: [Operand] -> Type ->
                    Operand -> Word32 -> Codegen Operand
sequentialInsert [] _ finalStruct _ = return finalStruct
sequentialInsert (op:ops) ty struct i = do
    newStruct <- instr ty $ insertvalue struct op i
    sequentialInsert ops ty newStruct (i + 1)


structUnPack :: Operand -> Codegen [Operand]
structUnPack st = case typeOf st of
        StructureType { elementTypes = tys } -> do
            let n = (fromIntegral $ length tys) :: Word32
            let ins = List.map (extractvalue st) [0..n-1]
            zipWithM instr tys ins
        _ -> shouldnt "expected struct to unpack"


-- | Generate basic blocks for a procedure body. The first block is named
-- 'entry' by default. All parameters go on the symbol table (output too).
codegenBody :: ProcBody -> Codegen ()
codegenBody body = do
    let prims = List.map content (bodyPrims body)
    -- Filter out prims which contain only phantom arguments
    case bodyFork body of
        NoFork -> do
            cgen prims True
            proto <- gets proto
            retOp <- buildOutputOp proto
            ret retOp
            return ()
        (PrimFork var ty _ fbody) -> do
            cgen prims False
            codegenForkBody var fbody

-- | Code generation for a conditional branch. Currently a binary split
-- is handled, which each branch returning the left value of their last
-- instruction.
codegenForkBody :: PrimVarName -> [ProcBody] -> Codegen ()
-- XXX Revise this to handle forks with more than two branches using
--     computed gotos
codegenForkBody var [b1, b2] = do
    ifthen <- addBlock "if.then"
    ifelse <- addBlock "if.else"

    testop <- castVar var boolType FlowOut
    cbr testop ifthen ifelse

    -- if.then
    preservingSymtab $ do
        setBlock ifthen
        codegenBody b2

    -- if.else
    preservingSymtab $ do
        setBlock ifelse
        codegenBody b1

    -- -- if.exit
    -- setBlock ifexit
    -- phi int_t [(trueval, ifthen), (falseval, ifelse)]

codegenForkBody var _ =
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
cgen :: [Prim] -> Bool -> Codegen ()
cgen (prim@(PrimCall callSiteID pspec args _):nextPrims) isLeaf = do
    logCodegen $ "--> Compiling " ++ show prim
    let nm = LLVMAST.Name $ toSBString $ show pspec
    -- Find the prototype of the pspec being called
    -- and match it's parameters with the args here
    -- and remove the unneeded ones.
    callerProto <- gets proto
    calleeProto <- lift2 $ getProcPrimProto pspec
    logCodegen $ "Proto = " ++ show calleeProto
    args' <- prepareArgs args (primProtoParams calleeProto)
    logCodegen $ "Prepared args = " ++ show args'

    -- If this call was marked with `tail`, then we generate the remaining prims
    --  *before* the call instruction.
    nextPrims' <- cgenTakeReferences nextPrims
    let isTailPosition = List.null nextPrims' && isLeaf

    -- if the call is to an external module, declare it
    addExternClosure pspec

    let (inArgs,outArgs) = partitionArgs args'
    logCodegen $ "In args = " ++ show inArgs

    (inops, allocaTracking) <- cgenArgsFull inArgs

    outTy <- lift2 $ primReturnType outArgs
    callerSignature <- lift2 $ getLLVMSignature callerProto
    calleeSignature <- lift2 $ getLLVMSignature calleeProto
    let tailCall = getTailCallHint isTailPosition allocaTracking outTy callerSignature calleeSignature
    logCodegen $ "Tail call kind = " ++ show tailCall ++ " (isTailPosition=" ++ show isTailPosition ++ " allocaTracking=" ++ show allocaTracking ++ " outTy=" ++ show outTy ++ " callerSignature=" ++ show callerSignature ++ " calleeSignature=" ++ show calleeSignature ++ ")"

    logCodegen $ "Translated inputs = " ++ show inops
    logCodegen $ "Out ty = " ++ show outTy
    let funcRef = externf (ptr_t (FunctionType outTy (typeOf <$> inops) False)) nm
    let callIns = callWybe tailCall funcRef inops
    logCodegen $ "Translated ins = " ++ show callIns
    addInstruction callIns outArgs

    -- We may need to generate "load" instructions after this call to grab
    -- the underlying values written to by these `outByReference` pointers.
    mapM_ (cgenMaybeLoadReference isTailPosition) args'

    -- Generate the remaining prims in the block
    cgen nextPrims' isLeaf

cgen (prim@(PrimHigher cId (ArgClosure pspec closed _) args):ps) isLeaf = do
    pspec' <- fromMaybe pspec <$> lift2 (maybeGetClosureOf pspec)
    logCodegen $ "Compiling " ++ show prim
              ++ " as first order call to " ++ show pspec'
              ++ " closed over " ++ show closed
    cgen (PrimCall cId pspec' (closed ++ args) univGlobalFlows : ps) isLeaf

cgen [] _ = return ()
cgen (p:ps) isLeaf = do
    cgenPrim p
    cgen ps isLeaf

cgenPrim :: Prim -> Codegen ()
cgenPrim prim@(PrimHigher callSiteId fn@ArgVar{} args) = do
    logCodegen $ "--> Compiling " ++ show prim
    -- We must set all arguments to be `AnyType`
    -- This ensures that we can uniformly pass all parameters to be passed in
    -- the same registers
    let (inArgs, outArgs) = partitionArgs $ setArgType AnyType <$> args
    inOps@(env:_) <- mapM cgenArg $ fn:inArgs
    logCodegen $ "In args = " ++ show inOps
    fnPtrTy <- llvmClosureType (argType fn)
    let addrPtrTy = ptr_t address_t
    envPtr <- inttoptr env addrPtrTy
    eltPtr <- doLoad address_t envPtr
    fnPtr <- doCast eltPtr fnPtrTy
    --- XXX: Tail could cause undef-behaviour in optimizer if the callee
    ---      user allocas from the caller. Double check this is okay.
    let callIns = callWybe (Just LLVMAST.Tail) fnPtr inOps
    addInstruction callIns outArgs

cgenPrim prim@(PrimHigher _ fn _) =
    shouldnt $ "cgen higher call to " ++ show fn

cgenPrim prim@(PrimForeign "llvm" name flags args) = do
    logCodegen $ "--> Compiling " ++ show prim
    args' <- filterPhantomArgs args
    case partitionArgs args' of
       ([], []) | name == "move" -> return () -- move phantom to phantom
       ([a], [b]) -> cgenLLVMUnop name flags a b
       ([a, b], [c]) -> cgenLLVMBinop name flags a b c
       _ -> shouldnt $ "LLVM instruction " ++ name
                       ++ " with wrong arity (" ++ show (length args') ++ ")!"

cgenPrim prim@(PrimForeign "lpvm" name flags args) = do
    logCodegen $ "--> Compiling " ++ show prim
    args' <- filterPhantomArgs args
    cgenLPVM name flags args'

cgenPrim prim@(PrimForeign lang name flags args) = do
    logCodegen $ "--> Compiling " ++ show prim
    when (lang /= "c") $
      shouldnt $ "Unknown foreign language " ++ lang ++ " in call " ++ show prim
    args' <- filterPhantomArgs args
    addExtern $ PrimForeign lang name flags args'
    let (inArgs,outArgs) = partitionArgs args'
    let nm = LLVMAST.Name $ toSBString name
    inops <- mapM cgenArg inArgs
    outty <- lift2 $ primReturnType outArgs
    -- XXX this ignores lang and just uses C calling conventions for all calls
    let ins =
          callC
          (externf (ptr_t (FunctionType outty (typeOf <$> inops) False)) nm)
          inops
    addInstruction ins outArgs

cgenPrim prim@PrimCall {} = shouldnt "calls should be handled by `cgen`"


-- | We use a number of indicators to choose the best TailCallKind where possible.
-- In the best case, the call is marked `musttail`, which signals LLVM must
-- tail-call-optimize, or else will throw an error.
-- `tail` is just a hint that LLVM "can" tail-call optimize but doesn't have to.
-- However there are certain restrictions on when these hints. LLVM may optimize
-- our code incorrectly (or crash) if we get this wrong.
getTailCallHint :: Bool -> AllocaTracking -> LLVMAST.Type -> LLVMCallSignature -> LLVMCallSignature -> Maybe LLVMAST.TailCallKind
-- Oh no! There is an `outByReference` argument which points to an `alloca`.
-- The LLVM language reference dictates that we are not allowed to add
-- `tail` or `musttail` in this case
getTailCallHint _ DoesAlloca _ _ _ = Nothing
-- Although this call is in LPVM tail position, we'll need to add some
-- `extractvalue` instrs after this call, so it won't be in LLVM
-- tail position, thus we cannot use `musttail`
getTailCallHint True NoAlloca StructureType {} _ _ = Just LLVMAST.Tail
-- Although this call is in LPVM tail position, the signatures of the
-- the caller and callee may not match , thus according to LLVM
-- language reference we aren't allowed to use `musttail`.
-- XXX: LLVM version >= 13.0.0 relaxes this restriction
getTailCallHint True NoAlloca _ callerSignature calleeSignature | callerSignature /= calleeSignature = Just LLVMAST.Tail
-- We know this LLVM call will be in LLVM tail position (since scalar/void
-- return type), and also we don't refer to any allocas to in the caller.
getTailCallHint True NoAlloca _ _ _ = Just LLVMAST.MustTail
-- This function isn't in LPVM tail position,
-- but we know it doesn't take any arguments which were created by allocas
-- in the caller.
getTailCallHint False NoAlloca _ _ _ = Just LLVMAST.Tail

-- | Translate a Binary primitive procedure into a binary llvm instruction,
-- add the instruction to the current BasicBlock's instruction stack and emit
-- the resulting Operand. Reads the 'llvmMapBinop' Map.  The primitive
-- arguments are split into inputs and outputs (according to their flow
-- type). The output argument is used to name and reference the resulting
-- Operand of the instruction.
cgenLLVMBinop :: ProcName -> [Ident] -> PrimArg -> PrimArg -> PrimArg -> Codegen ()
cgenLLVMBinop name flags inArg1 inArg2 outArg = do
       inOp1 <- cgenArg inArg1
       inOp2 <- cgenArg inArg2
       case Map.lookup (withFlags name flags) llvmMapBinop of
         Just (f,_,_) -> addInstruction (f inOp1 inOp2) [outArg]
         Nothing -> shouldnt $ "LLVM Instruction not found: " ++ name


-- | Similar to 'cgenLLVMBinop', but for unary operations on the
-- 'llvmMapUnary'.  There is no LLVM move instruction, a special case has to
-- be made for it. The special move instruction takes one input const/var
-- param, one output variable, and assigns the output variable operand the
-- input operand at the front of the symbol table. The next time the output
-- name is referenced, the symbol table will return the latest assignment to
-- it.
cgenLLVMUnop :: ProcName -> [Ident] -> PrimArg -> PrimArg -> Codegen ()
cgenLLVMUnop "move" flags input output = do
    inRep <- typeRep' $ argType input
    inop <- cgenArg input
    assign (pullName output) inop

cgenLLVMUnop name flags inArg outArg =
    case Map.lookup name llvmMapUnop of
        Just (f,_,_) -> do
            inOp <- cgenArg inArg
            outTy <- lift2 $ argLLVMType outArg
            addInstruction (f inOp outTy) [outArg]
        Nothing -> shouldnt $ "Unknown unary LLVM Instruction " ++ name


-- | Match PrimArgs with the parameters in the given prototype. If a PrimArg's
-- counterpart in the prototype is unneeded, filtered out. Arguments
-- are matched positionally, and are coerced to the type of corresponding
-- parameters.
prepareArgs :: [PrimArg] -> [PrimParam] -> Codegen [PrimArg]
prepareArgs [] []    = return []
prepareArgs [] (_:_) = shouldnt "more parameters than arguments"
prepareArgs (_:_) [] = shouldnt "more arguments than parameters"
prepareArgs (ArgUnneeded _ _:as) (p:ps)
    | paramIsNeeded p = shouldnt $ "unneeded arg for needed param " ++ show p
    | otherwise     = prepareArgs as ps
prepareArgs (a:as) (p@PrimParam{primParamType=ty}:ps) | argFlowDirection a == primParamFlow p = do
    real <- lift2 $ paramIsReal p
    rest <- prepareArgs as ps
    return $ if real then setArgType ty a:rest else rest
prepareArgs (a:as) (p:ps) = do
    shouldnt $ "incompatible flows: invocation=" ++ show (argFlowDirection a) ++ " definition: " ++ show (primParamFlow p)

cgenMaybeLoadReference :: Bool -> PrimArg -> Codegen ()
cgenMaybeLoadReference callIsTailPosition arg@ArgVar { argVarName = name, argVarType = ty, argVarFlow = FlowOutByReference } = do
    currentProto <- gets proto
    outParams <- lift2 $ protoRealParamsWhere paramGoesOut currentProto
    let outParamNames = List.map primParamName outParams
    let isFlowOutParam = name `elem` outParamNames
    logCodegen $ "determining whether to `load` " ++ show name ++ " after call. callIsTailPosition=" ++ show callIsTailPosition ++ " isFlowOutParam=" ++ show isFlowOutParam
    when (not callIsTailPosition || isFlowOutParam) $ do
        -- This call isn't in LPVM tail position,
        -- or the output was one of the outputs of the overall proc.
        -- In this case, we need to perform the load
        op <- maybeGetVar $ show (getRefName name)
        op' <- maybeGetVar $ show name
        var <- case (op, op') of
            -- the corresponding shadow variable `[name]#ref` exists
            (Just var, _) -> return var
            -- the shadow `[name]#ref` variable wasn't created, so instead
            -- we load `[name]` directly
            (Nothing, Just var) -> return var
            _ -> shouldnt $ show name ++ "not defined - when loading reference after call"
        logCodegen $ "doing `load` after call: " ++ show var
        outTy <- lift2 $ argLLVMType arg { argVarFlow = FlowOut }
        loadOp <- doLoad outTy var
        modifySymtab (show name) loadOp
cgenMaybeLoadReference _ _ = return ()

filterPhantomArgs :: [PrimArg] -> Codegen [PrimArg]
filterPhantomArgs = filterM ((not <$>) . lift2 . argIsPhantom)


-- | Code generation for LPVM instructions.
cgenLPVM :: ProcName -> [Ident] -> [PrimArg] -> Codegen ()
cgenLPVM "alloc" _ args@[sizeArg,addrArg] = do
          logCodegen $ "lpvm alloc " ++ show sizeArg ++ " " ++ show addrArg
          let (inputs,outputs) = partitionArgs args
          case inputs of
            [input] -> do
                outTy <- lift2 $ argLLVMType addrArg
                op <- gcAllocate sizeArg outTy
                assign (pullName addrArg) op
            _ ->
              shouldnt $ "alloc instruction with " ++ show (length inputs)
                         ++ " inputs"

cgenLPVM "access" _ args@[addrArg,offsetArg,_,_,val] = do
          logCodegen $ "lpvm access " ++ show addrArg ++ " " ++ show offsetArg
                 ++ " " ++ show val
          baseAddr <- cgenArg addrArg
          finalAddr <- offsetAddr baseAddr iadd offsetArg
          outTy <- lift2 $ argLLVMType val
          logCodegen $ "outTy = " ++ show outTy
          op <- gcAccess finalAddr outTy
          assign (pullName val) op

cgenLPVM "mutate" flags
    [addrArg, outArg, offsetArg, ArgInt 0 intTy, sizeArg, startOffsetArg,
        valArg] | argFlowDirection valArg == FlowIn  = do
         -- Non-destructive case:  copy structure before mutating
          logCodegen $ "lpvm mutate " ++ show addrArg
                       ++ " " ++ show outArg
                       ++ " " ++ show offsetArg ++ " *nondestructive*"
                       ++ " " ++ show sizeArg
                       ++ " " ++ show startOffsetArg
                       ++ " " ++ show valArg
          -- First copy the structure
          outTy <- lift2 $ argLLVMType addrArg
          allocAddr <- gcAllocate sizeArg outTy
          outAddr <- offsetAddr allocAddr iadd startOffsetArg
          assign (pullName outArg) outAddr
          taggedAddr <- cgenArg addrArg
          baseAddr <- offsetAddr taggedAddr isub startOffsetArg
          callMemCpy allocAddr baseAddr sizeArg
          -- Now destructively mutate the copy
          cgenLPVM "mutate" flags
            [outArg, outArg, offsetArg, ArgInt 1 intTy, sizeArg, startOffsetArg,
             valArg]
cgenLPVM "mutate" _
    [addrArg, outArg, offsetArg, ArgInt 1 _, sizeArg, startOffsetArg,
        valArg] | argFlowDirection valArg == FlowIn = do
         -- Destructive case:  just mutate
          logCodegen $ "lpvm mutate " ++ show addrArg
                       ++ " " ++ show outArg
                       ++ " " ++ show offsetArg ++ " *destructive*"
                       ++ " " ++ show sizeArg
                       ++ " " ++ show startOffsetArg
                       ++ " " ++ show valArg
          baseAddr <- cgenArg addrArg
          gcMutate baseAddr offsetArg valArg
          assign (pullName outArg) baseAddr
cgenLPVM "mutate" _  [inArg, outArg, offsetArg, ArgInt 1 _, sizeArg, startOffsetArg,
        refArg@ArgVar { argVarName = refArgName, argVarFlow = FlowTakeReference  }] = do
        shouldnt "lpvm mutate(..., takeReference ...) should be immediately following a call instruction, and should have already been generated"
cgenLPVM "mutate" _
    [_, _, _, ArgInt x _, _, _, _, _] | x == 0 || x == 1 = shouldnt "final argument to mutate should be FlowIn"
cgenLPVM "mutate" _ [_, _, _, destructiveArg, _, _, _] =
      nyi "lpvm mutate instruction with non-constant destructive flag"

cgenLPVM "cast" _ args@[inArg,outArg] =
    case partitionArgs args of
        ([inArg],[outArg]) -> do
            inTy <- lift2 $ argLLVMType inArg
            outTy <- lift2 $ argLLVMType outArg

            castOp <- if argIsConst inArg
                      then do
                          inOp <- cgenArgConst inArg
                          cons <$> consCast inOp outTy
                      else do
                          inOp <- cgenArg inArg
                          doCast inOp outTy

            logCodegen $ "CAST IN  : " ++ show inArg ++ " -> "
                                ++ show (argType inArg)
            logCodegen $ "CAST OUT : " ++ show outArg ++ " -> "
                                ++ show (argType outArg)
            logCodegen $ " CAST OP  : " ++ show castOp

            assign (pullName outArg) castOp

        -- A cast with no outputs:  do nothing
        (_, []) -> return ()
        (inputs,outputs) ->
            shouldnt $ "cast instruction with " ++ show (length inputs)
                       ++ " inputs and " ++ show (length outputs)
                       ++ " outputs"

cgenLPVM "store" _ args = do
    case partitionArgs args of
        ([input, global@(ArgGlobal (GlobalResource res) ty)], []) -> do
            logCodegen $ "lpvm store " ++ show input ++ " " ++ show global
            ty' <- llvmType' ty FlowIn
            global <- getGlobalResource res ty'
            op <- cgenArg input
            store global op
        ([],[]) -> return ()
        _ ->
           shouldnt "lpvm store instruction with wrong arity"

cgenLPVM "load" _ args = do
    case partitionArgs args of
        ([input@(ArgGlobal (GlobalResource res) ty)],
         [output@(ArgVar nm _ _ _ _)]) -> do
            logCodegen $ "lpvm load " ++ show input ++ " " ++ show output
            ty' <- llvmType' ty FlowIn
            global <- getGlobalResource res ty'
            op' <- doLoad ty' global
            assign (show nm) op'
        ([],[]) ->
            return ()
        _ ->
            shouldnt $ "lpvm load instruction with wrong arity " ++ show args

cgenLPVM pname flags args = do
    shouldnt $ "Instruction " ++ pname ++ " arity " ++ show (length args)
               ++ " not implemented."


-- | Codegen all `foreign lpvm mutate(..., takeReference xyz)` calls which occur
-- immediately after a PrimCall.
-- Returns the remaining prims which didn't match the above pattern.
cgenTakeReferences :: [Prim] -> Codegen [Prim]
cgenTakeReferences (prim@(PrimForeign "lpvm" "mutate" _  [inArg, outArg, offsetArg, ArgInt 1 _, sizeArg, startOffsetArg,
        refArg@ArgVar { argVarName = refArgName, argVarFlow = FlowTakeReference  }]):nextPrims) = do
        logCodegen $ "--> Compiling " ++ show prim
        baseAddr <- cgenArg inArg
        outTy <- lift2 $ argLLVMType refArg
        finalAddr <- offsetAddr baseAddr iadd offsetArg
        finalAddrPtr <- doCast finalAddr outTy
        -- take a reference to the field that we're interested in
        assign (show refArgName) finalAddrPtr
        -- assign outArg to be the same address as inArg
        -- This may implicitly write to a pointer (through a `store`
        -- instruction) if outArg is an `outByReference` param
        assign (pullName outArg) baseAddr
        cgenTakeReferences nextPrims
cgenTakeReferences prims = return prims

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


doCast :: Operand -> LLVMAST.Type -> Codegen Operand
doCast op ty2 = do
    (op',caseStr) <- castHelper bitcast zext trunc inttoptr ptrtoint op (typeOf op) ty2
    logCodegen $ "doCast from " ++ show op' ++ " to " ++ show ty2
                 ++ ":  " ++ caseStr
    return op'


consCast :: C.Constant -> LLVMAST.Type -> Codegen C.Constant
consCast c ty2 = do
    (c',caseStr) <- castHelper cbitcast czext ctrunc cinttoptr cptrtoint c (typeOf c) ty2
    logCodegen $ "doCast from " ++ show c' ++ " to " ++ show ty2
                 ++ ":  " ++ caseStr
    return c'


castHelper :: (a -> LLVMAST.Type -> Codegen a) -- bitcast
           -> (a -> LLVMAST.Type -> Codegen a) -- zext
           -> (a -> LLVMAST.Type -> Codegen a) -- trunc
           -> (a -> LLVMAST.Type -> Codegen a) -- inttoptr
           -> (a -> LLVMAST.Type -> Codegen a) -- ptrtoint
           -> a -> LLVMAST.Type -> LLVMAST.Type -> Codegen (a,String)
castHelper _ _ _ _ _ op fromTy toTy
    | fromTy == toTy = return (op, "identity cast")
castHelper _ _ _ i _ op (IntegerType _) ty2@(PointerType _ _) =
    (,"inttoptr") <$> i op ty2
castHelper _ _ _ i _ op (IntegerType _) ty2@(FunctionType _ _ _) =
    (,"inttoptr") <$> i op ty2
castHelper _ _ _ i _ op (IntegerType _) ty2@(ArrayType _ _) =
    (,"inttoptr") <$> i op ty2
castHelper _ _ _ _ p op (PointerType _ _) ty2@(IntegerType _) =
    (,"ptrtoint") <$> p op ty2
castHelper _ _ _ _ p op (FunctionType _ _ _) ty2@(IntegerType _) =
    (,"ptrtoint") <$> p op ty2
castHelper _ _ _ _ p op (ArrayType _ _) ty2@(IntegerType _) =
    (,"ptrtoint") <$> p op ty2
castHelper b z t _ _ op (IntegerType bs1) ty2@(IntegerType bs2)
    | bs1 == bs2 = (,"bitcast no-op") <$> b op ty2
    | bs2 > bs1 = (,"zext") <$> z op ty2
    | bs1 > bs2 = (,"trunc") <$> t op ty2
castHelper b z t _ _ op ty1@(FloatingPointType fp) ty2@(IntegerType bs2)
    | bs1 == bs2 = caseStr <$> b op ty2
    | bs2 > bs1 = caseStr <$> (b op ty' >>= flip z ty2)
    | bs1 > bs2 = caseStr <$> (b op ty' >>= flip t ty2)
  where
    bs1 = getBits ty1
    ty' = IntegerType bs1
    caseStr = (,"fp" ++ show bs1 ++ "-int" ++ show bs2)
castHelper b z t _ _ op ty1@(IntegerType bs1) ty2@(FloatingPointType fp)
    | bs2 == bs1 = caseStr <$> b op ty2
    | bs2 > bs1 = caseStr <$> (z op ty' >>= flip b ty2)
    | bs1 > bs2 = caseStr <$> (t op ty' >>= flip b ty2)
  where
    bs2 = getBits ty2
    ty' = IntegerType bs2
    caseStr = (,"int" ++ show bs1 ++ "-fp" ++ show bs2)
castHelper b _ _ _ _ op ty1 ty2 =
    (,"bitcast from " ++ show ty1 ++ " case") <$> b op ty2


----------------------------------------------------------------------------
-- Helpers for dealing with instructions                                  --
----------------------------------------------------------------------------


-- | Append an 'Instruction' to the current basic block's instruction stack.
-- The return type of the operand value generated by the instruction call is
-- inferred depending on the output arguments. The name is inferred from
-- the output argument's name (LPVM is in SSA form).
addInstruction :: Instruction -> [PrimArg] -> Codegen ()
addInstruction ins outArgs = do
    logCodegen $ "addInstruction " ++ show outArgs ++ " = " ++ show ins
    outTy <- lift2 $ primReturnType outArgs
    logCodegen $ "outTy = " ++ show outTy
    case outArgs of
        [] -> case outTy of
            VoidType -> voidInstr ins
            _        -> shouldnt "empty outArgs cant assign values"
        [outArg] -> do
            outTy <- lift2 $ argLLVMType outArg
            logCodegen $ "outTy = " ++ show outTy
            let outName = pullName outArg
            outop <- instr outTy ins
            assign outName outop
        _ -> do
            outOp <- instr outTy ins
            fields <- structUnPack outOp
            zipWithM_ assign (pullName <$> outArgs) fields


pullName :: PrimArg -> String
pullName ArgVar{argVarName=var} = show var
pullName _                      = shouldnt "Expected variable as output."

-- | Generate an expanding instruction name using the passed flags. This is
-- useful to augment a simple instruction. (Ex: compare instructions can have
-- the comparision type specified as a flag).
withFlags :: ProcName -> [Ident] -> String
withFlags p [] = p
withFlags p f  = unwords (p:f)




----------------------------------------------------------------------------
-- Helpers for primitive arguments                                        --
----------------------------------------------------------------------------


-- | Partition the argument list into inputs and outputs
partitionArgs :: [PrimArg] -> ([PrimArg],[PrimArg])
partitionArgs = List.partition goesIn


-- | Get the LLVM 'Type' of the given primitive output argument
-- list. If there is no output arg, return void_t.
primReturnType :: [PrimArg] -> Compiler Type
primReturnType outputs = mapM argLLVMType outputs >>= primReturnLLVMType


primReturnLLVMType :: [Type] -> Compiler Type
primReturnLLVMType []   = return void_t
primReturnLLVMType [ty] = return ty
primReturnLLVMType tys  = return $ struct_t tys

isLLVMInput :: PrimFlow -> Bool
isLLVMInput FlowIn = True
isLLVMInput FlowOut  = False
-- a `FlowOutByReference` arg is codegen-ed as a pointer input
isLLVMInput FlowOutByReference  = True
-- a `FlowTakeReference` arg is codegen-ed as a pointer output
isLLVMInput FlowTakeReference  = False

goesIn :: PrimArg -> Bool
goesIn = isLLVMInput . argFlowDirection

paramGoesIn :: PrimParam -> Bool
paramGoesIn = isLLVMInput . primParamFlow

paramGoesOut :: PrimParam -> Bool
paramGoesOut = not . paramGoesIn

-- | 'cgenArg' makes an Operand of the input argument.
-- * Variables return a casted version of their respective symbol table operand
-- * Constants are generated with cgenArgConst, then wrapped in `cons`
--
-- Also returns `AllocaTracking`, which specifies if any of these arguments will
-- point to allocas from the current proc.
-- The presence of such allocas breaks core assumptions of the LLVM `tail`
-- attribute, so we need to carefully handle this case.
cgenArgFull :: PrimArg -> Codegen (LLVMAST.Operand, AllocaTracking)
cgenArgFull arg = do
    opds <- gets (stOpds . symtab)
    case Map.lookup arg opds of
        Just opd -> noAlloca $ return opd
        Nothing -> do
            (opd, alloca) <- cgenArg' arg
            addOperand arg opd
            return (opd, alloca)

cgenArg :: PrimArg -> Codegen LLVMAST.Operand
cgenArg a = do
    (op, alloca) <- cgenArgFull a
    return op

-- Tracks whether a given pointer argument comes
-- from an LLVM "alloca" instruction inside the current function.
-- In this case, we are not allowed to mark an LLVM call
-- with `tail` or `musttail`
data AllocaTracking = DoesAlloca | NoAlloca deriving (Eq, Show)

noAlloca :: Codegen LLVMAST.Operand -> Codegen (LLVMAST.Operand, AllocaTracking)
noAlloca s = s >>= (\op -> return (op, NoAlloca))

-- | Makes Operands of the passed arguments, and returns
--   an summary AllocaTracking result for the whole list of arguments.
cgenArgsFull :: [PrimArg] -> Codegen ([LLVMAST.Operand], AllocaTracking)
cgenArgsFull args = do
    args' <- mapM cgenArgFull args
    let allocaTracking = if elem DoesAlloca $ List.map snd args' then DoesAlloca else NoAlloca
    return (List.map fst args', allocaTracking)

cgenArg' :: PrimArg -> Codegen (LLVMAST.Operand, AllocaTracking)
cgenArg' var@ArgVar{argVarName=name, argVarType=ty, argVarFlow=flow@FlowOutByReference} = do
    op <- maybeGetVar (show name)
    currentProto <- gets proto
    outParams <- lift2 $ protoRealParamsWhere paramGoesOut currentProto
    let outParamNames = List.map primParamName outParams
    if isNothing op || name `elem` outParamNames then do
        -- This variable wasn't already defined or was an output param of the
        -- current proc (which get set to `Undef`, so not really explicitly defined)
        -- In this case we need to allocate space on the stack and create a
        -- shadow reference variable to it.
        allocaTy <- llvmType' ty FlowOut
        alloca <- doAlloca allocaTy
        logCodegen $ "Performing %" ++ show name ++ " = alloca " ++ show allocaTy
        let refName = getRefName name
        assign (show refName) alloca
        -- Supply the shadow reference variable as argument to this proc.
        op <- castVar refName ty flow
        return (op,DoesAlloca)
    else noAlloca $ castVar name ty flow
cgenArg' var@ArgVar{argVarName=nm, argVarType=ty, argVarFlow=flow} = noAlloca $ castVar nm ty flow
cgenArg' (ArgUnneeded _ _) = shouldnt "Trying to generate LLVM for unneeded arg"
cgenArg' arg@(ArgClosure ps args ty) = do
    logCodegen $ "cgenArg of " ++ show arg
    args' <- neededFreeArgs ps args
    if all argIsConst args'
    then do
        noAlloca $ cons <$> cgenArgConst arg
    else do
        fnOp <- cons <$> cgenFuncRef ps
        (envArgs, allocaTracking) <- cgenArgsFull (setArgType intType <$> args')
        mem <- gcAllocate (toInteger (wordSizeBytes * (1 + length args))
                                      `ArgInt` intType) address_t
        memPtr <- inttoptr mem (ptr_t address_t)
        mapM_ (\(idx,arg) -> do
            let getEltPtr = getElementPtrInstr memPtr [idx]
            accessPtr <- instr (ptr_t address_t) getEltPtr
            store accessPtr arg
            ) $ zip [0..] (fnOp:envArgs)
        return (mem, allocaTracking)
cgenArg' arg = do
    noAlloca $ cons <$> cgenArgConst arg


-- returns the name of a "shadow" variable which is a pointer to the
-- underlying variable
getRefName :: PrimVarName -> PrimVarName
getRefName name = name { primVarName = primVarName name ++ "#ref" }


-- Generates a constant for a constant PrimArg, casted to the respective type
-- * Ints, Floats, Chars, Undefs are of respective LLVMTypes
-- * Strings are handled based on string variant
--   * CString    - ptr to global constant of [N x i8]
--   * WybeString - ptr to global constant of { i64, i64 } with the second
--                  element being as though it were a CString. This representation
--                  is to comply with the stdlib string implementation
cgenArgConst :: PrimArg -> Codegen C.Constant
cgenArgConst arg = do
    opds <- gets (stOpds . symtab)
    case Map.lookup arg opds of
        Just (ConstantOperand constant) -> return constant
        Just other -> shouldnt $ "cgenArgConst with " ++ show other
        Nothing -> do
            opd <- cgenArgConst' arg
            addOperand arg $ ConstantOperand opd
            return opd

cgenArgConst' :: PrimArg -> Codegen C.Constant
cgenArgConst' arg@(ArgInt val _) = do
    toTy <- lift2 $ argLLVMType arg
    case toTy of
        IntegerType bs -> return $ C.Int bs val
        _ -> consCast (C.Int (fromIntegral wordSize) val) toTy
cgenArgConst' arg@(ArgFloat val _) = do
    toTy <- lift2 $ argLLVMType arg
    case toTy of
        FloatingPointType DoubleFP -> return $ C.Float $ F.Double val
        _ -> consCast (C.Float $ F.Double val) toTy
cgenArgConst' (ArgString s WybeString ty) = do
    conPtr <- snd <$> addStringConstant s
    let strType = struct_t [address_t, address_t]
    let strStruct = C.Struct Nothing False
                  [ C.Int (fromIntegral wordSize) (fromIntegral $ length s)
                  , C.PtrToInt conPtr address_t ]
    strName <- addGlobalConstant strType strStruct
    let strPtr = C.GlobalReference (ptr_t strType) strName
    let strElem = C.GetElementPtr True strPtr [C.Int 32 0, C.Int 32 0]
    consCast strElem address_t
cgenArgConst' (ArgString s CString _) = do
    (_, conPtr) <- addStringConstant s
    let strElem = C.GetElementPtr True conPtr [C.Int 32 0, C.Int 32 0]
    consCast strElem address_t
cgenArgConst' arg@(ArgChar c _) = do
    let val = integerOrd c
    toTy <- lift2 $ argLLVMType arg
    case toTy of
        IntegerType bs -> return $ C.Int bs val
        _ -> consCast (C.Int (fromIntegral wordSize) val) toTy
cgenArgConst' arg@(ArgUndef _) = do
    llty <- lift2 $ argLLVMType arg
    return $ C.Undef llty
cgenArgConst' (ArgClosure ps args ty) = do
    fnRef <- cgenFuncRef ps
    args' <- neededFreeArgs ps args
    constArgs <- mapM cgenArgConst (setArgType intType <$> args')
    let arrElems = fnRef:constArgs
    let arrTy = array_t (fromIntegral $ length arrElems) address_t
    let arr = C.Array address_t arrElems
    conArrPtr <- C.GlobalReference (ptr_t arrTy) <$> addGlobalConstant arrTy arr
    let rawElem = C.GetElementPtr True conArrPtr [C.Int 32 0, C.Int 32 0]
    consCast rawElem address_t
cgenArgConst' arg = shouldnt $ "cgenArgConst of " ++ show arg


cgenFuncRef :: ProcSpec -> Codegen C.Constant
cgenFuncRef ps = do
    addExternClosure ps
    let fName = LLVMAST.Name $ fromString $ show ps
    psType <- HigherOrderType defaultProcModifiers . (primParamTypeFlow <$>)
          <$> primActualParams ps
    psTy <- llvmFuncType psType
    logCodegen $ "  with type " ++ show psType
    let conFn = C.GlobalReference psTy fName
    return $ C.PtrToInt conFn address_t

castVar :: PrimVarName -> TypeSpec -> PrimFlow -> Codegen Operand
castVar nm ty flow = do
    toTy <- llvmType' ty flow
    lift2 $ logBlocks $ "Coercing var " ++ show nm ++ " to " ++ show ty
    varOp <- getVar (show nm)
    doCast varOp toTy


primActualParams :: ProcSpec -> Codegen [PrimParam]
primActualParams pspec = lift2 $ do
    primParams <- protoRealParams . procImplnProto . procImpln
              =<< getProcDef pspec
    let nonFreeParams = List.filter ((/= Free) . primParamFlowType) primParams
    ifM (isClosureProc pspec)
        (return $ setPrimParamType AnyType <$> envPrimParam : nonFreeParams)
        (return nonFreeParams)


neededFreeArgs :: ProcSpec -> [PrimArg] -> Codegen [PrimArg]
neededFreeArgs pspec args = lift2 $ do
    params <- List.filter ((==Free) . primParamFlowType) . primProtoParams
              . procImplnProto . procImpln <$> getProcDef pspec
    List.map snd <$> filterM (paramIsReal . fst) (zip params args)


addExternClosure :: ProcSpec -> Codegen ()
addExternClosure ps@(ProcSpec mod _ _ _) = do
    args <- (primParamToArg <$>) <$> primActualParams ps
    thisMod <- lift2 getModuleSpec
    fileMod <- lift2 $ getModule modRootModSpec
    unless (thisMod == mod || maybe False (`List.isPrefixOf` mod) fileMod)
        $ addExtern $ PrimCall 0 ps args univGlobalFlows


addStringConstant :: String -> Codegen (LLVMAST.Type, C.Constant)
addStringConstant s = do
    let strCon = makeStringConstant s
    let conType = array_t (fromIntegral $ length s + 1) char_t
    let ptrConType = ptr_t conType
    globalConst <- addGlobalConstant conType strCon
    return (ptrConType, C.GlobalReference ptrConType globalConst)


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
-- Symbol Table                                                           --
----------------------------------------------------------------------------

-- | Store a local variable on the front of the symbol table.
-- |
-- | If the local variable happens to be an outByReference parameter of the
-- | current function we're generating, then we instead "write" the variable
-- | using a store instruction.
assign :: String -> Operand -> Codegen ()
assign var op = do
    params <- gets (primProtoParams . proto)
    let outByRefParamNames = List.map (show . primParamName) $ List.filter (\param -> FlowOutByReference == primParamFlow param) params
    if var `elem` outByRefParamNames then do
      logCodegen $ "assign outByReference " ++ var ++ " = " ++ show op ++ ":" ++ show (typeOf op)
      locOp <- getVar var
      locOp' <- doCast locOp (ptr_t (typeOf op))
      store locOp' op
      -- also store this operand in the symtab, for the case where
      -- we access this outByReference param later on in the proc
      modifySymtab var op
    else modifySymtab var op

----------------------------------------------------------------------------
-- Instruction maps                                                       --
----------------------------------------------------------------------------


-- | A map of arithmetic binary operations supported through LLVM to
-- their Codegen module counterpart.
llvmMapBinop :: Map String
                (Operand -> Operand -> Instruction,
                 TypeFamily, TypeRepresentation -> TypeRepresentation)
llvmMapBinop =
    Map.fromList [
            -- Integer arithmetic
            ("add",  (iadd, IntFamily, id)),
            ("sub",  (isub, IntFamily, id)),
            ("mul",  (imul, IntFamily, id)),
            ("udiv", (idiv, IntFamily, id)),
            ("sdiv", (sdiv, IntFamily, id)),
            ("urem", (urem, IntFamily, id)),
            ("srem", (srem, IntFamily, id)),
            -- Integer comparisions
            ("icmp_eq",  (icmp IP.EQ,  IntFamily, const $ Bits 1)),
            ("icmp_ne",  (icmp IP.NE,  IntFamily, const $ Bits 1)),
            ("icmp_ugt", (icmp IP.UGT, IntFamily, const $ Bits 1)),
            ("icmp_uge", (icmp IP.UGE, IntFamily, const $ Bits 1)),
            ("icmp_ult", (icmp IP.ULT, IntFamily, const $ Bits 1)),
            ("icmp_ule", (icmp IP.ULE, IntFamily, const $ Bits 1)),
            ("icmp_sgt", (icmp IP.SGT, IntFamily, const $ Bits 1)),
            ("icmp_sge", (icmp IP.SGE, IntFamily, const $ Bits 1)),
            ("icmp_slt", (icmp IP.SLT, IntFamily, const $ Bits 1)),
            ("icmp_sle", (icmp IP.SLE, IntFamily, const $ Bits 1)),
            -- Bitwise operations
            ("shl",  (shl,  IntFamily, id)),
            ("lshr", (lshr, IntFamily, id)),
            ("ashr", (ashr, IntFamily, id)),
            ("or",   (lOr,  IntFamily, id)),
            ("and",  (lAnd, IntFamily, id)),
            ("xor",  (lXor, IntFamily, id)),

            -- Floating point arithmetic
            ("fadd", (fadd, FloatFamily, id)),
            ("fsub", (fsub, FloatFamily, id)),
            ("fmul", (fmul, FloatFamily, id)),
            ("fdiv", (fdiv, FloatFamily, id)),
            ("frem", (frem, FloatFamily, id)),
            -- Floating point comparisions
            ("fcmp_eq",  (fcmp FP.OEQ, FloatFamily, const $ Bits 1)),
            ("fcmp_ne",  (fcmp FP.ONE, FloatFamily, const $ Bits 1)),
            ("fcmp_slt", (fcmp FP.OLT, FloatFamily, const $ Bits 1)),
            ("fcmp_sle", (fcmp FP.OLE, FloatFamily, const $ Bits 1)),
            ("fcmp_sgt", (fcmp FP.OGT, FloatFamily, const $ Bits 1)),
            ("fcmp_sge", (fcmp FP.OGE, FloatFamily, const $ Bits 1))
           ]

-- | A map of unary llvm operations wrapped in the 'Codegen' module.
llvmMapUnop :: Map String
               (Operand -> Type -> Instruction, TypeFamily, TypeFamily)
llvmMapUnop =
    Map.fromList [
            ("uitofp", (uitofp, IntFamily, FloatFamily)),
            ("sitofp", (sitofp, IntFamily, FloatFamily)),
            ("fptoui", (fptoui, FloatFamily, IntFamily)),
            ("fptosi", (fptosi, FloatFamily, IntFamily))
           ]



----------------------------------------------------------------------------
-- Helpers                                                                --
----------------------------------------------------------------------------


llvmType :: TypeSpec -> PrimFlow -> Compiler LLVMAST.Type
llvmType ty flow = repLLVMType flow <$> typeRep ty

llvmType' :: TypeSpec -> PrimFlow -> Codegen LLVMAST.Type
llvmType' ty flow = lift2 $ llvmType ty flow

primParamLLVMType :: PrimParam -> Compiler LLVMAST.Type
primParamLLVMType param = llvmType (primParamType param) (primParamFlow param)

argLLVMType :: PrimArg -> Compiler LLVMAST.Type
argLLVMType arg = llvmType (argType arg) (argFlowDirection arg)

llvmFuncType :: TypeSpec -> Codegen LLVMAST.Type
llvmFuncType ty = do
    tyRep <- typeRep' ty
    case tyRep of
        Func ins outs -> do
            let inTys = _repLLVMType <$> ins
            let outTys = _repLLVMType <$> outs
            outTy <- lift2 $ primReturnLLVMType outTys
            return $ ptr_t $ FunctionType outTy inTys False
        _ -> shouldnt $ "llvmFuncType of " ++ show ty


llvmClosureType :: TypeSpec -> Codegen LLVMAST.Type
llvmClosureType (HigherOrderType mods@ProcModifiers{modifierDetism=detism} tys)
    = llvmFuncType
        $ HigherOrderType mods{modifierDetism=Det}
        $ setTypeFlowType AnyType
       <$> TypeFlow AnyType ParamIn : tys
           ++ [TypeFlow AnyType ParamOut | detism == SemiDet]

llvmClosureType ty = shouldnt $ "llvmClosureType on " ++ show ty



typeRep :: TypeSpec -> Compiler TypeRepresentation
typeRep ty =
    let err = shouldnt $ "llvmType applied to InvalidType or unknown type ("
            ++ show ty
            ++ ")"
    in fromMaybe err <$> lookupTypeRepresentation ty

typeRep' :: TypeSpec -> Codegen TypeRepresentation
typeRep' = lift2 . typeRep


-- |The LLVM type of the specified module spec; error if it's not a type.
moduleLLVMType :: ModSpec -> Compiler LLVMAST.Type
moduleLLVMType mspec =
    _repLLVMType . trustFromJust "moduleLLVMType of non-type" <$> lookupModuleRepresentation mspec

repLLVMType :: PrimFlow -> TypeRepresentation -> LLVMAST.Type
repLLVMType FlowOutByReference tyRep = ptr_t $ _repLLVMType tyRep
repLLVMType FlowTakeReference  tyRep = ptr_t $ _repLLVMType tyRep
repLLVMType _ tyRep = _repLLVMType tyRep

_repLLVMType :: TypeRepresentation -> LLVMAST.Type
_repLLVMType Address        = address_t
_repLLVMType (Bits bits)
  | bits == 0              = void_t
  | bits >  0              = int_c $ fromIntegral bits
  | otherwise              = shouldnt $ "unsigned type with negative width "
                                        ++ show bits
_repLLVMType (Signed bits)
  | bits > 0               = int_c $ fromIntegral bits
  | otherwise              = shouldnt $ "signed type with non-positive width "
                                        ++ show bits
_repLLVMType (Floating 16)  = FloatingPointType HalfFP
_repLLVMType (Floating 32)  = FloatingPointType FloatFP
_repLLVMType (Floating 64)  = FloatingPointType DoubleFP
_repLLVMType (Floating 80)  = FloatingPointType X86_FP80FP
_repLLVMType (Floating 128) = FloatingPointType FP128FP
_repLLVMType (Floating b)   = shouldnt $ "unknown floating point width "
                                        ++ show b
_repLLVMType (Func _ _)     = address_t


------------------------------------------------------------------------------
-- -- Creating LLVM AST module from global definitions                    --
------------------------------------------------------------------------------

-- | Initialize and fill a new LLVMAST.Module with the translated
-- global definitions (extern declarations and defined functions)
-- of LPVM procedures in a module.
newLLVMModule :: String -> String -> [ProcDefBlock] -> TranslationState
              -> [ResourceSpec] -> Compiler LLVMAST.Module
newLLVMModule name fname blocks (TranslationState _ consts vars exts) ress = do
    let defs = List.map blockDef blocks
        varDefs = LLVMAST.GlobalDefinition <$> Map.elems vars
        constDefs = LLVMAST.GlobalDefinition <$> Map.elems consts
    resDefs <- catMaybes <$> mapM globalResourceExtern ress
    extDefs <- mapM declareExtern exts
    let exs' = uniqueExterns (resDefs ++ varDefs ++ constDefs)
            ++ uniqueExterns (extDefs ++ [mallocExtern] ++ intrinsicExterns)
    return $ modWithDefinitions name fname $ exs' ++ defs


globalResourceExtern :: ResourceSpec -> Compiler (Maybe LLVMAST.Definition)
globalResourceExtern res = do
    resMbTy <- canonicaliseResourceSpec Nothing "newLLVMModule" res
    case resMbTy of
        (res', Just ty) ->
            ifM (typeIsPhantom ty)
                (return Nothing)
                (typeRep ty >>= makeGlobalResourceVariable res' . _repLLVMType
                    <&> Just . LLVMAST.GlobalDefinition)
        _ -> shouldnt $ "globalResourceExtern " ++ show res


-- | Filter out non-unique externs
uniqueExterns :: [LLVMAST.Definition] -> [LLVMAST.Definition]
uniqueExterns exs = List.nubBy sameDef exs
  where
    sameDef (LLVMAST.GlobalDefinition g1) (LLVMAST.GlobalDefinition g2)
      = G.name g1 == G.name g2
    sameDef _ _ = False


-- | Create a new LLVMAST.Module with the given name, and fill it with the
-- given global definitions.
modWithDefinitions :: String -> String -> [LLVMAST.Definition] -> LLVMAST.Module
modWithDefinitions nm filename defs =
    LLVMAST.Module (toSBString nm) (toSBString filename) Nothing Nothing defs


-- | Build an extern declaration definition from a given LPVM primitive.
declareExtern :: Prim -> Compiler LLVMAST.Definition
declareExtern (PrimForeign "c" name _ args) = do
    let (inArgs,outArgs) = partitionArgs args
    fnargs <- mapM makeExArg $ zip [1..] inArgs
    retty <- primReturnType outArgs
    let ex = externalC retty name fnargs
    return ex

declareExtern (PrimForeign otherlang name _ _) =
    shouldnt $ "Don't know how to declare extern foreign function " ++ name
      ++ " in language " ++ otherlang

declareExtern (PrimHigher _ var _) =
    shouldnt $ "Don't know how to declare extern function var " ++ show var

declareExtern (PrimCall _ pspec@(ProcSpec m n _ _) args _) = do
    let (inArgs,outArgs) = partitionArgs args
    retty <- primReturnType outArgs
    fnargs <- mapM makeExArg $ zip [1..] inArgs
    return $ externalWybe retty (show pspec) fnargs


-- | Helper to make arguments for an extern declaration.
makeExArg :: (Word, PrimArg) -> Compiler (Type, LLVMAST.Name)
makeExArg (index,arg) = do
    ty <- argLLVMType arg
    let nm = LLVMAST.UnName index
    return (ty, nm)


-- | An extern for wybe_malloc
mallocExtern :: LLVMAST.Definition
mallocExtern =
    let ext_arg = [(LLVMAST.IntegerType 32, LLVMAST.Name $ toSBString "size")]
    in externalC (ptr_t (int_c 8)) "wybe_malloc" ext_arg


-- | Externs for any intrinsics we might need.  For now, just memcpy.
-- Intrinsics are built in to LLVM, so they're always available.
intrinsicExterns :: [LLVMAST.Definition]
intrinsicExterns =
    [externalC void_t "llvm.memcpy.p0i8.p0i8.i32" [
        (ptr_t (int_c 8), LLVMAST.Name $ toSBString "dest"),
        (ptr_t (int_c 8), LLVMAST.Name $ toSBString "src"),
        (int_t, LLVMAST.Name $ toSBString "len"),
        (int_c 1, LLVMAST.Name $ toSBString "isvolatile")]
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

-- $ functions

-- | Call "wybe_malloc" from external C shared lib. Returns an i8* pointer.
-- XXX What will be the type of 'size' we pass to extern C's malloc?
callWybeMalloc :: PrimArg -> Codegen Operand
callWybeMalloc size = do
    let outTy = ptr_t (int_c 8)
    let fnName = LLVMAST.Name $ toSBString "wybe_malloc"
    sizeOp <- cgenArg size
    logCodegen $ "callWybeMalloc casting size " ++ show sizeOp
                 ++ " to " ++ show int_t
    inops <- (:[]) <$> doCast sizeOp int_t
    let ins =
          callC
          (externf (ptr_t (FunctionType outTy (typeOf <$> inops) False)) fnName)
          inops
    instr outTy ins


-- | Invoke the LLVM memcpy intrinsic to copy a specified number of bytes of
-- memory from a source address to a non-overlapping destination address.
callMemCpy :: Operand -> Operand -> PrimArg -> Codegen ()
callMemCpy dst src bytes = do
    let fnName = LLVMAST.Name $ toSBString "llvm.memcpy.p0i8.p0i8.i32"
    let charptr_t = ptr_t (int_c 8)
    dstCast <- doCast dst charptr_t
    srcCast <- doCast src charptr_t
    bytesOp <- cgenArg bytes
    bytesCast <- doCast bytesOp int_t
    -- dstCast <- instr charptr_t $ LLVMAST.BitCast dst charptr_t []
    -- srcCast <- instr charptr_t $ LLVMAST.BitCast src charptr_t []
    -- bytesOp <- cgenArg bytes
    -- bytesCast <- instr int_t   $ LLVMAST.BitCast bytesOp int_t []
    let inops = [dstCast, srcCast, bytesCast,
                 cons (C.Int 1 0)]
    let ins =
          callC
          (externf (ptr_t (FunctionType void_t (typeOf <$> inops) False))
           fnName)
          inops
    voidInstr ins


-- | Call the external C-library function for malloc and return
-- the bitcasted pointer to that location.
gcAllocate :: PrimArg -> LLVMAST.Type -> Codegen Operand
gcAllocate size castTy = do
    voidPtr <- callWybeMalloc size
    doCast voidPtr castTy


-- | Index and return the value in the memory field referenced by the pointer
-- at the given offset.
-- If expected return type/value at that location is a pointer, then
-- the instruction inttoptr should precede the load instruction.
gcAccess :: Operand -> LLVMAST.Type -> Codegen Operand
gcAccess ptr outTy = do
    logCodegen $ "gcAccess " ++ show ptr ++ " " ++ show outTy
    let ptrTy = ptr_t outTy
    ptr' <- doCast ptr ptrTy
    logCodegen $ "doCast produced " ++ show ptr'

    -- TODO: is getelementptr here redundant? we always index the 0th thing...
    let getel = getElementPtrInstr ptr' [0]
    logCodegen $ "getel = " ++ show getel
    accessPtr <- instr ptrTy getel
    logCodegen $ "accessPtr = " ++ show accessPtr
    let loadInstr = load accessPtr
    logCodegen $ "loadInstr = " ++ show loadInstr
    instr outTy $ loadInstr


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
    valTy <- lift2 $ argLLVMType valArg
    let ptrTy = ptr_t valTy
    ptr' <- inttoptr finalAddr ptrTy
    logCodegen $ "inttoptr " ++ show finalAddr ++ " " ++ show ptrTy
    logCodegen $ "inttoptr produced " ++ show ptr'

    let getel = getElementPtrInstr ptr' [0]
    logCodegen $ "getel = " ++ show getel
    accessPtr <- instr ptrTy getel
    logCodegen $ "accessPtr = " ++ show accessPtr
    val <- cgenArg valArg
    store accessPtr val


-- | Get the LLVMAST.Type the given pointer type points to.
pullFromPointer :: LLVMAST.Type -> LLVMAST.Type
pullFromPointer (PointerType ty _) = ty
pullFromPointer pty                = shouldnt $ "Not a pointer: " ++ show pty



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
logCodegen s = lift2 $ logBlocks s
