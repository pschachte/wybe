--  File     : Blocks.hs
--  RCS      : $Id$
--  Author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

module Blocks
       where

import           AST
import           BinaryFactory
import           Codegen
import           Control.Monad
import           Control.Monad.Trans (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import qualified Data.Binary as B
import           Data.Char (ord)
import           Data.List as List
import           Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Word (Word32)
import           Debug.Trace
import qualified LLVM.General.AST as LLVMAST
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.Float as F
import qualified LLVM.General.AST.FloatingPointPredicate as FP
import qualified LLVM.General.AST.Global as G
import           LLVM.General.AST.Instruction
import qualified LLVM.General.AST.IntegerPredicate as IP
import           LLVM.General.AST.Operand
import           LLVM.General.AST.Type
import           LLVM.General.Context
import           LLVM.General.Module
import           LLVM.General.PrettyPrint
import           Options (LogSelection (Blocks))

----------------------------------------------------------------------------
-- LLVM Compiler Monad                                                    --
----------------------------------------------------------------------------
-- | The llvm compiler monad is a state transformer monad carrying the
--  clause compiler state over the compiler monad.
type LLVMComp = StateT LLVMCompState Compiler

-- | Hold some state while converting a AST.Module's procedures into LLVMAST
-- definitions.
data LLVMCompState = LLVMCompState {
      neededExterns    :: [Prim] -- ^ collect required extern declarations
    , neededGlobalVars :: [G.Global] -- ^ collect required global constants
    , modName          :: String
    , modProtos        :: [PrimProto] -- ^ All procedure prototypes in Module
    }

-- | Update the LLVMCompState list of primitives which require extern
-- declarations. Don't add the primitive again if it has been added
-- previously.
needExterns :: [Prim] -> LLVMComp ()
needExterns ps =
    do ex <- gets neededExterns
       let uniqueExs = List.nubBy samePrimName (ex ++ ps)
       logBlocks $ "Externs: " ++ (show uniqueExs)
       modify $ \s -> s { neededExterns = uniqueExs }
       return ()

-- | Predicate to test if two Prims have the same name.
samePrimName :: Prim -> Prim -> Bool
samePrimName (PrimCall p1 _) (PrimCall p2 _) = p1 == p2
samePrimName (PrimForeign _ p1 _ _) (PrimForeign _ p2 _ _) = p1 == p2
samePrimName PrimNop PrimNop = True
samePrimName _ _ = False


-- | Update the LLVMCompState list of global variables. These global variables
-- will be defined at the top of a module. Global variables get implicitely
--allocated and will be referenced using an element pointer wherever needed.
needGlobalVars :: [G.Global] -> LLVMComp ()
needGlobalVars gs =
    do new <- gets neededGlobalVars
       modify $ \s -> s { neededGlobalVars = new ++ gs }
       return ()

-- | Initialize the LLVMCompState
initLLVMComp :: String -> [PrimProto] -> LLVMCompState
initLLVMComp modName modProtos = LLVMCompState [] [] modName modProtos


evalLLVMComp :: String -> [PrimProto] -> LLVMComp t -> Compiler t
evalLLVMComp modName modProtos llcomp =
    evalStateT llcomp (initLLVMComp modName modProtos)


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
       let modName = showModSpec thisMod
       logBlocks' $ "*** Translating Module: " ++ modName
       (names, procs) <- fmap unzip $
                         getModuleImplementationField (Map.toList . modProcs)
       -- Collect all procedure prototypes in the module
       let protos = List.map extractLPVMProto (concat procs)

       -- Collect prototypes of imported modules
       imports <- getModuleImplementationField (keys . modImports)
       importProtos <- mapM getPrimProtos
                         (List.filter (not . isStdLib) imports)
       let allProtos = protos ++ (concat importProtos)

       logBlocks' $ "Prototypes:\n\t"
                         ++ intercalate "\n\t" (List.map show allProtos)
       -- Translate
       procs' <- mapM (mapM (translateProc modName allProtos) .
                       (List.filter (not . emptyProc))) procs
                         
       -- Listing all known types
       knownTypesSet <- fmap (List.map snd) $
           getModuleImplementationField (Map.toList . modKnownTypes)
       let knownTypes = concat $ List.map Set.toList knownTypesSet
       trs <- mapM lookupTypeRepresentation knownTypes
       logWrapWith '.' (show trs) 

       -- Init LLVM Module and fill it
       let llmod = newLLVMModule (showModSpec thisMod) procs'
       updateImplementation (\imp -> imp { modLLVM = Just llmod })
       -- logBlocks' $ showPretty llmod
       finishModule
       logBlocks' $ "*** Exiting Module " ++ showModSpec thisMod ++ " ***"


-- | Extract the LPVM compiled primitive from the procedure definition.
extractLPVMProto :: ProcDef -> PrimProto
extractLPVMProto procdef =
    let (ProcDefPrim proto _) = procImpln procdef in proto

-- | Go into a (compiled) Module and pull out the PrimProto implementation
-- of all ProcDefs in the module implementation.
getPrimProtos :: ModSpec -> Compiler [PrimProto]
getPrimProtos modSpec = do
    (_, procs) <- fmap (unzip . Map.toList . modProcs)
        $ getLoadedModuleImpln modSpec
    let protos = List.map extractLPVMProto (concat procs)
    return protos

-- | Filter for avoiding the standard library modules    
isStdLib :: ModSpec -> Bool
isStdLib [] = False
isStdLib (m:_) = m == "wybe"
    
    

-- | Predicate to test for procedure definition with an empty body.
emptyProc :: ProcDef -> Bool
emptyProc p = case procImpln p of
  ProcDefSrc pps -> List.null pps
  ProcDefPrim _ body -> List.null $ bodyPrims body
  _ -> False



-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). Each ProcDef is converted into a Global
-- Definition in a LLVM Module by translating it's primitives.  Translated
-- procedures (ProcDefBlocks ...) can optionally have a list of extern
-- declarations (which are also global definitions) if any primitive is going
-- to call some foreign function (mostly C).  Translated procedures will also
-- require some global variable/constant declarations which is represented as
-- G.Global values in the neededGlobalVars field of LLVMCompstate. All in all,
-- externs and globals go on the top of the module.
translateProc :: String -> [PrimProto]
              -> ProcDef 
              -> Compiler ProcDef
translateProc modName modProtos proc =
    evalLLVMComp modName modProtos $ do
      let def@(ProcDefPrim proto body) = procImpln proc
      logBlocks $ "\n" ++ replicate 70 '=' ++ "\n"
      logBlocks $ "In Module: " ++ modName ++ ", creating definition of: "
      logBlocks $ show def ++ "\n" ++ replicate 50 '-' ++ "\n"
      body' <- compileBodyToBlocks proto body
      ex <- gets neededExterns
      gs <- gets neededGlobalVars
      let externs = List.map declareExtern ex
      let globals = List.map LLVMAST.GlobalDefinition gs
      let lldef = makeGlobalDefinition modName proto body'
      logBlocks $ showPretty lldef
      let procblocks = ProcDefBlocks proto lldef (externs ++ globals)
      return $ proc { procImpln = procblocks}


-- | Create LLVM's module level Function Definition from the LPVM procedure
-- prototype and it's body as a list of BasicBlock(s). The return type of such
-- a definition is decided based on the Ouput parameter of the procedure, or
-- is made to be phantom.
makeGlobalDefinition :: String
                     -> PrimProto
                     -> [LLVMAST.BasicBlock]
                     -> LLVMAST.Definition
makeGlobalDefinition modName proto bls =
    globalDefine retty label fnargs bls
    where
      params = List.filter (not . isPhantomParam) (primProtoParams proto)
      isMain = primProtoName proto == ""
      -- *The top level procedure will be labelled main.
      label = modName ++ "." ++
        if isMain then "main" else primProtoName proto
      retty = if isMain then int_t else primOutputType params
      inputs = List.filter isInputParam params
      fnargs = List.map makeFnArg inputs

-- | Predicate to check if a primitive's parameter is of input flow (input)
-- and the param is needed (inferred by it's param info field)
isInputParam :: PrimParam -> Bool
isInputParam p = primParamFlow p == FlowIn &&
  (paramInfoUnneeded . primParamInfo) p == False

-- | Convert a primitive's input parameter to LLVM's Definition parameter.
makeFnArg :: PrimParam -> (Type, LLVMAST.Name)
makeFnArg arg = (ty, nm)
    where
      ty = typed $ primParamType arg
      nm = LLVMAST.Name (show $ primParamName arg)

-- | Open the Out parameter of a primitive (if there is one) into it's
-- inferred 'Type' and name.
primOutputType :: [PrimParam] -> Type
primOutputType params =
    let outputs = List.filter isOutputParam params in
    case length outputs of
        0 -> void_t
        1 -> (typed . primParamType . head) outputs
        n -> struct_t $ List.map (typed . primParamType) outputs


isPhantomParam :: PrimParam -> Bool
isPhantomParam p = case (typeName . primParamType) p of
                     "phantom" -> True
                     _ -> False

isOutputParam :: PrimParam -> Bool
isOutputParam p = not (isInputParam p || isPhantomParam p) &&
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
compileBodyToBlocks :: PrimProto           -- procedure prototype
                    -> ProcBody              -- procedure body
                    -> LLVMComp [LLVMAST.BasicBlock]
compileBodyToBlocks proto body =
    do modName <- gets Blocks.modName
       modProtos <- gets Blocks.modProtos
       let codestate = execCodegen modName modProtos (doCodegenBody proto body)
       let exs = externs codestate
       let gVars = globalVars codestate
       -- Copy to LLVMCompState state
       needExterns exs
       needGlobalVars gVars
       return $ createBlocks codestate

-- | Generate LLVM instructions for a procedure.
doCodegenBody :: PrimProto -> ProcBody -> Codegen ()
doCodegenBody proto body =
    do let params = primProtoParams proto
       entry <- addBlock entryBlockName
       -- Start with creation of blocks and adding instructions to it
       setBlock entry
       mapM_ assignParam $ List.filter (not . isOutputParam) params
       codegenBody body   -- Codegen on body prims
       builtOp <- buildOutputOp params

       case bodyFork body of
         NoFork -> case (primProtoName proto) == "" of
           -- Empty primitive prototype is the main function in LLVM
           True -> mainReturnCodegen
           False -> do ret builtOp
                       return ()
         (PrimFork var _ fbody) -> codegenForkBody var fbody builtOp


-- | Generate code for returning integer exit code at the end main
-- function.
mainReturnCodegen :: Codegen ()
mainReturnCodegen = do
    ptr <- instr (ptr_t int_t) (alloca int_t)
    let retcons = cons (C.Int 32 0)
    store ptr retcons
    ret (Just retcons)
    return ()


-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table. Don't assign if phantom.
assignParam :: PrimParam -> Codegen ()
assignParam p =
    do let nm = show (primParamName p)
       let ty = primParamType p
       case (typeName ty) of
         "phantom" -> return () -- No need to assign phantoms
         _ -> case (paramInfoUnneeded . primParamInfo) p of
           True -> return ()    -- unneeded param
           -- False -> do
           --     let varType = typed ty
           --     ptr <- instr (ptr_t varType) $ alloca varType
           --     store ptr (localVar varType nm)
           --     op <- instr varType $ load ptr
           --     assign nm op
           False -> assign nm (localVar (typed ty) nm)


-- | Retrive or build the output operand from the given parameters.
-- For no valid ouputs, return Nothing
-- For 1 single output, retrieve it's assigned operand from the symbol
-- table, and for multiple ouputs, generate code for creating an valid
-- structure, pack the operands into it and return it.
buildOutputOp :: [PrimParam] -> Codegen (Maybe Operand)
buildOutputOp params = do
    let outParams = List.filter isOutputParam params
    outputsMaybe <- mapM (getVarMaybe . show . primParamName) outParams
    let outputs = catMaybes outputsMaybe

    case length outputs of
        -- * No valid output
        0 -> return Nothing
        -- * single output case
        1 -> return $ Just $ head outputs
        -- * multiple output case
        n -> do op <- structPack outputs
                return $ Just op

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
codegenBody :: ProcBody -> Codegen (Maybe Operand)
codegenBody body =
    do let ps = List.map content (bodyPrims body)
       -- Filter out prims which contain only phantom arguments
       -- ops <- mapM cgen $ List.filter (not . phantomPrim) ps
       ops <- mapM cgen ps
       if List.null ops
           then return Nothing
           else return $ last ops

-- | Predicate to check whether a Prim is a phantom prim i.e Contains only
-- phantom arguments.
phantomPrim :: Prim -> Bool
phantomPrim (PrimCall _ args) = List.null $ List.filter notPhantom args
phantomPrim (PrimForeign _ _ _ args) =
  List.null $ List.filter notPhantom args
phantomPrim PrimNop = True


-- | Code generation for a conditional branch. Currently a binary split
-- is handled, which each branch returning the left value of their last
-- instruction.
codegenForkBody :: PrimVarName -> [ProcBody]
                -> Maybe Operand -> Codegen ()
codegenForkBody var (b1:b2:[]) outop =
    do ifthen <- addBlock "if.then"
       ifelse <- addBlock "if.else"
       -- ifexit <- addBlock "if.exit"
       testop <- getVar (show var)
       cbr testop ifthen ifelse

       -- if.then
       setBlock ifthen
       retop <- codegenBody b2
       case retop of
           Nothing -> ret outop
           _ -> ret retop
       -- if.else
       setBlock ifelse
       retop <- codegenBody b1
       case retop of
           Nothing -> ret outop
           _ -> ret retop
       return ()

       -- -- if.exit
       -- setBlock ifexit
       -- phi int_t [(trueval, ifthen), (falseval, ifelse)]
codegenForkBody _ _ _ = error
  $ "Unrecognized control flow. Too many/few blocks."


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
cgen prim@(PrimCall pspec args) =
    do modn <- getModName
       let (ProcSpec mod name _) = pspec
       let nm = LLVMAST.Name (showModSpec mod ++ "." ++ name)
       -- Find the prototype of the pspec being called
       -- and match it's parameters with the args here
       -- and remove the unneeded ones.
       protoFound <- findProto pspec       
       let filteredArgs = case protoFound of
               Just callProto -> filterUnneededArgs callProto args
               Nothing -> args

       -- if the call is to an external module, declare it
       unless (modn == (showModSpec mod))
           (addExtern $ PrimCall pspec filteredArgs)
               

       let inArgs = primInputs filteredArgs
       let outTy = primReturnType filteredArgs

       inops <- mapM cgenArg inArgs
       let ins = call (externf outTy nm) inops
       res <- addInstruction ins filteredArgs
       return (Just res)

cgen prim@(PrimForeign lang name flags args)
     | lang == "llvm" = case (length args) of
                          2 -> cgenLLVMUnop name flags args
                          3 -> cgenLLVMBinop name flags args
                          _ -> error $ "Instruction " ++ name ++ " not found!"
     | otherwise =
         do addExtern prim
            let inArgs = primInputs args
            let nm = LLVMAST.Name name
            inops <- mapM cgenArg inArgs
            let outty = primReturnType args
            let ins = call (externf outty nm) inops
            res <- addInstruction ins args
            return (Just res)


cgen PrimNop = error "No primitive found."

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
                     in addInstruction ins args >>= (return . Just)
         Nothing -> error $ "LLVM Instruction not found: " ++ name


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
           if length outputs == 1 && length inArgs == 1
               then do let (outTy, outNm) = openPrimArg $ head outputs
                       ptr <- doAlloca outTy
                       inop <- cgenArg $ head inArgs
                       store ptr inop
                       op <- doLoad outTy ptr
                       assign outNm op
                       return $ Just op
               else return Nothing

    | otherwise =
        do let inArgs = primInputs args
           inOps <- mapM cgenArg inArgs
           case Map.lookup name llvmMapUnop of
             (Just f) -> let ins = f (head inOps)
                         in addInstruction ins args >>= (return . Just)
             Nothing -> error $ "LLVM Instruction not found : " ++ name


-- | Look inside the Prototype list stored in the CodegenState monad and
-- find a matching ProcSpec.
findProto :: ProcSpec -> Codegen (Maybe PrimProto)
findProto pspec = do
    allProtos <- getModProtos
    let procNm = procSpecName pspec
    return $ List.find (\p -> primProtoName p == procNm) allProtos


-- | Match PrimArgs with the paramaters in the given prototype. If a PrimArg's
-- counterpart in the prototype is unneeded, filtered out. Positional matching
-- is used for this. 
filterUnneededArgs :: PrimProto -> [PrimArg] -> [PrimArg]
filterUnneededArgs proto args = argsNeeded args (primProtoParams proto)

argsNeeded :: [PrimArg] -> [PrimParam] -> [PrimArg]
argsNeeded [] [] = []
argsNeeded (a:_) [] = []
argsNeeded [] _ = []
argsNeeded (a:as) (p:ps) 
    | paramNeeded p == True = a : (argsNeeded as ps)
    | otherwise = argsNeeded as ps
      

----------------------------------------------------------------------------
-- Helpers for dealing with instructions                                  --
----------------------------------------------------------------------------

-- | The 'maybeMove' instruction creates operands for both the input and
-- output parameter and assigns the out operand the input operand on the
-- reference symbol table.
maybeMove :: [PrimArg] -> Maybe String -> Codegen (Maybe Operand)
maybeMove _ Nothing = return Nothing
maybeMove [] _ = return Nothing
maybeMove (a:[]) (Just nm) =
    do inop <- cgenArg a
       assign nm inop
       return (Just inop)
maybeMove _ _ = error $ "Move instruction received more than one input!"


-- | Append an 'Instruction' to the current basic block's instruction stack.
-- The return type of the operand value generated by the instruction call is
-- inferred depending on the primitive arguments. The name is inferred from
-- the output argument's name (LPVM is in SSA form).
addInstruction :: Instruction -> [PrimArg] -> Codegen Operand
addInstruction ins args =
     do let outArgs = primOutputs args
        let outTy = primReturnType args
        case length outArgs of
          0 -> instr outTy ins
          1 -> do let outName = pullName $ head outArgs
                  outop <- namedInstr outTy outName ins
                  assign outName outop
                  return outop
          n -> do outOp <- instr outTy ins
                  let outTys = List.map (typed . argType) outArgs
                  fields <- structUnPack outOp outTys
                  let outNames = List.map pullName outArgs
                  zipWithM_ assign outNames fields
                  return $ last fields
    where pullName (ArgVar var _ _ _ _) = show var
          pullName _ = error $ "Expected variable as output."

-- | Generate an expanding instruction name using the passed flags. This is
-- useful to augment a simple instruction. (Ex: compare instructions can have
-- the comparision type specified as a flag).
withFlags :: ProcName -> [Ident] -> String
withFlags p [] = p
withFlags p f = p ++ " " ++ (List.intercalate " " f)

-- | Apply Operands from the operand list (2 items) to the wrapped LLVM
-- instruction from 'Codegen' Module.
apply2 :: (Operand -> Operand -> Instruction) -> [Operand] -> Instruction
apply2 f (a:b:[]) = f a b
apply2 _ _ = error $ "Not a binary operation."


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
primReturnType :: [PrimArg] -> Type
primReturnType ps =
    let outputs = primOutputs ps in
    case length outputs of
        0 -> void_t
        1 -> typed $ argType (head outputs)
        n -> struct_t (List.map (typed . argType) outputs)


goesIn :: PrimArg -> Bool
goesIn p = (argFlowDirection p) == FlowIn

notPhantom :: PrimArg -> Bool
notPhantom p = ((typeName .argType) p) /= "phantom"

-- | Pull out the name of a primitive argument if it is a variable.
argName :: PrimArg -> Maybe String
argName (ArgVar var _ _ _ _) = Just $ show var
argName _ = Nothing

-- | Split primitive arguments into inputs and output arguments determined
-- by their flow type.
splitArgs :: [PrimArg] -> ([PrimArg], PrimArg)
splitArgs args = (inputs, output)
    where inputs = List.filter isInputP args
          output = head $ List.filter (not . isInputP) args
          isInputP a = argFlowDirection a == FlowIn

-- | Open a PrimArg into it's inferred type and string name.
openPrimArg :: PrimArg -> (Type, String)
openPrimArg (ArgVar nm ty _ _ _) = (typed ty, show nm)
openPrimArg a = error $ "Can't Open!: "
                ++ argDescription a
                ++ (show $ argFlowDirection a)


-- | Assigns the primitive argument on the symbol table
assignPrim :: Operand -> PrimArg -> Codegen ()
assignPrim op (ArgVar var _ _ _ _) = assign (show var) op
assignPrim _ _ = return ()


localOperandType :: Operand -> Type
localOperandType (LocalReference ty _) = ty
localOperandType _ = void_t


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
cgenArg (ArgInt val _) = return $ cons (C.Int 32 val)
cgenArg (ArgFloat val _) = return $ cons (C.Float $ F.Double val)
cgenArg (ArgString s _) =
    do let conStr = (makeStringConstant s)
       let len = (length s) + 1
       let conType = array_t (fromIntegral len) char_t
       conName <- addGlobalConstant conType conStr
       let conPtr = C.GlobalReference conType conName
       let conElem = C.GetElementPtr True conPtr [C.Int 32 0, C.Int 32 0]
       return $ cons conElem
cgenArg (ArgChar c _) = return $ cons (C.Int 8 $ integerOrd c)


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
            -- * Floating point instruction
            ("fadd", fadd),
            ("fsub", fsub),
            ("fmul", fmul),
            ("fdiv", fdiv),
            -- * Comparisions
            ("icmp eq", icmp IP.EQ),
            ("icmp ne", icmp IP.NE),
            ("icmp slt", icmp IP.SLT),
            ("icmp sle", icmp IP.SLE),
            ("icmp sgt", icmp IP.SGT),
            ("icmp sge", icmp IP.SGE),
            -- * Floating point comparisions
            ("fcmp eq", fcmp FP.OEQ),
            ("fcmp ne", fcmp FP.ONE),
            ("fcmp slt", fcmp FP.OLT),
            ("fcmp sle", fcmp FP.OLE),
            ("fcmp sgt", fcmp FP.OGT),
            ("fcmp sge", fcmp FP.OGE),
            -- * Bitwise operations
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
typed :: TypeSpec -> LLVMAST.Type
typed ty = case (typeName ty) of
             "int"     -> int_t
             "char"    -> char_t
             "float"   -> float_t
             "double"  -> float_t
             "bool"    -> int_c 1
             "string"  -> ptr_t char_t
             "phantom" -> void_t
             _         -> void_t


typed' :: TypeSpec -> Compiler LLVMAST.Type
typed' ty = do
    repr <- lookupTypeRepresentation ty
    case repr of
        Just typeStr -> return $ typeStrToType typeStr
        Nothing -> error "No type representaition"

typeStrToType :: String -> LLVMAST.Type
typeStrToType [] = void_t
typeStrToType (c:cs)
    | c == 'i' = int_c (fromIntegral bytes)
    | c == 'f' = float_c (fromIntegral bytes)
    | c == 'p' = ptr_t (int_c 8)
    | otherwise = void_t
  where
    bytes = (read cs :: Int)
------------------------------------------------------------------------------
-- -- * Creating LLVM AST module from global definitions                    --
------------------------------------------------------------------------------

-- | Initialize and fill a new LLVMAST.Module with the translated
-- global definitions (extern declarations and defined functions)
-- of LPVM procedures in a module.
newLLVMModule :: String -> [[ProcDef]] -> LLVMAST.Module
newLLVMModule name procs = let procs' = concat procs
                               defs = List.map takeDefinition procs'
                               exs = concat $ List.map takeExterns procs'
                               exs' = uniqueExterns exs
                           in modWithDefinitions name $ exs' ++ defs

-- | Pull out the LLVM Definition of a procedure.
takeDefinition :: ProcDef -> LLVMAST.Definition
takeDefinition p = case procImpln p of
                     (ProcDefBlocks _ def _) -> def
                     _ -> error "No definition found."

-- | Pull out the list of needed extern definitions built during
-- procedure translation.
takeExterns :: ProcDef -> [LLVMAST.Definition]
takeExterns p = case procImpln p of
                  (ProcDefBlocks _ _ exs) -> exs
                  _ -> error "No Externs field found."

-- | Filter out non-unique externs
uniqueExterns :: [LLVMAST.Definition] -> [LLVMAST.Definition]
uniqueExterns exs = List.nubBy sameDef exs
  where
    sameDef (LLVMAST.GlobalDefinition g1) (LLVMAST.GlobalDefinition g2)
      = (G.name g1) == (G.name g2)
    sameDef _ _ = False


-- | Create a new LLVMAST.Module with the given name, and fill it with the
-- given global definitions.
modWithDefinitions :: String -> [LLVMAST.Definition] -> LLVMAST.Module
modWithDefinitions nm defs = LLVMAST.Module nm Nothing Nothing defs


-- | Build an extern declaration definition from a given LPVM primitive.
declareExtern :: Prim -> LLVMAST.Definition
declareExtern (PrimForeign _ name _ args) =
    external retty name fnargs
    where
      retty = primReturnType args
      fnargs = List.map makeExArg (primInputs args)

declareExtern (PrimCall (ProcSpec m n _) args) =
    external retty ((showModSpec m) ++ "." ++ n) fnargs
    where
      retty = primReturnType args
      fnargs = List.map makeExArg (primInputs args)

declareExtern PrimNop = error "Can't declare extern for PrimNop."

-- | Helper to make arguments for an extern declaration.
makeExArg :: PrimArg -> (Type, LLVMAST.Name)
makeExArg arg = let ty = (typed . argType) arg
                    nm = LLVMAST.UnName 0
                in (ty, nm)


----------------------------------------------------------------------------
-- Block Modification                                                     --
----------------------------------------------------------------------------

-- | Create a new LLVMAST.Module with in-order calls to the
-- given modules' mains.
-- A module's main would look like: 'module.main'
-- For each call, an external declaration to that main function is needed.
newMainModule :: [ModSpec] -> LLVMAST.Module
newMainModule depends = modWithDefinitions "tmpMain" newDefs
  where
    mainDef = createMainFn depends
    externsForMain = mainExterns depends
    newDefs = externsForMain ++ [mainDef]

-- | Create the 'main' function definition which calls other modules'
-- main(s).
createMainFn :: [ModSpec] -> LLVMAST.Definition
createMainFn mods = globalDefine int_t "main" [] bls
  where
    bls = createBlocks (execCodegen "" [] $ mainCodegen mods)

-- | Run the Codegen monad collecting the instructions needed to call
-- the given modules' main(s). This main function returns 0.
mainCodegen :: [ModSpec] -> Codegen ()
mainCodegen mods = do
    entry <- addBlock entryBlockName
    setBlock entry
    let mainName m = LLVMAST.Name $ showModSpec m ++ ".main"
    forM_ mods $ \m -> instr int_t $
                       call (externf int_t (mainName m)) []
    -- int main returns 0
    ptr <- instr (ptr_t int_t) (alloca int_t)
    let retcons = cons (C.Int 32 0)
    store ptr retcons
    ret (Just retcons)
    return ()

-- | Create a list of extern declarations for each call to a foreign
-- module's main.
mainExterns :: [ModSpec] -> [LLVMAST.Definition]
mainExterns mods = List.map externalMain mods
    where
      mainName m = showModSpec m ++ ".main"
      externalMain m = external int_t (mainName m) []


-- | Concat the LLVMAST.Module implementations of a list of loaded modules
-- to the LLVMAST.Module implementation ModSpec passed as the first
-- parameter.
-- It is assumed and required that all these modules are loaded and compiled
-- to their LLVM stage (so that the modLLVM field will exist)
-- Concatenation involves uniquely appending the LLVMAST.Definition lists.
concatLLVMASTModules :: ModSpec      -- ^ Module to append to 
                     -> [ModSpec]    -- ^ Modules to append
                     -> Compiler ()
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
    updateLoadedModuleImpln (\imp -> imp { modLLVM = Just updatedLLMod })
        thisMod

-- | Extend the LLVMAST.Definition list of the first module with the
-- LLVMAST.Definition list passed as the second parameter. The concatenation
-- must be unique.
addUniqueDefinitions :: LLVMAST.Module -> [LLVMAST.Definition]
                     -> LLVMAST.Module
addUniqueDefinitions (LLVMAST.Module n l t ds) defs =
    LLVMAST.Module n l t newDefs
  where
    newDefs = List.nub $ ds ++ defs



----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the LLVMComp StateT Monad to Blocks.
logBlocks :: String -> LLVMComp ()
logBlocks s = lift $ logMsg Blocks s

-- | Logging from the Compiler monad to Blocks.
logBlocks' :: String -> Compiler ()
logBlocks' = logMsg Blocks

-- | Make 'show' not include quotes when being used to name symbols.
-- show' = sq . show

sq :: String -> String
sq s@[c] = s
sq ('"':s)
    | last s == '"'  = init s
    | otherwise      = s
sq ('\'':s)
    | last s == '\'' = init s
    | otherwise      = s
sq s = s

-- | Log with a wrapping line of replicated characters above and below.
logWrapWith :: Char -> String -> Compiler ()
logWrapWith ch s = do
    logMsg Blocks (replicate 80 ch)
    logMsg Blocks s
    logMsg Blocks (replicate 80 ch)



