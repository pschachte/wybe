--  File     : Blocks.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--

module Blocks
       where

import           AST
import           Codegen
import           Control.Monad
import           Control.Monad.Trans          (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Data.Char                    (ord)
import           Data.List                    as List
import           Data.Map                     as Map
import           Data.Maybe
import           Debug.Trace
import qualified LLVM.General.AST             as LLVMAST
import qualified LLVM.General.AST.Constant    as C
import qualified LLVM.General.AST.Float       as F
import           LLVM.General.AST.Instruction
import           LLVM.General.AST.Operand
import           LLVM.General.AST.Type
import           LLVM.General.Context
import           LLVM.General.Module
import           LLVM.General.PrettyPrint
import           Options                      (LogSelection (Blocks))

----------------------------------------------------------------------------
-- LLVM Compiler Monad                                                    --
----------------------------------------------------------------------------
-- | The llvm compiler monad is a state transformer monad carrying the
--  clause compiler state over the compiler monad.
type LLVMComp = StateT LLVMCompState Compiler

-- | Hold some state while converting a AST.Module's procedures into LLVMAST
-- definitions.
data LLVMCompState = LLVMCompState {
      neededExterns :: [Prim] -- ^ collect required extern declarations
    }

-- | Update the LLVMCompState list of primitives which require extern
-- declarations.
needExterns :: [Prim] -> LLVMComp ()
needExterns ps =
    do ex <- gets neededExterns
       modify $ \s -> s { neededExterns = ex ++ ps }
       return ()

-- | Initialize the LLVMCompState
initLLVMComp :: LLVMCompState
initLLVMComp = LLVMCompState []

evalLLVMComp :: LLVMComp t -> Compiler t
evalLLVMComp llcomp =
    evalStateT llcomp initLLVMComp


-- | Transofrorm the module's procedures (in LPVM by now) into LLVM function
-- definitions. A LLVMAST.Module is built up using these global definitions and then
-- stored in the modLLVM field of 'ModuleImplementation'.
blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule thisMod =
    do reenterModule thisMod
       logBlocks' "------------------------------"
       logBlocks' $ "----------- Translating Mod: " ++ showModSpec thisMod
       logBlocks' "------------------------------"
       (names, procs) <- fmap unzip $
                         getModuleImplementationField (Map.toList . modProcs)
       procs' <- mapM (mapM translateProc) procs
       -- Init LLVM Module and fill it
       let llmod = newLLVMModule (showModSpec thisMod) procs'
       updateImplementation (\imp -> imp { modLLVM = Just llmod })
       --logBlocks' $ showPretty llmod
       finishModule
       logBlocks' $ "*** Exiting Module " ++ showModSpec thisMod ++ " ***"



-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). Each ProcDef is converted into a Global Definition
-- in a LLVM Module by translating it's primitives.
-- Translated procedures (ProcDefBlocks ...) can optionally have a list
-- of extern declarations (which are also global definitions) if any primitive
-- is going to call some foreign function (mostly C).
translateProc :: ProcDef -> Compiler ProcDef
translateProc proc =
    evalLLVMComp $ do
      let def@(ProcDefPrim proto body) = procImpln proc
      logBlocks $ "Making definition of: "
      logBlocks $ show def
      let args = primProtoParams proto
      -- logBlocks $ "Args: " ++ (show args)
      body' <- compileBodyToBlocks args body
      ex <- gets neededExterns
      let externs = List.map declareExtern ex
      let lldef = makeGlobalDefinition proto body'
      -- logBlocks $ showPretty lldef
      let procblocks = ProcDefBlocks proto lldef externs
      return $ proc { procImpln = procblocks}


-- | Create LLVM's module level Function Definition from the LPVM procedure prototype
-- and it's body as a list of BasicBlock(s). The return type of such a definition is
-- decided based on the Ouput parameter of the procedure, or is made to be phantom.
makeGlobalDefinition :: PrimProto -> [LLVMAST.BasicBlock] -> LLVMAST.Definition
makeGlobalDefinition proto bls = globalDefine retty label fnargs bls
    where
      params = primProtoParams proto
      outp = openOutputParam params
      retty = case outp of
                (Just (ty, nm)) -> ty
                Nothing -> phantom_t
      label = primProtoName proto
      inputs = List.filter isInputParam params
      fnargs = List.map makeFnArg inputs


-- | Predicate to check if a primitive's parameter is of input flow (input)
isInputParam :: PrimParam -> Bool
isInputParam p = primParamFlow p == FlowIn

-- | Convert a primitive's input parameter to LLVM's Definition parameter.
makeFnArg :: PrimParam -> (Type, LLVMAST.Name)
makeFnArg arg = (ty, nm)
    where
      ty = typed $ primParamType arg
      nm = LLVMAST.Name $ show' (primParamName arg)

-- | Open the Out parameter of a primitive (if there is one) into it's
-- inferred 'Type' and name.
openOutputParam :: [PrimParam] -> Maybe (Type, String)
openOutputParam params =
    case outputs of
      (p:[]) -> Just (typed $ primParamType p, show $ primParamName p)
      _ -> Nothing
    where outputs = List.filter (not . isInputParam) params

-- | Compile a Procedure Body containing primitives to a list of llvm
-- basic blocks, the operand generated by the last block will be the terminitor's
-- emitted value. The parameters of the procedure will all enter the local scope
-- by being referenced on the symbol table (including the output parameter). This
-- is useful in leveraging the existing SSA form in the LPVM rather than generating
-- more unique names. Mostly all primitive's variable arguments can be resolved from
-- the symbol table.
compileBodyToBlocks :: [PrimParam] -> ProcBody -> LLVMComp [LLVMAST.BasicBlock]
compileBodyToBlocks args body =
    do let codestate = execCodegen $ codegenBody args body
       let exs = externs codestate
       needExterns exs
       logBlocks $ "Externs: " ++ (show exs)
       return $ createBlocks codestate


codegenBody :: [PrimParam] -> ProcBody -> Codegen ()
codegenBody args body =
    do entry <- addBlock entryBlockName
       setBlock entry
       mapM_ assignParam args
       let ps = List.map content (bodyPrims body)
       ops <- mapM cgen ps
       ret $ last ops
       return ()


-- | Convert a PrimParam to an Operand value and reference this value by the
-- param's name on the symbol table.
assignParam :: PrimParam -> Codegen ()
assignParam p =
    do let nm = show (primParamName p)
       let ty = typed $ primParamType p
       assign nm (localVar ty nm)


-- | Translate a Primitive statement (in clausal form) to a LLVM instruction.
cgen :: Prim -> Codegen Operand

-- | TODO: A primitive call
cgen (PrimCall pspec args) =
    do let nm = LLVMAST.Name $ show (procSpecName pspec)
       ops <- mapM cgenArg args
       let ins = call (externf phantom_t nm) ops
       instr phantom_t ins

-- | Foreign calls are resolved through numerous instruction maps which map
-- function name to a correspoinding LLVM instruction wrapper defined in
-- 'Codegen'. Two main maps are the ones containing Binary and Unary instructions
-- respectively. Adding each matched instruction to the BasicBlock creates a resulting
-- Operand.
cgen prim@(PrimForeign lang name flags args)
     | lang == "llvm" = case (length args) of
                          2 -> cgenLLVMUnop name flags args
                          3 -> cgenLLVMBinop name flags args
                          _ -> return $ localVar phantom_t "still have to make"
     | otherwise =
         do addExtern prim
            let (inp, outp) = splitArgs args
            let (outty, outnm) = openPrimArg $ head outp
            let nm = LLVMAST.Name name
            inops <- mapM cgenArg inp
            let ins = call (externf outty nm) inops
            outop <- namedInstr outty outnm ins
            assign outnm outop
            return outop


-- | Translate a Binary primitive procedure into a binary llvm instruction, add the
-- instruction to the current BasicBlock's instruction stack and emit the resulting
-- Operand. Reads the 'llvmMapBinop' Map.
-- The primitive arguments are split into inputs and outputs (according to
-- their flow type). The output argument is used to name and reference the resulting
-- Operand of the instruction.
cgenLLVMBinop :: ProcName -> [Ident] -> [PrimArg] -> Codegen Operand
cgenLLVMBinop name flags args =
    do let (inp, outp) = splitArgs args
       -- There should be 2 items in inp list and one item in outp list
       inops <- mapM cgenArg inp
       case Map.lookup name llvmMapBinop of
         (Just f) -> do let ins = (apply2 f inops)
                        let (outty, outnm) = openPrimArg $ head outp
                        outop <- namedInstr outty outnm ins
                        assign outnm outop
                        return outop
         Nothing -> error "LLVM Instruction not found."

-- | Similar to 'cgenLLVMBinop', but for unary operations on the 'llvmMapUnary'.
cgenLLVMUnop :: ProcName -> [Ident] -> [PrimArg] -> Codegen Operand
cgenLLVMUnop name flags args
    | name == "move" =
        do let (inp, outp) = splitArgs args
           -- Should be only one item in both inp and outp [Operand] list.
           let (_, inpnm) = openPrimArg (head inp)
           inop <- getVar inpnm
           let (_, outnm) = openPrimArg (head outp)
           assign outnm inop
           return inop
    | otherwise =
        do let (inp, outp) = splitArgs args
           inops <- mapM cgenArg inp
           case Map.lookup name llvmMapUnop of
             (Just f) -> do let ins = f (head inops)
                            let (outty, outnm) = openPrimArg $ head outp
                            outop <- namedInstr outty outnm ins
                            assign outnm outop
                            return outop
             Nothing -> error "LLVM Instruction not found."

-- | Apply Operands from the operand list (2 items) to the wrapped LLVM instruction
-- from 'Codegen' Module.
apply2 :: (Operand -> Operand -> Instruction) -> [Operand] -> Instruction
apply2 f (a:b:[]) = f a b


-- | Split primitive arguments into inputs and output arguments determined
-- by their flow type.
splitArgs :: [PrimArg] -> ([PrimArg], [PrimArg])
splitArgs args = (inputs, outputs)
    where inputs = List.filter isInputP args
          outputs = List.filter (not . isInputP) args
          isInputP (ArgVar _ _ FlowOut _ _) = False
          isInputP _ = True

-- | Open a PrimArg into it's inferred type and string name.
openPrimArg :: PrimArg -> (Type, String)
openPrimArg (ArgVar nm ty _ _ _) = (typed ty, show nm)
openPrimArg _ = error "Can't open!"

-- | 'cgenArg' makes an Operand of the input argument. The argument may be:
-- o input variable - lookup the symbol table to get it's Operand value.
-- o Constant - Make a constant Operand according to the type.
cgenArg :: PrimArg -> Codegen LLVMAST.Operand
cgenArg (ArgVar nm _ _ _ _) = getVar (show nm)
cgenArg (ArgInt val _) = return $ cons (C.Int 32 val)
cgenArg (ArgFloat val _) = return $ cons (C.Float $ F.Double val)
cgenArg (ArgString s _) = return $ cons (makeStringConstant s)
cgenArg (ArgChar c _) = return $ cons (C.Int 8 $ integerOrd c)

-- | Convert a string into a constant array of constant integers.
makeStringConstant :: String ->  C.Constant
makeStringConstant s = C.Array char_t cs
    where ns = List.map integerOrd s
          cs = List.map (C.Int 8) ns

-- | 'integerOrd' performs ord but returns an Integer type
integerOrd :: Char -> Integer
integerOrd = toInteger . ord


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
            ("fdiv", fdiv)
            -- * Others
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
             "phantom" -> phantom_t
             _         -> phantom_t


noteProcsSuperprocs :: ModSpec -> ProcName -> [ProcDef] ->
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcsSuperprocs mod name defs procs =
  List.foldr (\(def,n) ->
               noteImplnSuperprocs (ProcSpec mod name n) (procImpln def))
  procs $ zip defs [0..]

noteImplnSuperprocs :: ProcSpec -> ProcImpln ->
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnSuperprocs _ (ProcDefSrc _) _ =
  shouldnt "scanning unprocessed code for calls"
-- XXX do the actual work here:
noteImplnSuperprocs caller (ProcDefPrim _ body) procs = procs
noteImplnSuperprocs _ (ProcDefBlocks _ _ _) _ =
  shouldnt "scanning already compiled code for calls"


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
                           in modWithDefinitions name $ exs ++ defs

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

-- | Create a new LLVMAST.Module with the given name, and fill it with the
-- given global definitions.
modWithDefinitions :: String -> [LLVMAST.Definition] -> LLVMAST.Module
modWithDefinitions nm defs = LLVMAST.Module nm Nothing Nothing defs


-- | Build an extern declaration definition from a given LPVM primitive.
declareExtern :: Prim -> LLVMAST.Definition
declareExtern (PrimForeign _ name _ args) =
    external retty name fnargs
    where
      (inArgs, outArgs) = splitArgs args
      retty = (fst . openPrimArg) outArg
      outArg = head outArgs
      fnargs = List.map makeExArg inArgs

-- | Helper to make arguments for an extern declaration.
makeExArg :: PrimArg -> (Type, LLVMAST.Name)
makeExArg arg = let (ty, nm) = openPrimArg arg
                in (ty, LLVMAST.Name nm)

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
show' = sq . show

sq :: String -> String
sq s@[c] = s
sq ('"':s)
    | last s == '"'  = init s
    | otherwise      = s
sq ('\'':s)
    | last s == '\'' = init s
    | otherwise      = s
sq s = s
