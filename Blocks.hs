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

data LLVMCompState = LLVMCompState {
      fnargs :: [PrimParam]
    }

initLLVMComp :: LLVMCompState
initLLVMComp = LLVMCompState []

evalLLVMComp :: LLVMComp t -> Compiler t
evalLLVMComp llcomp =
    evalStateT llcomp initLLVMComp


blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule thisMod =
    do reenterModule thisMod
       logBlocks' "------------------------------"
       logBlocks' $ "----------- Translating Mod: " ++ showModSpec thisMod
       logBlocks' "------------------------------"
       (names, procs) <- fmap unzip $
                         getModuleImplementationField (Map.toList . modProcs)
       procs' <- mapM (mapM translateProc) procs
       updateImplementation
        (\imp -> imp { modProcs = Map.union
                                  (Map.fromList $ zip names procs')
                                  (modProcs imp) })

       finishModule
       logBlocks' $ "*** Exiting Module " ++ showModSpec thisMod ++ " ***"

-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). By now the final compilation to LPVM should be done
-- and Codegen module can be leveraged to emit LLVM.
translateProc :: ProcDef -> Compiler ProcDef
translateProc proc =
    evalLLVMComp $ do
      let def@(ProcDefPrim proto body) = procImpln proc
      logBlocks $ "Making definition of: "
      logBlocks $ show def
      let args = primProtoParams proto
      logBlocks $ "Args: " ++ (show args)
      body' <- compileBodyToBlocks args body
      -- logBlocks $ (showPretty body')
      let lldef = makeGlobalDefinition proto body'
      logBlocks $ showPretty lldef
      let procblocks = ProcDefBlocks proto lldef
      -- logBlocks $ "Head Block: " ++ (show (head body'))
      return $ proc { procImpln = procblocks}


makeGlobalDefinition :: PrimProto -> [LLVMAST.BasicBlock] -> LLVMAST.Definition
makeGlobalDefinition proto bls = globalDefine retty label fnargs bls
    where
      params = primProtoParams proto
      outp = openOutputParam params
      retty = case outp of
                (Just (ty, nm)) -> ty
                Nothing -> phantom_t
      label = (show' . primProtoName) proto
      inputs = List.filter isInputParam params
      fnargs = List.map makeFnArg inputs


-- | Predicate to check if a primitive's parameter is of input flow (input)
isInputParam :: PrimParam -> Bool
isInputParam p = primParamFlow p == FlowIn

-- | Convert a primitive's input parameter to LLVM's Definition argument.
makeFnArg :: PrimParam -> (Type, LLVMAST.Name)
makeFnArg arg = (ty, nm)
    where
      ty = typed $ primParamType arg
      nm = LLVMAST.Name $ show (primParamName arg)



-- | Compile a Procedure Body containing primitives to a list of llvm
-- basic blocks, the lvalue of the last block will be the terminitor's
-- emitted value.
compileBodyToBlocks :: [PrimParam] -> ProcBody -> LLVMComp [LLVMAST.BasicBlock]
compileBodyToBlocks args body =
    do let prims = bodyPrims body
       return $ createBlocks $ execCodegen $ do
         entry <- addBlock entryBlockName
         setBlock entry
         mapM_ assignParam args
         let ps = List.map content (bodyPrims body)
         ops <- mapM cgen ps
         -- case openOutputParam args of
         --   (Just (ty, nm)) -> ret $ localVar ty nm
         --   Nothing -> ret $ localVar phantom_t "void"
         ret $ last ops


openOutputParam :: [PrimParam] -> Maybe (Type, String)
openOutputParam params =
    case outputs of
      (p:[]) -> Just (typed $ primParamType p, show $ primParamName p)
      _ -> Nothing
    where outputs = List.filter (not . isInputParam) params

-- | Create space for a parameter and create a reference to this space
-- on the symbol table.
assignParam :: PrimParam -> Codegen ()
assignParam p =
    do let nm = show (primParamName p)
       let ty = typed $ primParamType p
       assign nm (localVar ty nm)


-- | Translate a Primitive statement (in clausal form) to LLVM
cgen :: Prim -> Codegen Operand
cgen (PrimCall pspec args) =
    do let nm = LLVMAST.Name $ show (procSpecName pspec)
       ops <- mapM cgenArg args
       let ins = call (externf phantom_t nm) ops
       instr phantom_t ins
cgen (PrimForeign lang name flags args)
     | lang == "llvm" = case (length args) of
                          2 -> cgenLLVMUnop name flags args
                          3 -> cgenLLVMBinop name flags args
                          _ -> return $ localVar phantom_t "still have to make"
     | otherwise =
         return $ localVar phantom_t "c-phantom"


cgenLLVMBinop :: ProcName -> [Ident] -> [PrimArg] -> Codegen Operand
cgenLLVMBinop name flags args =
    do let (inp, outp) = splitArgs args
       inops <- mapM cgenArg inp
       case Map.lookup name llvmMapBinop of
         (Just f) -> do let ins = (apply2 f inops)
                        let (outty, outnm) = openPrimArg $ head outp
                        outop <- namedInstr outty outnm ins
                        assign outnm outop
                        return outop
         Nothing -> error "LLVM Instruction not found."


cgenLLVMUnop :: ProcName -> [Ident] -> [PrimArg] -> Codegen Operand
cgenLLVMUnop name flags args
    | name == "move" =
        do let (inp, outp) = splitArgs args
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


openLocalOp :: LLVMAST.Operand -> (Type, String)
openLocalOp (LLVMAST.LocalReference ty (LLVMAST.Name nm)) = (ty, nm)

openPrimArg :: PrimArg -> (Type, String)
openPrimArg (ArgVar nm ty _ _ _) = (typed ty, show nm)
openPrimArg _ = error "Can't open!"

-- | 'cgenArg' makes an Operand of the input argument. The argument may be:
-- o input variable - lookup the symbol table to get the pointer to the operand
--   and load it.
-- o Constant - Make a constant operand accordingly
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

llvmMapUnop =
    Map.fromList [
            ("uitofp", uitofp),
            ("fptoui", fptoui)
           ]

initModule :: LLVMAST.Module
initModule = emptyModule "WYBE"


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
noteImplnSuperprocs _ (ProcDefBlocks _ _) _ =
  shouldnt "scanning already compiled code for calls"

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

show' :: Show a => a -> String
show' s = read (show s)

logBlocks :: String -> LLVMComp ()
logBlocks s = lift $ logMsg Blocks s

logBlocks' :: String -> Compiler ()
logBlocks' = logMsg Blocks
