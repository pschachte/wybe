--  File     : Snippets.hs
--  Author   : Peter Schachte
--  Purpose  : Convenience functions for generation of Wybe AST
--  Copyright: 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Snippets (intType, intCast, boolType, boolCast, boolTrue, boolFalse,
                 boolBool, phantomType, varSet, varGet, varGetSet,
                 boolVarSet, boolVarGet, intVarSet, intVarGet, castTo,
                 lpvmCast, lpvmCastExp, lpvmCastToVar, iVal, move, primMove,
                 boolNegate, comparison, succeedTest, failTest,
                 succeedIfSemiDet) where

import AST

-- |An expression to cast a value to the specified type
castTo :: Exp -> TypeSpec -> Exp
castTo exp typ = Typed exp typ True

-- |The int type
intType :: TypeSpec
intType = TypeSpec ["wybe"] "int" []

-- |Cast an expr to the int type
intCast :: Exp -> Exp
intCast exp = castTo exp intType

-- |The bool type
boolType :: TypeSpec
boolType = TypeSpec ["wybe"] "bool" []

-- |Cast an expr to the bool type
boolCast :: Exp -> Exp
boolCast exp = castTo exp boolType

-- |True as a bool Exp
boolTrue :: Exp
boolTrue = boolCast $ iVal 1

-- |False as a bool Exp
boolFalse :: Exp
boolFalse = boolCast $ iVal 0

-- |Return an expression holding value of a Haskell Bool
boolBool :: Bool -> Exp
boolBool bool = boolCast $ iVal $ if bool then 1 else 0

-- | The phantom type
phantomType :: TypeSpec
phantomType = TypeSpec ["wybe"] "phantom" []

-- |An output variable reference (lvalue)
varSet :: Ident -> Exp
varSet name = Var name ParamOut Ordinary

-- |An input variable reference (rvalue)
varGet :: Ident -> Exp
varGet name = Var name ParamIn Ordinary

-- |An input variable reference (rvalue)
varGetSet :: Ident -> ArgFlowType -> Exp
varGetSet name flowType = Var name ParamInOut flowType

-- |A Boolean typed output variable reference (lvalue)
boolVarSet :: Ident -> Exp
boolVarSet name = Typed (varSet name) boolType False

-- |A Boolean typed input variable reference (rvalue)
boolVarGet :: Ident -> Exp
boolVarGet name = Typed (varGet name) boolType False

-- |An integer type output variable reference (lvalue)
intVarSet :: Ident -> Exp
intVarSet name = Typed (varSet name) intType False

-- |An integer type input variable reference (rvalue)
intVarGet :: Ident -> Exp
intVarGet name = Typed (varGet name) intType False

-- |An unplaced statement to cast a value into fresh variable
lpvmCast :: Exp -> Ident -> TypeSpec -> Placed Stmt
lpvmCast from to totype =
    Unplaced $ ForeignCall "lpvm" "cast" []
    [Unplaced from, Unplaced $ Typed (varSet to) totype True]

-- |An expr to cast a value
lpvmCastExp :: Exp -> TypeSpec -> Exp
lpvmCastExp from totype =
    Typed (ForeignFn "lpvm" "cast" [] [Unplaced from]) totype True

-- |An unplaced statement to cast a value into fresh variable
lpvmCastToVar :: Exp -> Ident -> Placed Stmt
lpvmCastToVar from to =
    Unplaced $ ForeignCall "lpvm" "cast" []
    [Unplaced from, Unplaced $ varSet to]

-- |An integer constant expression
iVal :: Integral a => a -> Exp
iVal v = IntValue $ fromIntegral v

-- |An instruction to move a value to a variable
move :: Exp -> Exp -> Placed Stmt
move src dest =
    Unplaced $ ForeignCall "llvm" "move" [] [Unplaced src, Unplaced dest]

-- |An instruction to negate a bool value to a variable.  We optimise negation
-- of constant values.
boolNegate :: Exp -> Exp -> Placed Stmt
boolNegate (IntValue 0) dest = move boolTrue dest
boolNegate (IntValue 1) dest = move boolFalse dest
boolNegate (Typed (IntValue 0) _ _) dest = move boolTrue dest
boolNegate (Typed (IntValue 1) _ _) dest = move boolFalse dest
boolNegate src@(Typed _ ty _) dest =
    Unplaced $ ForeignCall "llvm" "xor" []
               [Unplaced src, Unplaced $ castTo (iVal 1) ty, Unplaced dest]
boolNegate src dest =
    Unplaced $ ForeignCall "llvm" "xor" []
               [Unplaced src, Unplaced $ boolCast $ iVal 1, Unplaced dest]

-- |A primitive move instruction
primMove :: PrimArg -> PrimArg -> Prim
primMove src dest =
  PrimForeign "llvm" "move" [] [src, dest]

-- |An unplaced instruction to compare two integer values
comparison :: Ident -> Exp -> Exp  -> Placed Stmt
comparison tst left right =
    Unplaced $ ForeignCall "llvm" "test" [tst]
     [Unplaced left, Unplaced right]


-- |A TestBool statement that always succeeds
succeedTest :: Placed Stmt
succeedTest = Unplaced $ TestBool $ castTo (iVal 1) boolType


-- |In a SemiDet context, generates code to succeed, otherwise generates no code
succeedIfSemiDet :: Determinism -> [Placed Stmt]
succeedIfSemiDet Det     = []
succeedIfSemiDet SemiDet = [succeedTest]


-- |A TestBool statement that always fails
failTest :: Placed Stmt
failTest = Unplaced $ TestBool $ castTo (iVal 0) boolType
