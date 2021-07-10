--  File     : Snippets.hs
--  Author   : Peter Schachte
--  Purpose  : Convenience functions for generation of Wybe AST
--  Copyright: 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Snippets (castFromTo, castTo, withType, intType, intCast,
                 tagType, tagCast, phantomType, varSet, varGet, varGetSet,
                 boolType, boolCast, boolTrue, boolFalse, boolBool,
                 boolVarSet, boolVarGet, intVarSet, intVarGet,
                 lpvmCast, lpvmCastExp, lpvmCastToVar, iVal, move, primMove,
                 boolNegate, comparison, succeedTest, failTest, testVar,
                 succeedIfSemiDet) where

import AST

-- |An expression to cast a value to the specified type
castFromTo :: TypeSpec -> TypeSpec -> Exp -> Exp
castFromTo innerType outerType exp = Typed exp outerType $ Just innerType

-- |An expression to cast a value to the specified type
castTo :: Exp -> TypeSpec -> Exp
castTo = flip $ castFromTo AnyType 

-- |An expression to constrain th subexpression to have the specified type
withType :: Exp -> TypeSpec -> Exp
withType exp typ = Typed exp typ Nothing

-- |The int type
intType :: TypeSpec
intType = TypeSpec ["wybe"] "int" []

-- |Cast an expr to the int type
intCast :: Exp -> Exp
intCast = (`castTo` intType)

-- |The type of a secondary tag (currently 16 bits unsigned)
tagType :: TypeSpec
tagType = Representation $ Bits 16

-- |Cast an expr to the int type
tagCast :: Exp -> Exp
tagCast = (`castTo` tagType)

-- |The bool type
boolType :: TypeSpec
boolType = TypeSpec ["wybe"] "bool" []

-- |Cast an expr to the bool type
boolCast :: Exp -> Exp
boolCast = (`castTo` boolType)

-- |True as a bool Exp
boolTrue :: Exp
boolTrue = iVal 1 `withType` boolType

-- |False as a bool Exp
boolFalse :: Exp
boolFalse = iVal 0 `withType` boolType

-- |Return an expression holding value of a Haskell Bool
boolBool :: Bool -> Exp
boolBool bool = iVal (if bool then 1 else 0) `withType` boolType

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
boolVarSet name = varSet name `withType` boolType

-- |A Boolean typed input variable reference (rvalue)
boolVarGet :: Ident -> Exp
boolVarGet name = varGet name `withType` boolType

-- |An integer type output variable reference (lvalue)
intVarSet :: Ident -> Exp
intVarSet name = varSet name `withType` intType

-- |An integer type input variable reference (rvalue)
intVarGet :: Ident -> Exp
intVarGet name = varGet name `withType` intType

-- |An unplaced statement to cast a value into fresh variable
lpvmCast :: Exp -> Ident -> TypeSpec -> Placed Stmt
lpvmCast from to totype =
    Unplaced $ ForeignCall "lpvm" "cast" []
    [Unplaced from, Unplaced $ varSet to `castTo` totype]

-- |An expr to cast a value
lpvmCastExp :: Exp -> TypeSpec -> Exp
lpvmCastExp from totype =
    ForeignFn "lpvm" "cast" [] [Unplaced from] `castTo` totype

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
comparison :: Ident -> Exp -> Exp -> Placed Stmt
comparison tst left right =
    Unplaced $ TestBool $ boolCast
    $ ForeignFn "llvm" tst [] [Unplaced left, Unplaced right]


-- |A TestBool statement that always succeeds
succeedTest :: Placed Stmt
succeedTest = Unplaced $ TestBool $ boolCast (iVal 1)


-- |In a SemiDet context, generates code to succeed, otherwise generates no code
succeedIfSemiDet :: Determinism -> [Placed Stmt]
succeedIfSemiDet Terminal = []
succeedIfSemiDet Failure  = []
succeedIfSemiDet Det      = []
succeedIfSemiDet SemiDet  = [succeedTest]


-- |A TestBool statement that always fails
failTest :: Placed Stmt
failTest = Unplaced $ Fail


-- |An unplaced TestBool of a Boolean variable
testVar :: Ident -> Placed Stmt
testVar name = Unplaced $ TestBool $ boolCast $ varGet name
