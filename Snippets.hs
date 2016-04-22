--  File     : Snippets.hs
--  Author   : Peter Schachte
--  Origin   : Thu 21 Apr 2016 23:17:48 AEST
--  Purpose  : Convenience functions for generation of Wybe AST
--  Copyright: 2016 Peter Schachte.  All rights reserved.

module Snippets (intType, intCast, boolType, boolCast, varSet, varGet, castTo,
                lpvmCast, lpvmCastToVar, iVal, move, comparison) where

import AST

-- |The int type
intType :: TypeSpec
intType = TypeSpec ["wybe"] "int" []

-- |Cast an expr to the int type
intCast :: Exp -> Exp
intCast exp = Typed exp intType True

-- |The bool type
boolType :: TypeSpec
boolType = TypeSpec ["wybe"] "bool" []

-- |Cast an expr to the bool type
boolCast :: Exp -> Exp
boolCast exp = Typed exp boolType True

-- |An output variable reference (lvalue)
varSet :: Ident -> Exp
varSet name = Var name ParamOut Ordinary

-- |An input variable reference (rvalue)
varGet :: Ident -> Exp
varGet name = Var name ParamIn Ordinary

-- |An expression to cast a value to the specified type
castTo :: Exp -> TypeSpec -> Exp
castTo exp typ = Typed exp typ True

-- |An unplaced statement to cast a value into fresh variable
lpvmCast :: Exp -> Ident -> TypeSpec -> Placed Stmt
lpvmCast from to totype =
    Unplaced $ ForeignCall "lpvm" "cast" []
    [Unplaced from, Unplaced $ Typed (varSet to) totype True]

-- |An unplaced statement to cast a value into fresh variable
lpvmCastToVar :: Exp -> Ident -> Placed Stmt
lpvmCastToVar from to =
    Unplaced $ ForeignCall "lpvm" "cast" []
    [Unplaced from, Unplaced $ varSet to]

-- |An integer constant expression
iVal :: Integral a => a -> Exp
iVal v = IntValue $ fromIntegral v

-- |An unplaced instruction to move a value to a variable
move :: Exp -> Exp -> Placed Stmt
move src dest =
    Unplaced $ ForeignCall "llvm" "move" [] [Unplaced src, Unplaced dest]

-- |An unplaced instruction to compare two integer values
comparison :: Ident -> Exp -> Exp -> Ident -> Placed Stmt
comparison tst left right dest =
    Unplaced $ ForeignCall "llvm" "icmp" [tst]
    [Unplaced left, Unplaced right, Unplaced $ boolCast $ varSet dest]
