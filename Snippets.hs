--  File     : Snippets.hs
--  Author   : Peter Schachte
--  Origin   : Thu 21 Apr 2016 23:17:48 AEST
--  Purpose  : Convenience functions for generation of Wybe AST
--  Copyright: 2016 Peter Schachte.  All rights reserved.

module Snippets (intType, intCast, boolType, boolCast, varSet, varGet) where

import AST

intType :: TypeSpec
intType = TypeSpec ["wybe"] "int" []

intCast :: Exp -> Exp
intCast exp = Typed exp intType True

boolType :: TypeSpec
boolType = TypeSpec ["wybe"] "bool" []

boolCast :: Exp -> Exp
boolCast exp = Typed exp boolType True

varSet :: Ident -> Exp
varSet name = Var name ParamOut Ordinary

varGet :: Ident -> Exp
varGet name = Var name ParamIn Ordinary
