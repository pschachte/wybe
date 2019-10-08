--  File     : DefUse.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri May 31 22:53:12 2013
--  Purpose  : Compute defined and used variables for statements and exprs
--  Copyright: (c) 2013 Peter Schachte.  All rights reserved.
--
-- XXX this module is currently not used; should be deleted when it's
--     clear it won't be needed.

module DefUse (DefUse, pstmtsDefUse) where

import AST
import Data.Set as Set
import Data.List as List

type DefUse = (Set VarName,Set VarName)

noDefUse :: DefUse
noDefUse = (Set.empty, Set.empty)

sequentialDefUse :: DefUse -> DefUse -> DefUse
sequentialDefUse (d1,u1) (d2,u2) =
    (d1 `Set.union` (d2 `Set.difference` u1), 
     u1 `Set.union` (u2 `Set.difference` d1))

parallelDefUse :: DefUse -> DefUse -> DefUse
parallelDefUse (d1,u1) (d2,u2) = (d1 `Set.union` d2, u1 `Set.union` u2)

joinDefUse :: DefUse -> DefUse -> DefUse
joinDefUse (d1,u1) (d2,u2) = (d1 `Set.intersection` d2, u1 `Set.union` u2)

defVar :: VarName -> DefUse
defVar var = (Set.singleton var, Set.empty)

useVar :: VarName -> DefUse
useVar var = (Set.empty, Set.singleton var)

-- |Return the set of variables used as inputs to the given code, other
--  than those in the supplied set of variables.
pstmtsDefUse :: [Placed Stmt] -> DefUse
pstmtsDefUse stmts =
    List.foldl sequentialDefUse noDefUse $ List.map pstmtDefUse stmts

pstmtDefUse :: Placed Stmt -> DefUse
pstmtDefUse placed = stmtDefUse $ content placed

stmtDefUse :: Stmt -> DefUse
stmtDefUse (ProcCall _ args _ _) = pexpsDefUse args
stmtDefUse (ForeignCall _ _ args _ _) = pexpsDefUse args
stmtDefUse (Cond exp thn els _ _) =
    pexpDefUse exp `sequentialDefUse`
    (pstmtsDefUse thn `joinDefUse` pstmtsDefUse els)
stmtDefUse (Loop loop _ _) = pstmtsDefUse loop
stmtDefUse Nop = noDefUse
-- stmtDefUse (For gen _ _) = generatorDefUse gen
stmtDefUse Break = noDefUse
stmtDefUse Next = noDefUse

-- |Return the DefUse info for a generator.  This is a bit different than
--  you would expect.  It is *not* considered to define the 
--  quantified variable, because that is not defined at the place the 
--  generator appears in the loop, but at the loop top.
generatorDefUse (In var exp) = pexpDefUse exp
generatorDefUse (InRange var exp updateOp inc limit) =
    -- XXX This handles the initialisation expr in the wrong place;
    --     it should be handled at the top of the loop
    ((pexpDefUse exp `sequentialDefUse` pexpDefUse inc) `sequentialDefUse`
     case limit of
         Nothing -> noDefUse
         Just (_,pexp) -> pexpDefUse pexp) 
--    `sequentialDefUse` defVar var

pexpsDefUse :: [Placed Exp] -> DefUse
pexpsDefUse exps = List.foldr parallelDefUse noDefUse $
                     List.map pexpDefUse exps

pexpDefUse :: Placed Exp -> DefUse
pexpDefUse placed = expDefUse $ content placed

expDefUse :: Exp -> DefUse
expDefUse (IntValue a) = noDefUse
expDefUse (FloatValue a) = noDefUse
expDefUse (StringValue a) = noDefUse
expDefUse (CharValue a) = noDefUse
expDefUse (Var name dir) =
    (if flowsOut dir then Set.singleton name else Set.empty,
     if flowsIn dir then Set.singleton name else Set.empty)
expDefUse (Where stmts exp) =
    pstmtsDefUse stmts `sequentialDefUse` pexpDefUse exp
expDefUse (CondExp cond thn els) =
    pexpDefUse cond `sequentialDefUse` 
    (pexpDefUse thn `joinDefUse` pexpDefUse els)
expDefUse (Fncall _ exps) = pexpsDefUse exps
expDefUse (ForeignFn _ _ exps) = pexpsDefUse exps
