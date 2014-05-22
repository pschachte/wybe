--  File     : Expansion.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 14:58:14 2014
--  Purpose  : Replace certain procedure calls with others
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--
--  This code is used for inlining procedures and other similar
--  transformations.  As part of this, variables are also renamed.
--  This code operates on LPVM (Prim) form.

module Expansion (CallExpansion, identityExpansion, addExpansion,
                  bodyExpansion, Substitution, identitySubstitution,
                  ) where

import AST
import Data.Map as Map
import Data.List as List


-- |Type to remember proc call expansions.  For each proc, we remember
-- the parameters of the call, to bind to the actual arguments, and
-- the body of the definition.  We also store a set of the variable
-- names used in the body, so that they can be renamed if necessary to
-- avoid variable capture.
type CallExpansion = Map ProcSpec ([PrimParam],ProcBody)


-- |A CallExpansion that doesn't expand anything
identityExpansion :: CallExpansion
identityExpansion = Map.empty


addExpansion :: ProcSpec -> [PrimParam] -> ProcBody -> CallExpansion ->
                CallExpansion
addExpansion proc params body expn = Map.insert proc (params,body) expn

-- |Type to remember the variable renamings.  A variable that maps to 
--  Nothing is not permitted to be renamed, because it is a parameter. 
type Substitution = Map PrimVarName PrimArg


-- |A Substitution that doesn't substitute anything
identitySubstitution :: Substitution
identitySubstitution = Map.empty


addSubstitution :: PrimVarName -> PrimArg -> Substitution -> Substitution
addSubstitution = Map.insert


procExpansion :: Substitution -> CallExpansion -> ProcDef -> ProcDef
procExpansion subst expn (ProcDef n proto (ProcBody body fork) pos tmp vis) =
    (ProcDef n proto (ProcBody body' fork') pos tmp' vis) where
      


placedPrimExpansion :: Substitution -> CallExpansion -> Bool -> 
    Placed Prim -> [Placed Prim]
placedPrimExpansion subst expn oneClause placed =
    List.map (flip maybePlace (place placed)) $
    primExpansion subst expn oneClause (content placed)


primExpansion :: Substitution -> Prim -> [Prim]
primExpansion subst (PrimCall "=" _ [ArgVar name1 _ _, ArgVar name2 _ _])
  | ultimateTarget subst name1 == ultimateTarget subst name2 = []
primExpansion subst (PrimCall name id args) =
    [PrimCall name id $ List.map (renameArg subst) args]
primExpansion subst (PrimForeign lang name id args) = 
    [PrimForeign lang name id $ List.map (renameArg subst) args]
primExpansion subst (PrimGuard guard val) =
    [PrimGuard (executeSubstitution subst guard) val]
primExpansion subst (PrimNop) = [PrimNop]


renameArg :: Substitution -> PrimArg -> PrimArg
renameArg subst (ArgVar name dir flowType) =
    ArgVar (fst $ ultimateTarget subst name) dir flowType
renameArg subst primArg = primArg
