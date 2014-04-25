--  File     : AssignElim.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Apr 25 10:49:18 2014
--  Purpose  : Remove as many redundant assignments as possible
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--
--  We remove unnecessary assignments of the form x=y by keeping 
--  renaming all following occurrences of x to y or vice versa.  
--  For simplicity, especially for procs with multiple clauses, we 
--  preserve the names of all parameters.  This optimisation is 
--  performed in two passes.  In the first pass, we construct the 
--  renaming map, and in the second, we execute the renaming.  This 
--  allows us to rename either variable appearing in assignment, even 
--  if it appears earlier in the clause.

module AssignElim (assignElim) where

import AST
import Data.Map as Map
import Data.List as List

type Renaming = Map PrimVarName PrimVarName

assignElim :: ProcDef -> ProcDef
assignElim (ProcDef name proto body pos) = ProcDef name proto body' pos where
    PrimProto _ params = proto
    renaming = List.foldr insertSelfMappping Map.empty $ 
               List.map primParamName params
    body' = List.map (assignElim' renaming) body


assignElim' :: Renaming -> [Placed Prim] -> [Placed Prim]
assignElim' initNaming clause =
    let renaming = planRenaming initNaming clause
    in  executeRenaming renaming clause


planRenaming :: Renaming -> [Placed Prim] -> Renaming
planRenaming naming clause = 
    List.foldl planPrimRenaming naming $ List.map content clause


planPrimRenaming :: Renaming -> Prim -> Renaming
planPrimRenaming naming (PrimCall "=" _ [ArgVar name1 _ _, ArgVar name2 _ _]) =
    if Map.member name1 naming
    then if Map.member name2 naming
         then naming
         else Map.insert name2 name1 naming
    else Map.insert name1 name2 naming
planPrimRenaming naming _ = naming


executeRenaming :: Renaming -> [Placed Prim] -> [Placed Prim]
executeRenaming naming clause =
    List.concatMap (executePrimRenaming naming) clause


executePrimRenaming :: Renaming -> Placed Prim -> [Placed Prim]
executePrimRenaming naming placed =
    List.map (flip maybePlace (place placed)) $
    renamePrim naming (content placed)


renamePrim :: Renaming -> Prim -> [Prim]
renamePrim naming (PrimCall "=" _ [ArgVar name1 _ _, ArgVar name2 _ _])
  | Map.lookup name1 naming == Just name2 
    || Map.lookup name2 naming == Just name1 
    = []
renamePrim naming (PrimCall name id args) =
    [PrimCall name id $ List.map (renameArg naming) args]
renamePrim naming (PrimForeign lang name id args) = 
    [PrimForeign lang name id $ List.map (renameArg naming) args]
renamePrim naming (PrimGuard guard val) =
    [PrimGuard (executeRenaming naming guard) val]
renamePrim naming (PrimFail) = [PrimFail]
renamePrim naming (PrimNop) = [PrimNop]


renameArg :: Renaming -> PrimArg -> PrimArg
renameArg naming (ArgVar name dir flowType) =
    ArgVar (Map.findWithDefault name name naming) dir flowType
renameArg naming primArg = primArg


insertSelfMappping :: Ord t => t -> Map t t -> Map t t
insertSelfMappping k = Map.insert k k