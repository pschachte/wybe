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

-- |Type to remember the variable renamings.  A variable that maps to 
--  Nothing is not permitted to be renamed, because it is a parameter. 
type Renaming = Map PrimVarName (Maybe PrimVarName)


assignElim :: ProcDef -> ProcDef
assignElim (ProcDef name proto body pos tmpCtr vis) = 
    ProcDef name proto body' pos tmpCtr vis
    where
    PrimProto _ params = proto
    renaming = List.foldr (flip Map.insert Nothing) Map.empty $ 
               List.map primParamName params
    body' = assignElimBody renaming body


assignElimBody :: Renaming -> ProcBody -> ProcBody
assignElimBody initNaming body =
    let renaming = planRenaming initNaming body
    in  executeRenaming renaming body


planRenaming :: Renaming -> ProcBody -> Renaming
planRenaming naming (ProcBody prims _) = 
    -- Ignore the forks for now, as we can only rename variables
    -- initially assigned in a fork, which means we need to keep track
    -- of which variables are assigned before entering a fork.
    List.foldl planPrimRenaming naming $ List.map content prims


planPrimRenaming :: Renaming -> Prim -> Renaming
planPrimRenaming naming (PrimCall [] "=" _ [ArgVar name1 _ FlowOut _, 
                                                 ArgVar name2 _ FlowIn _]) =
    planAssignRenaming naming name1 name2
planPrimRenaming naming (PrimCall [] "=" _ [ArgVar name1 _ FlowIn _, 
                                                 ArgVar name2 _ FlowOut _]) =
    planAssignRenaming naming name2 name1
planPrimRenaming naming _ = naming


planAssignRenaming :: Renaming -> PrimVarName -> PrimVarName -> Renaming
planAssignRenaming naming lname rname =
    let lmapping = Map.findWithDefault (Just lname) lname naming
        (rname',rrenameable) = ultimateTarget naming rname
    in  case (lmapping,rrenameable) of
      (Just lname',_) -> Map.insert lname' (Just rname') naming
      (Nothing,True)  -> Map.insert rname' (Just lname) naming
      (Nothing,False) -> naming


ultimateTarget :: Renaming -> PrimVarName -> (PrimVarName,Bool)
ultimateTarget naming name =
  case Map.lookup name naming of
      Just (Just name') -> ultimateTarget naming name'
      Just Nothing      -> (name, False)
      Nothing           -> (name, True)


executeRenaming :: Renaming -> ProcBody -> ProcBody
executeRenaming naming (ProcBody prims fork) =
    ProcBody (List.concatMap (executePrimRenaming naming) prims)
             (executeForkRenaming naming fork)


executeForkRenaming :: Renaming -> PrimFork -> PrimFork
executeForkRenaming _ NoFork = NoFork
executeForkRenaming naming (PrimFork var bodies) =
    PrimFork var $ List.map (executeRenaming naming) bodies


executePrimRenaming :: Renaming -> Placed Prim -> [Placed Prim]
executePrimRenaming naming placed =
    List.map (flip maybePlace (place placed)) $
    renamePrim naming (content placed)


renamePrim :: Renaming -> Prim -> [Prim]
renamePrim naming (PrimCall [] "=" _ 
                   [ArgVar name1 _ _ _, ArgVar name2 _ _ _])
  | ultimateTarget naming name1 == ultimateTarget naming name2 = []
renamePrim naming (PrimCall maybeMod name id args) =
    [PrimCall maybeMod name id $ List.map (renameArg naming) args]
renamePrim naming (PrimForeign lang name id args) = 
    [PrimForeign lang name id $ List.map (renameArg naming) args]
renamePrim naming (PrimNop) = [PrimNop]


renameArg :: Renaming -> PrimArg -> PrimArg
renameArg naming (ArgVar name typ dir flowType) =
    ArgVar (fst $ ultimateTarget naming name) typ dir flowType
renameArg naming primArg = primArg
