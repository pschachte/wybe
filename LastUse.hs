--  File     : LastUse.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri May 31 22:53:12 2013
--  Purpose  : Mark last use of each variable and remove unneeded parameters
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--

module LastUse (markLastUse) where

import AST
import Data.Set as Set
import Data.List as List
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad

markLastUse :: ProcSpec -> ProcDef -> Compiler ProcDef
markLastUse ps def = do
    let params = primProtoParams $ procProto def
    let body = procBody def
    let outputs = List.filter ((==FlowOut) . primParamFlow) params
    let outSet = List.foldr (Set.insert . primParamName) Set.empty outputs
    (body',needed) <- runStateT (bodyLastUse body) outSet
    let params' = List.map 
                  (\p -> p { primParamNeeded = neededIfInput needed p }) 
                  params
    let proto' = (procProto def) { primProtoParams = params' }
    return $ def { procProto = proto', procBody = body' }


neededIfInput :: Set PrimVarName -> PrimParam -> Bool
neededIfInput needed param =
    -- XXX still need to consider phantom arguments to be needed?
    (typeName $ primParamType param) == "phantom" ||
    (primParamFlow param == FlowOut || Set.member (primParamName param) needed)


----------------------------------------------------------------
--                       The NeededVars Monad
--
-- records the variables that will be used later in a proc definition 
-- as we process it from end to beginning. 
----------------------------------------------------------------

type NeededVars = StateT (Set PrimVarName)  Compiler


needVar :: PrimVarName -> NeededVars ()
needVar var = do
    modify (Set.insert var)


needed :: PrimVarName -> NeededVars Bool
needed var = gets (Set.member var)


unneeded :: PrimVarName -> NeededVars Bool
unneeded var = gets (not . Set.member var)


bodyLastUse :: ProcBody -> NeededVars ProcBody
bodyLastUse (ProcBody prims fork) = do
    fork' <- forkLastUse fork
    prims' <- pprimsLastUse prims
    return $ ProcBody prims' fork'


forkLastUse :: PrimFork -> NeededVars PrimFork
forkLastUse NoFork = return NoFork
forkLastUse (PrimFork var _ bodies) = do
    needed <- get -- this will always be the empty set
    pairs <- mapM (\b -> lift $ runStateT (bodyLastUse b) needed) bodies
    let bodies' = List.map fst pairs
    let needs = List.map snd pairs
    let needed' = List.foldr Set.union Set.empty needs
    put needed'
    last <- unneeded var
    needVar var
    return $ PrimFork var last bodies'


pprimsLastUse :: [Placed Prim] -> NeededVars [Placed Prim]
pprimsLastUse [] = return []
pprimsLastUse (pprim:pprims) = do
    pprims' <- pprimsLastUse pprims   -- Do tail first, for backward traversal
    prim' <- primLastUse (content pprim) (place pprim)
    return $ prim' ++ pprims'

primLastUse :: Prim -> OptPos -> NeededVars [Placed Prim]
primLastUse (PrimCall md pr sp args) pos = do
    noteLastUses args pos $ PrimCall md pr sp
primLastUse (PrimForeign ln pr tg args) pos = do
    noteLastUses args pos $ PrimForeign ln pr tg
primLastUse (PrimNop) pos = return [maybePlace PrimNop pos]


noteLastUses :: [PrimArg] -> OptPos -> ([PrimArg] -> Prim) -> 
                NeededVars [Placed Prim]
noteLastUses args pos buildPrim = do
    primNeeded <- foldM neededOutput False args
    if primNeeded 
    then do
        args' <- mapM argLastUse args
        mapM_ argNoteUse args
        return [maybePlace (buildPrim args') pos]
    else return []


neededOutput :: Bool -> PrimArg -> NeededVars Bool
neededOutput True _ = return True
neededOutput False (ArgVar var _ FlowOut _ _) =
    needed var
neededOutput needed _ = return needed


argLastUse :: PrimArg -> NeededVars PrimArg
argLastUse (ArgVar var ty FlowIn ft _) = do
    last <- unneeded var
    return $ ArgVar var ty FlowIn ft last
argLastUse otherArg = return otherArg


argNoteUse :: PrimArg -> NeededVars ()
argNoteUse (ArgVar var _ FlowIn _ _) = do
    needVar var
argNoteUse _ = return ()
