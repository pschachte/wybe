--  File     : LastUse.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri May 31 22:53:12 2013
--  Purpose  : Mark last use of each variable and remove unneeded parameters
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--

module LastUse (markLastUse) where

import AST
import Options (LogSelection(LastUse))
import Data.Set as Set
import Data.List as List
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad

markLastUse :: ProcSpec -> ProcDef -> Compiler ProcDef
markLastUse ps def = do
    let ProcDefPrim proto body = procImpln def
    let params = primProtoParams proto
    let (inputs,outputs) = List.partition ((==FlowIn) . primParamFlow) params
    let inSet = List.foldr (Set.insert . primParamName) Set.empty inputs
    let outSet = List.foldr (Set.insert . primParamName) Set.empty outputs
    logMsg LastUse $ "\nMarking last uses in:" ++ showBlock 4 body
    (body',needed) <- runStateT (bodyLastUse body) outSet
    logMsg LastUse $ "Result:" ++ showBlock 4 body'
    logMsg LastUse $ "Needed: " ++ show needed
    let params' = List.map 
                  (\p -> p { primParamInfo = ParamInfo $ 
                                             unneededParam needed inSet p })
                  params
    let proto' = proto { primProtoParams = params' }
    return $ def { procImpln = ProcDefPrim proto' body' }


-- |Returns whether this parameter is strictly superfluous.  For input
-- params, that means it is never used; for outputs, that means its
-- value is alwas identical to one of the inputs, which we detect by
-- the fact that parameter name (including version) is the same as a
-- input parameter.
unneededParam :: Set PrimVarName -> Set PrimVarName -> PrimParam -> Bool
unneededParam needed inSet param =
    if primParamFlow param == FlowIn
    then not $ Set.member (primParamName param) needed
    else Set.member (primParamName param) inSet


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
forkLastUse (PrimFork var ty _ bodies) = do
    needed <- get -- this will always be the empty set
    pairs <- mapM (\b -> lift $ runStateT (bodyLastUse b) needed) bodies
    let bodies' = List.map fst pairs
    let needs = List.map snd pairs
    let needed' = List.foldr Set.union Set.empty needs
    put needed'
    last <- unneeded var
    needVar var
    return $ PrimFork var ty last bodies'


pprimsLastUse :: [Placed Prim] -> NeededVars [Placed Prim]
pprimsLastUse [] = return []
pprimsLastUse (pprim:pprims) = do
    pprims' <- pprimsLastUse pprims   -- Do tail first, for backward traversal
    logLastUse $ "\nfinding last uses in " ++ show pprim
    prim' <- primLastUse (content pprim) (place pprim)
    logLastUse $ "           result is " ++ show pprim
    needed <- get
    logLastUse $ "            needed = " ++ show needed
    return $ prim' ++ pprims'

primLastUse :: Prim -> OptPos -> NeededVars [Placed Prim]
primLastUse (PrimCall sp args) pos = do
    noteLastUses args pos $ PrimCall sp
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


-- |Log a message, if we are logging unbrancher activity.
logLastUse :: String -> NeededVars ()
logLastUse s = lift $ logMsg LastUse s
