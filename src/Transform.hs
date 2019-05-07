--  File     : Transform.hs
--  Author   : Ting Lu
--  Origin   : Mon Apr 01 14:58:00 EST 2019
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module Transform (transformProc) where

import           AliasAnalysis (aliasedArgsInPrimCall, aliasedArgsInSimplePrim,
                                mapParamToArgVar, maybeAliasPrimArgs)
import           AST
import           Control.Monad
import           Data.List     as List
import           Data.Map      as Map
import           Options       (LogSelection (Transform))
import           Util


----------------------------------------------------------------
--
-- Transform mutate instructions with correct destructive flag
-- This is the extra pass after found the alais analysis fixed point
--
----------------------------------------------------------------
transformProc :: ProcDef -> Compiler ProcDef
transformProc def
    | not (procInline def) = do
        let (ProcDefPrim caller body oldAnalysis) = procImpln def
        logTransform $ replicate 60 '~'
        logTransform $ show caller
        logTransform $ replicate 60 '~'

        -- (1) Analysis of current caller's prims
        (aliaseMap1, newPrims) <- transformPrims caller body (initUnionFind, [])
        -- Update bodyPrims of this procbody
        let body1 = body { bodyPrims = newPrims }

        -- (2) Analysis of caller's bodyFork
        -- Update body while checking alias incurred by bodyfork
        (aliaseMap2, body2) <- transformForks caller body1 aliaseMap1

        -- Some logging
        logTransform $ "\n^^^  after transform prims:    " ++ show aliaseMap1
        logTransform $ "^^^  after transform forks:    " ++ show aliaseMap2

        -- (4) Update procImpln with updated body prims
        return def { procImpln = ProcDefPrim caller body2 oldAnalysis }

transformProc def = return def


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMap, [Placed Prim])
                    -> Compiler (AliasMap, [Placed Prim])
transformPrims caller body (initAliases, initPrims) = do
    let nonePhantomParams = protoNonePhantomParams caller
    let prims = bodyPrims body
    -- Transform simple prims:
    -- (only process alias pairs incurred by move, mutate, access, cast)
    logTransform "\nTransform prims (transformPrims):    "
                -- ++ List.intercalate "\n    " (List.map show prims)
    let aliasMap = List.foldr newUfItem initAliases nonePhantomParams
    let nonePhantomParams = protoNonePhantomParams caller
    foldM (transformPrim nonePhantomParams) (aliasMap, []) prims


-- Build up alias pairs triggerred by proc calls
transformPrim :: [PrimVarName] -> (AliasMap, [Placed Prim]) -> Placed Prim
                    -> Compiler (AliasMap, [Placed Prim])
transformPrim nonePhantomParams (aliasMap, prims) prim =
    case content prim of
        -- | Transform proc calls
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logTransform $ "\n--- call          " ++ show spec ++" (callee): "
            logTransform $ "" ++ show calleeProto
            logTransform $ "PrimCall args:    " ++ show args
            logTransform $ "current aliasMap: " ++ show aliasMap
            logTransform $ "calleeAlias:      " ++ show calleeParamAliases
            let paramArgMap = mapParamToArgVar calleeProto args
            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            let calleeArgsAliases = Map.foldrWithKey (transformUfKey paramArgMap)
                                            initUnionFind calleeParamAliases
            combinedAliases <- aliasedArgsInPrimCall calleeArgsAliases
                                        nonePhantomParams aliasMap args
            return (combinedAliases, prims ++ [prim])
        -- | Transform simple prims
        _ -> do
            logTransform $ "\n--- simple prim:  " ++ show prim
            -- Mutate destructive flag if this is a mutate instruction
            prim2 <- mutateInstruction prim aliasMap
            maybeAliasInfo <- maybeAliasPrimArgs (content prim)
            -- Update alias map for escapable args
            aliasMap2 <- aliasedArgsInSimplePrim nonePhantomParams aliasMap
                                                    maybeAliasInfo
            logTransform $ "current aliasMap: " ++ show aliasMap
            logTransform $ "after :           " ++ show aliasMap2
            return (aliasMap2, prims ++ [prim2])


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> AliasMap
                    -> Compiler (AliasMap, ProcBody)
transformForks caller body aliasMap = do
    logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logTransform "Forking:"
            (aliasMap', fBodies') <-
                foldM (\(amap, bs) currBody -> do
                    (amap', ps') <-
                        transformPrims caller currBody (initUnionFind, [])
                    let currBody1 = currBody { bodyPrims = ps' }
                    (amap'', currBody2) <-
                        transformForks caller currBody1 amap'
                    let combinedAliases = combineUf amap'' amap
                    return (combinedAliases, bs++[currBody2])
                ) (aliasMap, []) fBodies
            return (aliasMap', body { bodyFork = fork {forkBodies=fBodies'} })
        _ -> do
            -- NoFork: transform prims done
            logTransform "No fork."
            return (aliasMap, body)


-- Update mutate prim by checking if input is aliased
mutateInstruction :: Placed Prim -> AliasMap -> Compiler (Placed Prim)
mutateInstruction (Placed (PrimForeign lang "mutate" flags args) pos) aliasMap = do
    args' <- _updateMutateForAlias aliasMap args
    return (Placed (PrimForeign lang "mutate" flags args') pos)
mutateInstruction (Unplaced (PrimForeign lang "mutate" flags args)) aliasMap = do
    args' <- _updateMutateForAlias aliasMap args
    return (Unplaced (PrimForeign lang "mutate" flags args'))
mutateInstruction prim _ =  return prim


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMap -> [PrimArg] -> Compiler [PrimArg]
_updateMutateForAlias aliasMap
    args@[fIn@(ArgVar inName _ _ _ final1), fOut, size, offset, ArgInt des typ,
        mem@(ArgVar memName _ _ _ final2)] =
            -- When the val is also a pointer
            if not (connectedToOthers aliasMap inName) && final1
                && not (connectedToOthers aliasMap memName) && final2
                && des /= 1
            then return [fIn, fOut, size, offset, ArgInt 1 typ, mem]
            else return args
_updateMutateForAlias aliasMap
    args@[fIn@(ArgVar inName _ _ _ final), fOut, size, offset, ArgInt des typ, mem] =
        if not (connectedToOthers aliasMap inName) && final && des /= 1
        then return [fIn, fOut, size, offset, ArgInt 1 typ, mem]
        else return args
_updateMutateForAlias _ args = return args


-- |Log a message, if we are logging optimisation activity.
logTransform :: String -> Compiler ()
logTransform = logMsg Transform
