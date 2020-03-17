--  File     : Transform.hs
--  Author   : Ting Lu
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


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
        body2 <- transformForks caller body1 aliaseMap1

        -- Some logging
        logTransform $ "\n^^^  after transform prims:    " ++ show aliaseMap1

        -- (4) Update procImpln with updated body prims
        return def { procImpln = ProcDefPrim caller body2 oldAnalysis }

transformProc def = return def


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMap, [Placed Prim])
                    -> Compiler (AliasMap, [Placed Prim])
transformPrims caller body (initAliases, initPrims) = do
    realParams <- (primParamName <$>) <$> protoRealParams caller
    inputParams <- protoInputParamNames caller
    let prims = bodyPrims body
    -- Transform simple prims:
    -- (only process alias pairs incurred by move, mutate, access, cast)
    logTransform "\nTransform prims (transformPrims):   "
    logTransform $ "realParams: " ++ show realParams
    logTransform $ "input params: " ++ show inputParams
    let aliasMap = List.foldr newUfItem initAliases realParams
    foldM (transformPrim realParams inputParams) (aliasMap, []) prims


-- Build up alias pairs triggerred by proc calls
transformPrim :: [PrimVarName] -> [PrimVarName] -> (AliasMap, [Placed Prim])
                    -> Placed Prim -> Compiler (AliasMap, [Placed Prim])
transformPrim realParams inputParams (aliasMap, prims) prim =
    case content prim of
        PrimCall spec args -> do
            -- | Transform proc calls
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logTransform $ "\n--- call          " ++ show spec ++" (callee): "
            logTransform $ "" ++ show calleeProto
            logTransform $ "PrimCall args:    " ++ show args
            let paramArgMap = mapParamToArgVar calleeProto args
            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            let calleeArgsAliases = Map.foldrWithKey (transformUfKey paramArgMap)
                                            initUnionFind calleeParamAliases
            combinedAliases <- aliasedArgsInPrimCall calleeArgsAliases
                                        realParams aliasMap args
            logTransform $ "calleeArgsAliases:" ++ show calleeArgsAliases
            logTransform $ "current aliasMap: " ++ show aliasMap
            logTransform $ "combinedAliases:  " ++ show combinedAliases
            return (combinedAliases, prims ++ [prim])
        _ -> do
            -- | Transform simple prims
            logTransform $ "\n--- simple prim:    " ++ show prim
            logTransform $ "current aliasMap: " ++ show aliasMap
            maybeAliasInfo <- maybeAliasPrimArgs (content prim)
            -- Update alias map for escapable args
            aliasMap2 <- aliasedArgsInSimplePrim realParams aliasMap
                                                maybeAliasInfo
            -- Mutate destructive flag if this is a mutate instruction
            prim2 <- mutateInstruction prim aliasMap inputParams
            logTransform $ "--- transformed to: " ++ show prim2
            logTransform $ "updated aliasMap: " ++ show aliasMap2
            -- Final arguments get removed from aliasmap after mutate
            --   instruction is transformed
            return (aliasMap2, prims ++ [prim2])


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> AliasMap -> Compiler ProcBody
transformForks caller body aliasMap = do
    logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logTransform "Forking:"
            fBodies' <-
                foldM (\bs currBody -> do
                    (amap', ps') <-
                        transformPrims caller currBody (aliasMap, [])
                    let currBody1 = currBody { bodyPrims = ps' }
                    currBody2 <- transformForks caller currBody1 amap'
                    return (bs++[currBody2])
                ) [] fBodies
            return body { bodyFork = fork {forkBodies=fBodies'} }
        NoFork -> do
            -- NoFork: transform prims done
            logTransform "No fork."
            return body


-- Update mutate prim by checking if input is aliased
mutateInstruction :: Placed Prim -> AliasMap -> [PrimVarName] -> Compiler (Placed Prim)
mutateInstruction (Placed (PrimForeign "lpvm" "mutate" flags args) pos) aliasMap inputParams = do
    args' <- _updateMutateForAlias aliasMap inputParams args
    return (Placed (PrimForeign "lpvm" "mutate" flags args') pos)
mutateInstruction (Unplaced (PrimForeign "lpvm" "mutate" flags args)) aliasMap inputParams = do
    args' <- _updateMutateForAlias aliasMap inputParams args
    return (Unplaced (PrimForeign "lpvm" "mutate" flags args'))
mutateInstruction prim _ _ =  return prim


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMap -> [PrimVarName] -> [PrimArg] -> Compiler [PrimArg]
_updateMutateForAlias aliasMap inputParams
    args@[fIn@ArgVar{argVarName=inName,argVarFinal=final1},
          fOut, offset, ArgInt des typ,
        size, offset2, mem@ArgVar{argVarName=memName,argVarFinal=final2}] =
            -- When the val is also a pointer
            if notElem inName inputParams
                && not (connectedToOthers aliasMap inName) && final1
                && not (connectedToOthers aliasMap memName) && final2
                && des /= 1
            then return [fIn, fOut, offset, ArgInt 1 typ, size, offset2, mem]
            else return args
_updateMutateForAlias aliasMap inputParams
    args@[fIn@ArgVar{argVarName=inName,argVarFinal=final},
          fOut, offset, ArgInt des typ,
          size, offset2, mem] =
        if notElem inName inputParams
            && not (connectedToOthers aliasMap inName) && final
            && des /= 1
        then return [fIn, fOut, offset, ArgInt 1 typ, size, offset2, mem]
        else return args
_updateMutateForAlias _ _ args = return args


-- |Log a message, if we are logging optimisation activity.
logTransform :: String -> Compiler ()
logTransform = logMsg Transform
