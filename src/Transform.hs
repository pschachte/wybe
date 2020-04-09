--  File     : Transform.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Transform (transformProc) where

import           AliasAnalysis (updateAliasedByPrim, 
                                pairArgVarWithParam)
import           AST
import           Control.Monad
import           Data.Bits     as Bits
import           Data.List     as List
import           Data.Map      as Map
import           Flow          ((|>))
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
        let (ProcDefPrim caller body analysis speczBodies) = procImpln def
        logTransform $ replicate 60 '~'
        logTransform $ show caller
        logTransform $ replicate 60 '~'

        unless (Map.null speczBodies) $ shouldnt "speczBodies should be empty"

        -- transform the standard body
        -- In this case, all input params are aliased
        inputParams <- protoInputParamNames caller
        body' <- transformBody caller body emptyDS inputParams

        -- generate&transform all specz versions
        let speczInfo = procArgAliasMultiSpeczInfo analysis
        let versions = allPossiblespeczIds speczInfo
        speczBodies' <- mapM (\id -> do
                let nonAliasedParams = speczIdToNonAliasedParams speczInfo id 
                realParams <- (primParamName <$>) <$> protoRealParams caller
                let aliasedParams = 
                        List.filter (`List.notElem` nonAliasedParams) realParams
                logTransform $ replicate 60 '~'
                logTransform $ "Generating specialized version: "
                                ++ show id ++ " alisedParams: "
                                ++ show aliasedParams
                sbody <- transformBody caller body emptyDS aliasedParams
                return (id, sbody)
            ) versions

        return def { procImpln = 
                        ProcDefPrim caller body' 
                        analysis (Map.fromList speczBodies')}

transformProc def = return def


transformBody :: PrimProto -> ProcBody -> AliasMap -> [PrimVarName]
                             -> Compiler ProcBody
transformBody caller body aliasMap aliasedParams = do
    -- (1) Analysis of current caller's prims
    (aliaseMap', newPrims) <- 
            transformPrims caller body aliasMap aliasedParams
    -- Update bodyPrims of this procbody
    let body' = body { bodyPrims = newPrims }

    -- (2) Analysis of caller's bodyFork
    -- Update body while checking alias incurred by bodyfork
    transformForks caller body' aliaseMap' aliasedParams


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> AliasMap -> [PrimVarName]
                    -> Compiler (AliasMap, [Placed Prim])
transformPrims caller body initAliases aliasedParams = do
    realParams <- (primParamName <$>) <$> protoRealParams caller
    let prims = bodyPrims body
    -- Transform simple prims:
    -- (only process alias pairs incurred by move, mutate, access, cast)
    logTransform "\nTransform prims (transformPrims):   "
    logTransform $ "realParams: " ++ show realParams
    logTransform $ "aliased params: " ++ show aliasedParams
    let aliasMap = List.foldr addOneToDS initAliases realParams
    foldM (transformPrim realParams aliasedParams) (aliasMap, []) prims


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> AliasMap 
                    -> [PrimVarName] -> Compiler ProcBody
transformForks caller body aliasMap aliasedParams = do
    logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logTransform "Forking:"
            fBodies' <-
                mapM (\currBody -> 
                        transformBody caller currBody 
                                        aliasMap aliasedParams
                ) fBodies
            return body { bodyFork = fork {forkBodies=fBodies'} }
        NoFork -> do
            -- NoFork: transform prims done
            logTransform "No fork."
            return body


-- Build up alias pairs triggerred by proc calls
transformPrim :: [PrimVarName] -> [PrimVarName] -> (AliasMap, [Placed Prim])
                    -> Placed Prim -> Compiler (AliasMap, [Placed Prim])
transformPrim realParams aliasedParams (aliasMap, prims) prim = do
    -- TODO: Redundent work here. We should change the current design.
    aliasMap' <- updateAliasedByPrim realParams aliasMap prim
    logTransform $ "\n--- prim:    " ++ show prim
    prim' <- updatePlacedM (\primc -> case primc of
            PrimCall spec args
                    -> do
                        spec' <- _updatePrimCallForSpecz
                                    spec args aliasedParams aliasMap
                        return $ PrimCall spec' args
            PrimForeign "lpvm" "mutate" flags args
                    -> do
                        let args' = _updateMutateForAlias aliasMap 
                                        aliasedParams args
                        return $ PrimForeign "lpvm" "mutate" flags args'
            _       -> return primc
        ) prim
    logTransform $ "--- transformed to: " ++ show prim'
    return (aliasMap', prims ++ [prim'])


-- Update PrimCall to make it uses a better specialized version
-- than the general version based on the current [AliasMap]
_updatePrimCallForSpecz :: ProcSpec -> [PrimArg] -> [PrimVarName]
                            -> AliasMap -> Compiler ProcSpec
_updatePrimCallForSpecz spec args aliasedParams aliasMap = do
    calleeDef <- getProcDef spec
    let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
    let calleeMultiSpeczInfo = procArgAliasMultiSpeczInfo analysis
    let nonAliasedArgWithParams = List.filter (\(arg, param) ->
                -- it should be in callee's interesting params list
                List.elem param calleeMultiSpeczInfo
                -- it shouldn't be aliased
                -- (it can only be [ArgVar] 
                --  if it passed the first check)
                && (let ArgVar{argVarName=argName, 
                                argVarFinal=final} = arg in
                    notElem argName aliasedParams
                    && not (connectedToOthersInDS argName aliasMap)
                    && final)
            ) (pairArgVarWithParam args calleeProto)
    let nonAliasedParams = List.map snd nonAliasedArgWithParams
    return 
        (if List.null nonAliasedParams
        then spec
        else
            let speczId = 
                    Just $ nonAliasedParamsToSpeczId 
                            calleeMultiSpeczInfo nonAliasedParams
            in
            spec { procSpeczVersionID = speczId })


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMap -> [PrimVarName] -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasMap aliasedParams
    args@[fIn@ArgVar{argVarName=inName,argVarFinal=final},
          fOut, offset, ArgInt des typ,
          size, offset2, mem] =
        if notElem inName aliasedParams
            && not (connectedToOthersInDS inName aliasMap) && final
            && des /= 1
        then [fIn, fOut, offset, ArgInt 1 typ, size, offset2, mem]
        else args
_updateMutateForAlias _ _ args = args

----------------------------------------------------------------
--
-- Multiple specialization
--
----------------------------------------------------------------

-- Currently we use [Int] as [SpeczVersionId]. 
-- The bijection works as: 
-- InterestingParams: ["x", "y", "z"]
--  NonAliasedParams: ["x", "y"]
--            Bitmap: 011
-- (the least significant bit is for the first in the list)
--    SpeczVersionId: 5
-- The [String] representation of [SpeczVersionId] is just the hex
-- of the [Int]


-- List all possible specialized version ids since we are
-- generating all versions for now.
allPossiblespeczIds :: AliasMultiSpeczInfo -> [SpeczVersionId]
allPossiblespeczIds speczInfo = 
    let maxId = (2 ^ List.length speczInfo) - 1 in
        if List.length speczInfo >= 20
        -- TODO: handle this
        then shouldnt "Too many versions"
        else [1..maxId] 


-- Return a list of non aliased parameters based on the given id
speczIdToNonAliasedParams :: AliasMultiSpeczInfo
                            -> SpeczVersionId -> [PrimVarName]
speczIdToNonAliasedParams speczInfo speczId =
    List.zip [0..] speczInfo 
    |> List.filter (\(idx, _) -> 
            Bits.testBitDefault speczId idx)
    |> List.map snd


-- Return the corresponding [SpeczVersionId] of the given 
-- non aliased parameters.
nonAliasedParamsToSpeczId :: AliasMultiSpeczInfo
                            -> [PrimVarName] -> SpeczVersionId
nonAliasedParamsToSpeczId speczInfo nonAliasedParams =
    List.zip [0..] speczInfo
    |> List.map (\(idx, param) ->
        if List.elem param nonAliasedParams
            then Bits.bit idx
            else Bits.zeroBits)
    |> List.foldl (Bits..|.) Bits.zeroBits 


-- |Log a message, if we are logging optimisation activity.
logTransform :: String -> Compiler ()
logTransform = logMsg Transform
