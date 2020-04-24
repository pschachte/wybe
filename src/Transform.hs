--  File     : Transform.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Transform (transformProc) where

import           AliasAnalysis
import           AST
import           Control.Monad
import           Data.Bits     as Bits
import           Data.List     as List
import           Data.Map      as Map
import           Data.Maybe    as Maybe
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
        aliasMap <- initAliasMap inputParams []
        body' <- transformBody caller body (aliasMap, Map.empty)

        -- generate&transform all specz versions
        let speczInfo = procArgAliasMultiSpeczInfo analysis
        let versions = allPossiblespeczIds speczInfo
        speczBodies' <- mapM (\id -> do
                let nonAliasedParams = speczIdToNonAliasedParams speczInfo id 
                aliasMap <- initAliasMap inputParams nonAliasedParams
                logTransform $ replicate 60 '~'
                logTransform $ "Generating specialized version: " ++ show id
                sbody <- 
                    transformBody caller body (aliasMap, Map.empty)
                return (id, sbody)
            ) versions

        return def { procImpln = 
                        ProcDefPrim caller body' 
                        analysis (Map.fromList speczBodies')}

transformProc def = return def


-- init aliasMap based on the given "nonAliasedParams",
-- in the transform step, we don't have "MaybeAliasByParam".
initAliasMap inputParams nonAliasedParams = do
    logTransform $ "inputParams:      " ++ show inputParams
    logTransform $ "nonAliasedParams: " ++ show nonAliasedParams
    return $ 
        List.foldl (\aliasMap param -> 
            if List.notElem param nonAliasedParams
                then unionTwoInDS (LiveVar param) (AliasByParam param) aliasMap
                else aliasMap
            ) emptyDS inputParams 


transformBody :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Compiler ProcBody
transformBody caller body (aliasMap, deadCells) = do
    -- (1) Analysis of current caller's prims
    ((aliaseMap', deadCells'), newPrims) <- 
            transformPrims caller body (aliasMap, deadCells)
    -- Update bodyPrims of this procbody
    let body' = body { bodyPrims = newPrims }

    -- (2) Analysis of caller's bodyFork
    -- Update body while checking alias incurred by bodyfork
    transformForks caller body' (aliaseMap', deadCells')


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells) 
        -> Compiler ((AliasMapLocal, DeadCells), [Placed Prim])
transformPrims caller body (aliasMap, deadCells) = do
    let prims = bodyPrims body
    -- Transform simple prims:
    logTransform "\nTransform prims (transformPrims):   "
    foldM transformPrim ((aliasMap, deadCells), []) prims


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Compiler ProcBody
transformForks caller body (aliasMap, deadCells) = do
    logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logTransform "Forking:"
            fBodies' <-
                mapM (\currBody -> 
                        transformBody caller currBody (aliasMap, deadCells)
                ) fBodies
            return body { bodyFork = fork {forkBodies=fBodies'} }
        NoFork -> do
            -- NoFork: transform prims done
            logTransform "No fork."
            return body


-- Build up alias pairs triggerred by proc calls
transformPrim :: ((AliasMapLocal, DeadCells), [Placed Prim])
        -> Placed Prim -> Compiler ((AliasMapLocal, DeadCells), [Placed Prim])
transformPrim ((aliasMap, deadCells), prims) prim = do
    -- TODO: Redundent work here. We should change the current design.
    aliasMap' <- updateAliasedByPrim aliasMap prim
    logTransform $ "\n--- prim:           " ++ show prim
    let primc = content prim
    
    (primc', deadCells') <- case primc of
            PrimCall spec args -> do
                spec' <- _updatePrimCallForSpecz spec args aliasMap
                return (PrimCall spec' args, deadCells)
            PrimForeign "lpvm" "mutate" flags args -> do
                let args' = _updateMutateForAlias aliasMap args
                return (PrimForeign "lpvm" "mutate" flags args', deadCells)
            -- dead cell transform
            PrimForeign "lpvm" "access" _ args -> do
                deadCells' 
                    <- updateDeadCellsByAccessArgs (aliasMap, deadCells) args
                return (primc, deadCells')
            PrimForeign "lpvm" "alloc" _ args  -> do
                let (result, deadCells') = 
                        assignDeadCellsByAllocArgs deadCells args
                let primc' = case result of 
                        Nothing -> primc
                        Just (selectedCell, []) -> 
                            -- replace "alloc" with "move" by reusing the 
                            -- "selectedCell".
                            let [_, varOut] = args in
                            let varIn = 
                                    varOut {argVarName = selectedCell,
                                            argVarFlow = FlowIn,
                                            argVarFinal = True}
                            in
                            PrimForeign "llvm" "move" [] [varIn, varOut]
                        _ -> shouldnt "invalid aliasMap for transform"
                when (Maybe.isJust result) $ 
                        logTransform "replacing [alloc] with [move]."
                return (primc', deadCells')
            -- default case
            _ -> return (primc, deadCells)
    
    prim' <- updatePlacedM (\_ -> return primc') prim
    logTransform $ "--- transformed to: " ++ show prim'
    return ((aliasMap', deadCells'), prims ++ [prim'])


-- Update PrimCall to make it uses a better specialized version
-- than the general version based on the current [AliasMap]
_updatePrimCallForSpecz :: ProcSpec -> [PrimArg] -> AliasMapLocal
        -> Compiler ProcSpec
_updatePrimCallForSpecz spec args aliasMap = do
    calleeDef <- getProcDef spec
    let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
    let calleeMultiSpeczInfo = procArgAliasMultiSpeczInfo analysis
    let nonAliasedArgWithParams = List.filter (\(arg, param) ->
                -- it should be in callee's interesting params list
                List.elem param calleeMultiSpeczInfo
                -- it should be an interesting variable
                && Right [] == isArgVarInteresting aliasMap arg
            ) (pairArgVarWithParam args calleeProto)
    let nonAliasedParams = List.map snd nonAliasedArgWithParams
    return 
        (if List.null nonAliasedParams
        then spec
        else
            let speczId = 
                    Just $ nonAliasedParamsToSpeczId calleeMultiSpeczInfo nonAliasedParams
            in
            spec { procSpeczVersionID = speczId })


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMapLocal -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasMap
    args@[fIn, fOut, offset, ArgInt des typ, size, offset2, mem] =
        if des /= 1 && Right [] == isArgVarInteresting aliasMap fIn
        then [fIn, fOut, offset, ArgInt 1 typ, size, offset2, mem]
        else args
_updateMutateForAlias _ args = args

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
