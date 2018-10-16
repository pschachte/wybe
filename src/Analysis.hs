--  File     : Analysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Entry point of all kinds of analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module Analysis (analyseMod) where

import           AliasAnalysis
import           Control.Monad.Trans
import           Control.Monad.Trans.State
-- import           FreshnessAnalysis
import           AST
import           Control.Monad
import           Data.Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Options                   (LogSelection (Optimise))
import           Util

analyseMod :: [SCC ProcSpec] -> Compiler ()
analyseMod orderedScc = do
  mapM_ aliasSccBottomUp orderedScc
  mapM_ freshnessSccBottomUp orderedScc




  ----------------------------------------------------------------
--                     Freshness Analysis
----------------------------------------------------------------
freshnessSccBottomUp :: SCC ProcSpec -> Compiler ()
freshnessSccBottomUp procs = mapM_ freshnessProcBottomUp $ sccElts procs

freshnessProcBottomUp :: ProcSpec -> Compiler ()
freshnessProcBottomUp pspec = do
    updateProcDefM (updateFreshness pspec) pspec
    return ()


-- Build a set of fresh vars and update destructive flag in lpvm mutate
-- instruction
updateFreshness :: ProcSpec -> ProcDef -> Compiler ProcDef
updateFreshness spec procDef = do
    let (ProcDefPrim proto body analysis) = procImpln procDef
    let aliasPairs = procArgAliases analysis
    let primParams = primProtoParams proto
    let aliasParams = _aliasPairsToParams primParams aliasPairs

    let prims = bodyPrims body
    (freshset, _, prims')
          <- foldM freshInPrim (Set.empty, aliasParams, []) prims
    logAnalysis $ "\n*** Freshness analysis" ++ ": "
                    ++ procName procDef ++ " " ++ show freshset ++ "\n\n"
    let body' = body { bodyPrims = prims' }
    return procDef { procImpln = ProcDefPrim proto body' analysis }

-- Update args in a signle (alloc/mutate) prim
freshInPrim :: (Set PrimVarName, [(PrimVarName, PrimVarName)], [Placed Prim])
                -> Placed Prim
                -> Compiler (Set PrimVarName, [(PrimVarName, PrimVarName)],
                              [Placed Prim])
freshInPrim (freshVars, aliasParams, prims)
    (Placed (PrimForeign lang "mutate" flags args) pos) =
      return (freshVars', aliasParams,
        prims ++ [Placed (PrimForeign lang "mutate" flags args') pos])
          where
            (freshVars', args') =
              _freshCheckInMutate freshVars aliasParams args
freshInPrim (freshVars, aliasParams, prims)
    (Unplaced (PrimForeign lang "mutate" flags args)) =
      return (freshVars', aliasParams,
        prims ++ [Unplaced (PrimForeign lang "mutate" flags args')])
          where
            (freshVars', args') =
              _freshCheckInMutate freshVars aliasParams args
freshInPrim (freshVars, aliasParams, prims) prim =
    case content prim of
      (PrimForeign _ "alloc" _ args) ->
          return (freshVars', aliasParams, prims ++ [prim])
              where
                freshVars' = List.foldl _freshCheckInAlloc freshVars args
      PrimCall spec args -> do
          -- Should also append aliases of prims that are called in this caller
          -- to aliasParams
          calleeDef <- getProcDef spec
          let (ProcDefPrim calleeProto body analysis) = procImpln calleeDef
          let calleeAlias = procArgAliases analysis
          logAnalysis $ "\n    call " ++ show spec ++" (callee): "
          logAnalysis $ "    " ++ show calleeProto
          -- logAnalysis $ "    PrimCall args: " ++ show args
          -- logAnalysis $ "    callerAlias: " ++ show callerAlias
          logAnalysis $ "    calleeAlias: " ++ show calleeAlias
          let aliasNames' = aliasPairsToVarNames args calleeAlias
          logAnalysis $ "    names: " ++ show aliasNames'
          return (freshVars, aliasParams ++ aliasNames', prims ++ [prim])
      _ ->
        return (freshVars, aliasParams, prims ++ [prim])


-- newly allocated space is fresh
_freshCheckInAlloc :: Set PrimVarName -> PrimArg -> Set PrimVarName
_freshCheckInAlloc freshVars (ArgVar nm _ FlowOut _ _) = Set.insert nm freshVars
_freshCheckInAlloc freshVars _                         = freshVars

-- variable after mutation is also fresh
_freshCheckInMutate :: Set PrimVarName -> [(PrimVarName, PrimVarName)]
                      -> [PrimArg] -> (Set PrimVarName, [PrimArg])
_freshCheckInMutate freshVars aliasParams
    [fIn@(ArgVar inName _ _ _ final), fOut@(ArgVar outName _ _ _ _), size,
    offset, ArgInt des typ, mem] =
        let
            freshVars' = Set.insert outName freshVars
        in
            if Set.member inName freshVars'
                && final
                && not (isVarAliased inName aliasParams)
            then (freshVars', [fIn, fOut, size, offset, ArgInt 1 typ, mem])
            else (freshVars', [fIn, fOut, size, offset, ArgInt 0 typ, mem])
_freshCheckInMutate freshVars _ args = (freshVars, args)

-- Helper: convert alias index pairs to var name pairs
_aliasPairsToParams :: [PrimParam] -> [AliasPair]
                            -> [(PrimVarName, PrimVarName)]
_aliasPairsToParams primCallArgs =
  List.foldr (\(p1,p2) aliasNames ->
      let v1 = primCallArgs !! p1
          v2 = primCallArgs !! p2
      in
        (primParamName v1, primParamName v2):aliasNames
      ) []

-- |Log a message, if we are logging optimisation activity.
logAnalysis :: String -> Compiler ()
logAnalysis = logMsg Optimise
