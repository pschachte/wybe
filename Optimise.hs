--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: © 2014 Peter Schachte.  All rights reserved.

module Optimise (optimiseMod) where

import AST
import Options (LogSelection(Optimise))
import Types
import Expansion
import LastUse
import Data.List as List
import Data.Map as Map
import Data.Graph
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans

optimiseMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
optimiseMod mods thisMod = do
    reenterModule thisMod
    -- checkFullyTyped -- Sanity check: be sure everything is fully typed
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(pspec,pspec,
              nub $ concatMap (localBodyCallees thisMod . procBody) procDefs)
             | (name,procDefs) <- procs,
               (n,def) <- zip [0..] procDefs,
               let pspec = ProcSpec thisMod name n
             ]
    logOptimise $ "Optimise SCCs:\n" ++ 
      unlines (List.map (show . sccElts) ordered)
    mapM_ optimiseSCCBottomUp ordered
    finishModule
    return (False,[])


procBody :: ProcDef -> ProcBody
procBody def =
    case procImpln def of
        ProcDefSrc _ -> shouldnt "Optimising un-compiled code"
        ProcDefPrim _ body -> body


sccElts (AcyclicSCC single) = [single]
sccElts (CyclicSCC multi) = multi


optimiseSCCBottomUp :: SCC ProcSpec -> Compiler ()
optimiseSCCBottomUp (AcyclicSCC pspec) = do
    optimiseProc pspec
optimiseSCCBottomUp (CyclicSCC pspecs) = do
    mapM_ optimiseProc pspecs


optimiseProc :: ProcSpec -> Compiler ()
optimiseProc pspec = do
    logOptimise $ ">>> Optimise " ++ show pspec
    updateProcDefM (optimiseProcDef pspec) pspec
    return ()


optimiseProcDef :: ProcSpec -> ProcDef -> Compiler ProcDef
optimiseProcDef pspec def = do
    logOptimise $ "Definition of " ++ show pspec ++
      " before optimisation:" ++ showProcDef 4 def
    def' <- procExpansion def >>= markLastUse pspec >>= inlineIfWanted
    logOptimise $ "Definition of " ++ show pspec ++
      " after optimisation:" ++ showProcDef 4 def'
    return def'


----------------------------------------------------------------
--                       Deciding what to inline
----------------------------------------------------------------

inlineIfWanted :: ProcDef -> Compiler ProcDef
inlineIfWanted def
    |  NoFork == bodyFork body && not (procInline def) = do
    logOptimise $ "Considering inline of " ++ procName def
    let benefit = 2 + procCost proto -- add 2 for time saving
    logOptimise $ "  benefit = " ++ show benefit
    let cost = bodyCost $ bodyPrims body
    logOptimise $ "  cost = " ++ show cost
    if  benefit >= cost
    then return $ def { procInline = True }
    else return def
    where ProcDefPrim proto body = procImpln def
inlineIfWanted def = return def


procCost :: PrimProto -> Int
procCost proto = 
    1 + (length $ List.filter (not . phantomParam) $ primProtoParams proto)

bodyCost :: [Placed Prim] -> Int
bodyCost pprims = sum $ List.map (primCost . content) pprims

primCost :: Prim -> Int
primCost (PrimCall _ args) = 1 + (sum $ List.map argCost args)
primCost (PrimForeign "llvm" _ _ _) = 1 -- single instuction, so cost = 1
primCost (PrimForeign _ _ _ args) = 1 + (sum $ List.map argCost args)
primCost (PrimNop) = 0

argCost :: PrimArg -> Int
argCost arg = if phantomArg arg then 0 else 1

phantomParam :: PrimParam -> Bool
phantomParam param = phantomType $ primParamType param

phantomArg :: PrimArg -> Bool
phantomArg (ArgVar _ ty _ _ _) = phantomType ty
phantomArg _ = False -- Nothing but a var can be a phantom

phantomType Unspecified = False
phantomType ty = "phantom" == typeName ty

----------------------------------------------------------------
--                     Handling the call graph
----------------------------------------------------------------


-- |Finding all procs called by a given proc body
localBodyCallees :: ModSpec -> ProcBody -> [ProcSpec]
localBodyCallees modspec body =
    mapBodyPrims (localCallees modspec) (++) [] (++) [] body


localCallees :: ModSpec -> Prim -> [ProcSpec]
localCallees modspec (PrimCall pspec _) = [pspec]
localCallees _ _ = []


-- |Log a message, if we are logging unbrancher activity.
logOptimise :: String -> Compiler ()
logOptimise s = logMsg Optimise s
