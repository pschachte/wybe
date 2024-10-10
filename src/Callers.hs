--  File     : Callers.hs
--  Author   : Peter Schachte
--  Purpose  : Find all callers for each proc and count static calls per caller
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Callers ( collectCallers, getSccProcs ) where

import           AST
import           Data.Graph
import           Data.List  as List
import           Data.Map   as Map
import           Data.Maybe
import qualified Data.Set as Set

-- | Count calls to all the procs in the specified module from procs in modules
-- in the specified list of modules, which is a strongly connected component in
-- the module dependency graph.
collectCallers :: ModSpec -> Compiler ()
collectCallers mod = do
  reenterModule mod
  procs <- getModuleImplementationField modProcs
  -- XXX For what we use this for, we really need to count all the calls to each
  -- private proc in the same file (ie, having the same modRootModSpec) as the
  -- caller.
  let procs' = Map.foldrWithKey (noteProcCallers mod) procs procs
  updateImplementation (\imp -> imp {modProcs = procs'})
  reexitModule
  return ()


noteProcCallers :: ModSpec -> ProcName -> [ProcDef] ->
                   Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcCallers mod name defs procs =
  List.foldr (\(def,n) ->
               noteImplnCallers mod
                      (ProcSpec mod name n generalVersion) (procImpln def))
  procs $ zip defs [0..]

noteImplnCallers :: ModSpec -> ProcSpec -> ProcImpln ->
                    Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnCallers _ _ (ProcDefSrc _) _ =
  shouldnt "scanning unprocessed code for calls"
noteImplnCallers mod caller ProcDefPrim{procImplnBody = body} procs =
  let callers = foldBodyDistrib (noteCall mod caller)
                Map.empty mergeCallers mergeCallers
                body
  in  registerCallers caller callers procs

-- |Compute for each proc a total count of calls and determine if it
-- should be a subproc of another proc, and if so, which one.
type CallRec = Map ProcSpec Int


noteCall :: ModSpec -> ProcSpec -> Bool -> Prim -> CallRec -> CallRec
noteCall mod caller final prim rec =
    List.foldr (noteCalls' mod) rec (localCallees mod prim)


noteCalls' :: ModSpec -> ProcSpec -> CallRec -> CallRec
noteCalls' mod spec rec
  | mod == procSpecMod spec  = Map.alter (Just . maybe 1 (1+)) spec rec
  | otherwise = rec


mergeCallers :: CallRec -> CallRec -> CallRec
mergeCallers rec1 rec2 = Map.unionWith (+) rec1 rec2

registerCallers :: ProcSpec -> CallRec -> Map Ident [ProcDef]
                   -> Map Ident [ProcDef]
registerCallers caller callRec procs =
  List.foldr (\(callee,count) ps ->
               Map.adjust (adjustNth (noteCalls caller count)
                           (procSpecID callee))
               (procSpecName callee) ps)
  procs
  $ Map.assocs callRec


noteCalls :: ProcSpec -> Int -> ProcDef -> ProcDef
noteCalls caller count procdef =
  procdef { procCallers = Map.alter (Just . (+count) . fromMaybe 0) caller
            $ procCallers procdef}


-- Apply a function to the nth element of a list, leaving the rest untouched.
adjustNth :: (a -> a) -> Int -> [a] -> [a]
adjustNth _ _ [] = error "adjustNth refers beyond list end"
adjustNth fn 0 (e:es) = fn e:es
adjustNth fn n (e:es)
  | n > 0     = e : adjustNth fn (n-1) es
  | otherwise = error "adjustNth with negative n"


----------------------------------------------------------------
--                     Handling the call graph
----------------------------------------------------------------
-- Note: We do not consider Multiple Specialization in the call graph.

getSccProcs :: ModSpec -> Compiler [SCC ProcSpec]
getSccProcs thisMod = do
  procs <- getModuleImplementationField (Map.toList . modProcs)
  let ordered =
          stronglyConnComp
          [(pspec,pspec,
            nub $ concatMap
                ( localBodyCallees thisMod
                . trustFromJust "Analysing un-compiled code"
                . procBody) procDefs)
           | (name,procDefs) <- procs,
             (n,def) <- zip [0..] procDefs,
             let pspec = ProcSpec thisMod name n generalVersion
           ]
  return ordered


-- |Finding all procs called by a given proc body
localBodyCallees :: ModSpec -> ProcBody -> [ProcSpec]
localBodyCallees modspec body =
  foldBodyDistrib (\_ prim callees -> localCallees modspec prim ++ callees)
  [] (++) (++) body

-- | Find all callees in a given prim
localCallees :: ModSpec -> Prim -> [ProcSpec]
localCallees modspec (PrimCall _ pspec _ args _)
  = pspec{procSpeczVersion=generalVersion}:concatMap (argRefs modspec) args
localCallees modspec (PrimHigher _ fn _ args)
  = concatMap (argRefs modspec) (fn:args)
localCallees modspec (PrimForeign _ _ _ args)
  = concatMap (argRefs modspec) args

-- | Find all callees in a given PromArg
argRefs :: ModSpec -> PrimArg -> [ProcSpec]
argRefs modspec (ArgClosure pspec closed _)
  = localCallees modspec (PrimCall (shouldnt "argRefs") pspec Pure closed univGlobalFlows)
argRefs _ _ = []