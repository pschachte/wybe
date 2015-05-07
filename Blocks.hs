--  File     : Blocks.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module Blocks ( blockTransformModule ) where

import AST
import Data.Maybe
import Data.Map as Map
import Data.List as List


blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule mod = do
  reenterModule mod
  procs <- getModuleImplementationField modProcs
  let procs' = Map.foldrWithKey (noteProcsSuperprocs mod) procs procs
  updateImplementation (\imp -> imp {modProcs = procs'})
  exitModule
  return ()


noteProcsSuperprocs :: ModSpec -> ProcName -> [ProcDef] -> 
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcsSuperprocs mod name defs procs =
  List.foldr (\(def,n) ->
               noteImplnSuperprocs (ProcSpec mod name n) (procImpln def)) 
  procs $ zip defs [0..]

noteImplnSuperprocs :: ProcSpec -> ProcImpln -> 
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnSuperprocs _ (ProcDefSrc _) _ =
  shouldnt "scanning unprocessed code for calls"
noteImplnSuperprocs caller (ProcDefPrim _ body) procs =
  let callers = foldBodyDistrib (noteCall caller) 
                Map.empty mergeCallers mergeCallers
                body
  in  registerCallers caller callers procs
noteImplnSuperprocs _ (ProcDefBlocks _ _) _ =
  shouldnt "scanning already compiled code for calls"

-- |Compute for each proc a total count of calls and determine if it
-- should be a subproc of another proc, and if so, which one.
type CallRec = Map ProcSpec Int


noteCall :: ProcSpec -> Bool -> Prim -> CallRec -> CallRec
noteCall caller final (PrimCall spec _) rec = 
  Map.alter (Just . maybe 1 (1+)) spec rec
noteCall caller final (PrimNop) rec = rec
noteCall caller final (PrimForeign _ _ _ _) rec = rec


-- updateCallInfo :: Bool -> Maybe Int -> Int
-- updateCallInfo final Nothing = 1
-- updateCallInfo final (Just n) = n+1


mergeCallers :: CallRec -> CallRec -> CallRec
mergeCallers rec1 rec2 = Map.unionWith (\n1 n2 -> n1+n2) rec1 rec2

mergeSuperprocs NoSuperproc _ = NoSuperproc
mergeSuperprocs _ NoSuperproc = NoSuperproc
mergeSuperprocs AnySuperproc sp = sp
mergeSuperprocs sp AnySuperproc = sp
mergeSuperprocs sp1@(SuperprocIs p1) (SuperprocIs p2) =
  if p1 == p2 then sp1 else NoSuperproc

registerCallers :: ProcSpec -> CallRec -> Map Ident [ProcDef] -> Map Ident [ProcDef]
registerCallers caller callRec procs =
  List.foldr (\(callee,count) ps ->
               Map.adjust (adjustNth (noteCalls caller count) (procSpecID callee))
               (procSpecName callee) ps)
  procs
  $ Map.assocs callRec


noteCalls :: ProcSpec -> Int -> ProcDef -> ProcDef
noteCalls caller count procdef =
  procdef { procCallers = Map.alter (Just . (+count) . fromMaybe 0) caller
            $ procCallers procdef}



adjustNth :: (a -> a) -> Int -> [a] -> [a]
adjustNth _ _ [] = error "adjustNth refers beyond list end"
adjustNth fn 0 (e:es) = fn e:es
adjustNth fn n (e:es) 
  | n > 0 = e : adjustNth fn (n-1) es
  | True  = error "adjustNth with negative n"
