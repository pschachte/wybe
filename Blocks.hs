--  File     : Blocks.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module Blocks ( blockTransformModule ) where

import AST
import Data.Map as Map
import Data.List as List


blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule mod = do
  reenterModule mod
  procs <- getModuleImplementationField modProcs
  let procs' = Map.foldr noteProcsSuperprocs procs procs
  updateImplementation (\imp -> imp {modProcs = procs'})
  exitModule
  return ()


noteProcsSuperprocs :: [ProcDef] -> Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcsSuperprocs defs procs =
  List.foldr (noteImplnSuperprocs . procImpln) procs defs

noteImplnSuperprocs :: ProcImpln -> Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnSuperprocs (ProcDefSrc _) _ =
  shouldnt "scanning unprocessed code for calls"
noteImplnSuperprocs (ProcDefPrim _ body) procs =
  let callers = foldBodyDistrib (noteCall undefined) 
                Map.empty mergeCallers mergeCallers
                body
  in  registerCallers callers procs
noteImplnSuperprocs (ProcDefBlocks _ _) _ =
  shouldnt "scanning already compiled code for calls"

-- |Compute for each proc a total count of calls and determine if it
-- should be a subproc of another proc, and if so, which one.
type CallRec = Map ProcSpec (Int,SuperprocSpec)


noteCall :: ProcSpec -> Bool -> Prim -> CallRec -> CallRec
noteCall caller final (PrimCall spec _) rec = 
  Map.alter (Just . updateCallInfo caller final) spec rec
noteCall caller final (PrimNop) rec = rec
noteCall caller final (PrimForeign _ _ _ _) rec = rec


updateCallInfo :: ProcSpec -> Bool ->
                  Maybe (Int,SuperprocSpec) -> (Int,SuperprocSpec)
updateCallInfo caller final Nothing = (1,SuperprocIs caller)
updateCallInfo caller final (Just (n,NoSuperproc)) = (n+1,NoSuperproc)
updateCallInfo caller final (Just (n,AnySuperproc)) = (n+1,SuperprocIs caller)
updateCallInfo caller final (Just (n,sup@(SuperprocIs oldcaller))) = 
  (n+1, if oldcaller == caller then sup else NoSuperproc)

mergeCallers :: CallRec -> CallRec -> CallRec
mergeCallers rec1 rec2 = 
  Map.unionWith (\(n1,sp1) (n2,sp2) -> (n1+n2,mergeSuperprocs sp1 sp2)) 
  rec1 rec2

mergeSuperprocs NoSuperproc _ = NoSuperproc
mergeSuperprocs _ NoSuperproc = NoSuperproc
mergeSuperprocs AnySuperproc sp = sp
mergeSuperprocs sp AnySuperproc = sp
mergeSuperprocs sp1@(SuperprocIs p1) (SuperprocIs p2) =
  if p1 == p2 then sp1 else NoSuperproc

registerCallers :: CallRec -> Map Ident [ProcDef] -> Map Ident [ProcDef]
registerCallers callRec procs =
  List.foldr (\(callee,(count,sup)) ps ->
               Map.adjust (adjustNth (noteCalls count sup) (procSpecID callee))
               (procSpecName callee) ps)
  procs
  $ Map.assocs callRec


noteCalls :: Int -> SuperprocSpec -> ProcDef -> ProcDef
noteCalls count sup procdef =
  procdef { procCallCount = count + procCallCount procdef,
            procSuperproc = mergeSuperprocs sup $ procSuperproc procdef }



adjustNth :: (a -> a) -> Int -> [a] -> [a]
adjustNth _ _ [] = error "adjustNth refers beyond list end"
adjustNth fn 0 (e:es) = fn e:es
adjustNth fn n (e:es) 
  | n > 0 = e : adjustNth fn (n-1) es
  | True  = error "adjustNth with negative n"
