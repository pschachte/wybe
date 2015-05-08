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
-- XXX do the actual work here:
noteImplnSuperprocs caller (ProcDefPrim _ body) procs = procs
noteImplnSuperprocs _ (ProcDefBlocks _ _) _ =
  shouldnt "scanning already compiled code for calls"
