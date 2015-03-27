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
  let procs' = Map.foldr noteProcsSubprocs procs procs
  exitModule
  return ()


noteProcsSubprocs :: [ProcDef] -> Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcsSubprocs defs procs =
  List.foldr (noteImplnSubprocs . procImpln) procs defs

noteImplnSubprocs :: ProcImpln -> Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnSubprocs (ProcDefSrc _) _ = 
  shouldnt "scanning unprocessed code for calls"
noteImplnSubprocs (ProcDefPrim _ body) procs = 
  procs
--  foldBodyPrims noteCall procs
noteImplnSubprocs (ProcDefBlocks _ _) _ = 
  shouldnt "scanning already compiled code for calls"