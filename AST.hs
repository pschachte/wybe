--  File     : AST.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.
--


type Module = [ModuleItem]

data ModuleItem =
  ModuleStart String -- module name
  | TypeDecl String TypeDefn
  | FnDef String [Param] FnBody
  | ProcDef String [Param] ProcBody
  deriving Show
