--  File     : Config.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sat Feb 18 00:38:48 2012
--  Purpose  : Configuration for wybe compiler
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Compiler configuration parameters.  These may vary between
--  OSes.
module Config (sourceExtension, objectExtension, executableExtension,
               interfaceExtension) where

-- |The file extension for source files.
sourceExtension :: String
sourceExtension = "wybe"

-- |The file extension for object files.
objectExtension :: String
objectExtension = "o"

-- |The file extension for executable files.
executableExtension :: String
executableExtension = ""

-- |The file extension for interface files.
interfaceExtension :: String
interfaceExtension = "int"

