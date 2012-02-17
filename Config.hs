--  File     : Config.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sat Feb 18 00:38:48 2012
--  Purpose  : Configuration for frege compiler
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Config (sourceExtension, objectExtension, executableExtension,
               interfaceExtension) where

sourceExtension :: String
sourceExtension = "frg"

objectExtension :: String
objectExtension = "o"

executableExtension :: String
executableExtension = ""

interfaceExtension :: String
interfaceExtension = "int"

