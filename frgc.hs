--  File     : frgc.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : 
--  Copyright: © 2011 Peter Schachte.  All rights reserved.
--

module Main where

import Parser
import Scanner

main = do
  toks <- inputTokens
  print $ parse $ map frgtoken toks
