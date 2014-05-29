--  File     : Util.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu May 22 14:43:47 2014
--  Purpose  : Various small utility functions
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--

module Util (checkMaybe) where


-- | Test the value in a maybe, and if it fails, return Nothing.
checkMaybe :: (a -> Bool) -> Maybe a -> Maybe a
checkMaybe test Nothing = Nothing
checkMaybe test (Just val) = if test val then Just val else Nothing
