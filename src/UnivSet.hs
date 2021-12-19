--  File     : Util.hs
--  Author   : Peter Schachte
--  Purpose  : Provide a set type supporting the universal set.
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE DeriveGeneric #-}


module UnivSet (
    UnivSet(..), UnivSet.union, UnivSet.intersection, UnivSet.member,
    UnivSet.isEmpty, UnivSet.isUniv
    ) where


import Data.Set as S
import qualified GHC.IO.Buffer as S
import           GHC.Generics (Generic)


----------------------------------------------------------------
--
-- A set type that supports a top (universal set) value, making this a lattice.
--
----------------------------------------------------------------

data UnivSet a = UniversalSet | FiniteSet (Set a) deriving (Show, Generic)


union :: Ord a => UnivSet a -> UnivSet a -> UnivSet a
union UniversalSet _ = UniversalSet
union _ UniversalSet = UniversalSet
union (FiniteSet s1) (FiniteSet s2) = FiniteSet $ s1 `S.union` s2

intersection :: Ord a => UnivSet a -> UnivSet a -> UnivSet a
intersection UniversalSet s = s
intersection s UniversalSet = s
intersection (FiniteSet s1) (FiniteSet s2) = FiniteSet $ s1 `S.intersection` s2

member :: Ord a => a -> UnivSet a -> Bool
member elt UniversalSet = True
member elt (FiniteSet s) = elt `S.member` s

isEmpty :: UnivSet a -> Bool
isEmpty UniversalSet = False
isEmpty (FiniteSet s) = S.null s

isUniv :: UnivSet a -> Bool
isUniv UniversalSet = True
isUniv (FiniteSet s) = False
 