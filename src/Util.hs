--  File     : Util.hs
--  Author   : Peter Schachte
--  Purpose  : Various small utility functions
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE DeriveGeneric #-}

module Util (sameLength, maybeNth, checkMaybe, setMapInsert,
             applyPair, fillLines, nop, sccElts, DisjointSet, 
             emptyDS, addOneToDS, unionTwoInDS, combineTwoDS, 
             removeOneFromDS, removeFromDS, connectedToOthersInDS,
             mapDS, filterDS, dsToTransitivePairs, removeDupTuples,
             pruneTuples, transitiveTuples, cartProd) where


import           Data.Graph
import           Data.List    as List
import           Data.Map     as Map
import           Data.Set     as Set
import           Data.Maybe (isJust)
import           GHC.Generics (Generic)
import           Flow ((|>))


-- |Do the the two lists have the same length?
sameLength :: [a] -> [b] -> Bool
sameLength [] [] = True
sameLength (_:as) (_:bs) = sameLength as bs
sameLength _ _ = False


-- |Return the nth element of the list, if present, else Nothing.
maybeNth :: (Eq n, Ord n, Num n) => n -> [a] -> Maybe a
maybeNth _ []     = Nothing
maybeNth 0 (e:_ ) = Just e
maybeNth n (_:es)
 | n > 0          = maybeNth (n - 1) es
 | otherwise      = Nothing


-- |Test the value in a maybe, and if it fails, return Nothing.
checkMaybe :: (a -> Bool) -> Maybe a -> Maybe a
checkMaybe test Nothing = Nothing
checkMaybe test (Just val) = if test val then Just val else Nothing


-- |Insert an element into the set mapped to by the specified key in
--  the given map.  Maps to a singleton set if there is no current
--  mapping for the specified key.
setMapInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
setMapInsert key item dict =
    Map.alter (\ms -> case ms of
                    Nothing -> Just $ Set.singleton item
                    Just s -> Just $ Set.insert item s)
    key dict



-- |Apply a pair of functions to a value and return a pair of results.
applyPair :: (a->b,a->c) -> a -> (b,c)
applyPair (f,g) val = (f val, g val)


-- |fillLines marginText currColumn lineLength text
--  Fill lines with text.  marginText is the string to start each
--  line but the first.  currColumn is the output column at the start
--  of the first word, and lineLength is the maximum line length.
fillLines :: String -> Int -> Int -> String -> String
fillLines marginText currColumn lineLength text =
    fillLines' marginText currColumn lineLength $ words text

fillLines' :: String -> Int -> Int -> [String] -> String
fillLines' marginText currColumn lineLength [] = []
fillLines' marginText currColumn lineLength [word] = word
fillLines' marginText currColumn lineLength (word1:word2:words) =
    let nextColumn = currColumn + length word1 + 1
    in  word1 ++
        if nextColumn + length word2 >= lineLength
        then "\n" ++ marginText ++
             fillLines' marginText (length marginText) lineLength (word2:words)
        else " " ++ fillLines' marginText nextColumn lineLength (word2:words)

-- |Do nothing monadically.
nop :: Monad m => m ()
nop = return ()


sccElts :: SCC a -> [a]
sccElts (AcyclicSCC single) = [single]
sccElts (CyclicSCC multi)   = multi


----------------------------------------------------------------
--
-- Helpers used in AliasAnalysis & UnionFind
--
----------------------------------------------------------------

-- King, D.J. and Launchbury, J., 1994, March. Lazy depth-first search and
-- linear graph algorithms in haskell. In Glasgow Workshop on Functional
-- Programming (pp. 145-155).
_reverseE :: Graph -> [Edge]
_reverseE g = [ (w,v) | (v,w) <- edges g]

-- Helper: normalise alias pairs in order
_normaliseTuple :: Ord a => (a,a) -> (a,a)
_normaliseTuple t@(x,y)
    | y < x    = (y,x)
    | otherwise = t

-- Helper: then remove duplicated alias pairs
removeDupTuples :: Ord a => [(a,a)] -> [(a,a)]
removeDupTuples =
    List.map List.head . List.group . List.sort . List.map _normaliseTuple

-- Helper: prune list of tuples with int larger than the range
pruneTuples :: Ord a => [(a,a)] -> a -> [(a,a)]
pruneTuples tuples upperBound =
    List.foldr (\(t1, t2) tps ->
                if t1 < upperBound && t2 < upperBound then (t1, t2):tps
                else tps) [] tuples


-- Helper: to expand alias pairs
-- e.g. Aliases [(1,2),(2,3),(3,4)] is expanded to
-- [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
-- items in pairs are sorted already
transitiveTuples :: [(Int,Int)] -> [(Int,Int)]
transitiveTuples [] = []
transitiveTuples pairs =
    let loBound = List.foldr (\(p1,p2) bound ->
            if p1 < bound then p1
            else bound) 0 pairs
        upBound = List.foldr (\(p1,p2) bound ->
            if p2 > bound then p2
            else bound) 0 pairs
        adj = buildG (loBound, upBound) pairs
        undirectedAdj = buildG (loBound, upBound) (edges adj ++ _reverseE adj)
        elements = vertices undirectedAdj
    in List.foldr (\vertex tuples ->
        let reaches = reachable undirectedAdj vertex
            vertexPairs = [(vertex, r) | r <- reaches, r /= vertex]
        in vertexPairs ++ tuples
        ) [] elements


-- Helper: Cartesian product of escaped FlowIn vars to proc output
cartProd :: [a] -> [a] -> [(a, a)]
cartProd ins outs = [(i, o) | i <- ins, o <- outs]


----------------------------------------------------------------
--
-- Disjoint set for alias map
--
----------------------------------------------------------------
-- TODO: Using Union-Find instead of this naive implementation
-- The old implement is wrong https://github.com/pschachte/wybe/issues/25
-- So we use this version as a quick fix.

type DisjointSet a = Set (Set a)

emptyDS = Set.empty

_findFristInSet :: (a -> Bool) -> Set a -> Maybe a
_findFristInSet f set = 
    Set.foldr 
        (\x result -> 
            case result of
            Just _ -> result
            Nothing -> if f x then Just x else Nothing
            ) Nothing set

addOneToDS :: Ord a => a -> DisjointSet a -> DisjointSet a
addOneToDS x ds = 
    case _findFristInSet (Set.member x) ds of
        Just _ -> ds
        Nothing -> 
            Set.insert (Set.singleton x) ds

unionTwoInDS :: Ord a => a -> a -> DisjointSet a -> DisjointSet a
unionTwoInDS x y ds = 
    let xSet = _findFristInSet (Set.member x) ds in 
    let ySet = _findFristInSet (Set.member y) ds in 
        if (xSet == ySet) && (isJust xSet)
        then ds
        else 
            let (ds', newSet') = case xSet of 
                                Nothing -> (ds, Set.singleton x)
                                Just xSet -> ((Set.delete xSet ds), xSet)
            in
            let (ds'', newSet'') = case ySet of
                                Nothing -> (ds', Set.insert y newSet')
                                Just ySet -> ((Set.delete ySet ds'), Set.union newSet' ySet)
            in
                Set.insert newSet'' ds''

combineTwoDS :: Ord a => DisjointSet a -> DisjointSet a -> DisjointSet a
combineTwoDS ds1 ds2 =
    Set.foldr
        (\singleSet resultDs ->
            case Set.toList singleSet of
                [] -> resultDs -- can't be empty
                x:xs -> 
                    let resultDs' = addOneToDS x resultDs in
                    List.foldl (\ds y -> unionTwoInDS x y ds) resultDs' xs
            ) ds1 ds2 


removeOneFromDS :: Ord a => a -> DisjointSet a -> DisjointSet a
removeOneFromDS x ds = 
    case _findFristInSet (Set.member x) ds of 
        Nothing -> ds
        Just xSet -> 
            let xSet' = Set.delete x xSet in
            let ds' = Set.delete xSet ds in
                if Set.null xSet' 
                    then ds'
                    else  Set.insert xSet' ds'

removeFromDS :: Ord a => Set a -> DisjointSet a -> DisjointSet a
removeFromDS set ds = 
    filterDS (\x -> not $ Set.member x set) ds


connectedToOthersInDS :: Ord a => a -> DisjointSet a -> Bool
connectedToOthersInDS x ds =
    case _findFristInSet (Set.member x) ds of 
        Nothing -> False
        Just xSet -> Set.size xSet > 1

-- The map function must be a bijection, i.e. 1-to-1 mapping.
mapDS :: Ord a => (a -> a) -> DisjointSet a -> DisjointSet a
mapDS f ds = 
    Set.map (Set.map f) ds

filterDS :: Ord a => (a -> Bool) -> DisjointSet a -> DisjointSet a
filterDS f ds =
    Set.map (\x -> Set.filter f x) ds
    |> Set.filter (not . Set.null)


dsToTransitivePairs :: Ord a => DisjointSet a -> Set (a, a)
dsToTransitivePairs ds =
    Set.foldr
        (\singleSet result ->
            cartesianProduct singleSet singleSet
            |> Set.union result |> Set.filter (\(a, b) -> a < b)
            ) Set.empty ds

