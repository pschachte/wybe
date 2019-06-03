--  File     : Util.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu May 22 14:43:47 2014
--  Purpose  : Various small utility functions
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--

{-# LANGUAGE DeriveGeneric #-}

module Util (sameLength, maybeNth, checkMaybe, setMapInsert,
             fillLines, nop, sccElts,
             UnionFind, UFInfo, unionFindToTransitivePairs,
             initUnionFind, newUfItem, uniteUf, transformUfKey,
             combineUf, removeFromUf, connectedToOthers,
             removeDupTuples, pruneTuples, transitiveTuples, cartProd) where


import           Data.Graph
import           Data.List    as List
import           Data.Map     as Map
import           Data.Set     as Set
import           GHC.Generics (Generic)


-- |Do the the two lists have the same length?
sameLength :: [a] -> [b] -> Bool
sameLength [] []         = True
sameLength (_:as) (_:bs) = sameLength as bs
sameLength _ _           = False


-- |Return the nth element of the list, if present, else Nothing.
maybeNth :: (Eq n, Ord n, Num n) => n -> [a] -> Maybe a
maybeNth _ []     = Nothing
maybeNth 0 (e:_ ) = Just e
maybeNth n (_:es)
 | n > 0          = maybeNth (n - 1) es
 | otherwise      = Nothing


-- |Test the value in a maybe, and if it fails, return Nothing.
checkMaybe :: (a -> Bool) -> Maybe a -> Maybe a
checkMaybe test Nothing    = Nothing
checkMaybe test (Just val) = if test val then Just val else Nothing


-- |Insert an element into the set mapped to by the specified key in
--  the given map.  Maps to a singleton set if there is no current
--  mapping for the specified key.
setMapInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
setMapInsert key item dict =
    Map.alter (\ms -> case ms of
                    Nothing -> Just $ Set.singleton item
                    Just s  -> Just $ Set.insert item s)
    key dict



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
-- UnionFind implementation by Map
--
----------------------------------------------------------------

type UnionFind a = Map a (UFInfo a)

data UFInfo a = UFInfo {
    root   :: a,
    weight :: Int
    } deriving (Eq, Generic)

instance Show a => Show (UFInfo a) where
    show (UFInfo root _) = show root


-- Convert UnionFind as transitive (key, root) tuples
unionFindToTransitivePairs :: (Ord a, Show a) => UnionFind a -> [(a,a)]
unionFindToTransitivePairs unionFind = removeDupTuples transIdxAPairs
    where
        f k info (aPairs, set) =
            let r = root info
                set' = Set.insert k set
            in if k == r then (aPairs, set')
                else ((k, r): aPairs, Set.insert r set')
        (aPairs, distinctA) = foldrWithKey f ([], Set.empty) unionFind
        (aToIdx, cumu, idxToA) =
            Set.foldr (\dis (map, cumulator, ls) ->
                if not $ Map.member dis map
                then (Map.insert dis cumulator map, cumulator + 1, ls ++ [dis])
                else (map, cumulator, ls)
                ) (Map.empty, 0, []) distinctA
        idxPairs =
            List.foldr (\(k, r) ls ->
                let kIdx = Map.lookup k aToIdx
                    rIdx = Map.lookup r aToIdx
                in case (kIdx, rIdx) of
                    (Just kid, Just rid) -> (kid, rid) : ls
                    _                    -> ls
                ) [] aPairs
        transIdxPairs =
            removeDupTuples $ transitiveTuples $ removeDupTuples idxPairs
        transIdxAPairs =
            List.foldr (\(idx1, idx2) ls ->
                (idxToA !! idx1, idxToA !! idx2) : ls
                ) [] transIdxPairs


initUnionFind :: UnionFind a
initUnionFind = Map.empty


-- Insert new item with default UFInfo if newK not exists in currUf
newUfItem :: Ord a => a -> UnionFind a -> UnionFind a
newUfItem newK currUf =
    let ufList = Map.toList currUf
        ufList' = [key | (key, info) <- ufList, key == newK || root info == newK]
    in if List.null ufList'
        then Map.insert newK (UFInfo newK 1) currUf
        else currUf


-- -- Check if two item is connected
-- connectedUf :: Ord a => UnionFind a -> a -> a -> Bool
-- connectedUf uf p q =
--     let infoP = Map.lookup p uf
--         infoQ = Map.lookup q uf
--     in case (infoP, infoQ) of
--         (Just ip, Just iq) -> root ip == root iq
--         (_, _)             -> False


-- Unite two nodes in the tree
-- e.g.
--  UnionFind {r: {root: b}, a: {root: a}, b: {root: b}},
--  p = a, q = r
uniteUf :: Ord a => UnionFind a -> a -> a -> UnionFind a
uniteUf uf p q =
    case (infoP, infoQ) of
        (Just ip, Just iq) ->
            -- if root is the same between two existing UFInfo then no need to
            -- update anything
            if root ip == root iq then uf
            else _updateUf p q ip iq uf
        (Just ip, Nothing) ->
            -- Insert q to the map
            let iq = ufInfo q
                uf1 = Map.insert q iq uf
            in _updateUf p q ip iq uf1
        (Nothing, Just iq) ->
            -- Insert p to the map
            let ip = ufInfo p
                uf1 = Map.insert p ip uf
            in _updateUf p q ip iq uf1
        (_, _) ->
            -- Insert both p and q to the map
            let ip = ufInfo p
                iq = ufInfo q
                uf1 = Map.insert p ip uf
                uf2 = Map.insert q iq uf1
            in _updateUf p q ip iq uf2
    where
        infoP = Map.lookup p uf
        infoQ = Map.lookup q uf

-- e.g.
--  UnionFind {r: {root: b}, a: {root: a}, b: {root: b}},
--  p = a, q = r,
--  ip = UFInfo{root: a, weight: 1},
--  iq = UFInfo{root: b, weight: 1}
-- TODO: Verify if this works for currMap(r,b) and p=a, q=b??
_updateUf :: Ord a => a -> a -> UFInfo a -> UFInfo a -> UnionFind a
                        -> UnionFind a
_updateUf p q ip iq currMap =
    let rp = root ip -- p=a, rp=a
        rq = root iq -- q=r, rq=b
        currRootP = Map.lookup rp currMap -- rootP=UFInfo{root: a, weight: 1}
        currRootQ = Map.lookup rq currMap -- rootQ=UFInfo{root: b, weight: 2}
    in case (currRootP, currRootQ) of
        (Just rootP, Just rootQ)
            | weight rootP <= weight rootQ ->
                let
                    -- update p's root to q's root
                    ip' = ip {root = rq}
                    -- append p's weight to q's root's weight
                    rootQ' = rootQ {weight = weight rootQ + weight ip}
                    currMap1 = Map.insert p ip' currMap
                    -- also make p's children point to new root (ip')
                    currMap2 = _updateRoot p ip' currMap1
                in Map.insert rq rootQ' currMap2
            | otherwise ->
                let
                    -- update q's root to p's root
                    iq' = iq {root = rp}
                    -- append q's weight to p's root's weight
                    rootP' = rootP {weight = weight rootP + weight iq}
                    currMap1 = Map.insert q iq' currMap
                    -- also make q's children point to new root (iq')
                    currMap2 = _updateRoot q iq' currMap1
                in Map.insert rp rootP' currMap2
        (_,_) -> currMap


-- Set default UFInfo that with root to itself and weight to 1
ufInfo :: a -> UFInfo a
ufInfo i = UFInfo i 1

-- Convert UnionFind map by mapping key with type 'a' to another value
transformUfKey :: (Ord a) => Map a a -> a -> UFInfo a -> UnionFind a
                        -> UnionFind a
transformUfKey mp k info uf =
    case Map.lookup k mp of
        Just y ->
            let rootX = root info
                rootY = Map.lookup rootX mp
            in case rootY of
                Just rootY ->
                    Map.insert y info{root = rootY} uf
                _ -> uf
        _        -> uf


-- Combine two UnionFind
-- e.g.
--  fromUf=UnionFind{b: UFInfo{root: c}, c: UFInfo{root: c}}
--  toUf=UnionFind{a: UFInfo{root: b}, b: UFInfo{root: b}}
combineUf :: Ord a => UnionFind a -> UnionFind a -> UnionFind a
combineUf fromUf toUf
    | Map.null fromUf = toUf
    | Map.null toUf = fromUf
    | otherwise =
        Map.foldrWithKey (
            \key newInfo currTo ->
                -- key=b, newInfo={root: c},
                -- currTo=UnionFind{a: UFInfo{root: b}, b: UFInfo{root: b}}
                let newRoot = root newInfo -- newRoot=c
                in uniteUf currTo key newRoot -- unite b and c in currTo map
            ) toUf fromUf


-- Helper: update root of nodes based on condition
_updateRoot cond newInfo =
    Map.foldrWithKey (\k i uf ->
        if root i == cond
        then Map.insert k newInfo uf
        else Map.insert k i uf
        ) Map.empty

-- -- Reset key and value in UnionFind to default (so it's not connected to anyone)
-- resetUf :: (Ord a) => UnionFind a -> a -> UnionFind a
-- resetUf uf k = Map.insert k (ufInfo k) uf


-- Check if item is connected to anyone else except itself
connectedToOthers :: (Eq a, Ord a) => UnionFind a -> a -> Bool
connectedToOthers uf val =
    let ufList = Map.toList uf
        ufList' = [(k, root info) | (k, info) <- ufList,
                    k /= root info, k == val || root info == val]
    in not (List.null ufList')


removeFromUf :: (Ord a) => Set a -> UnionFind a -> UnionFind a
removeFromUf toBeRemoved unionFind
    | Set.null toBeRemoved = unionFind
    | otherwise = unionFind3
        where
            -- In case the key is in toBeRemoved, we cleanup these keys as well
            (unionFind1, rootMap1) = Map.foldrWithKey (_convertUfKey toBeRemoved)
                                (initUnionFind, Map.empty) unionFind
            -- Cleanup root that is in toBeRemoved set and gather a mapping from
            -- the removed root to the new root
            (unionFind2, rootMap2) =
                Map.foldrWithKey (_convertUfRoot toBeRemoved)
                                (initUnionFind, rootMap1) unionFind1
            -- Now all variables in toBeRemoved would be converted to map to
            -- itself;
            -- So we'll need to remove them from the map
            unionFind3 = Map.foldrWithKey (_filterUfItems toBeRemoved)
                                initUnionFind unionFind2


-- convert UnionFind to a new UnionFind so if any root exists in the aSet then
--     its children would be moved to a newRoot; the newRoot is the first
--     occurrance of k whose root is in the aSet
-- aSet: the set containing items that to be filtered out
-- rootMap: map oldRoot to newRoot
_convertUfRoot :: (Ord a) => Set a -> a -> UFInfo a -> (UnionFind a, Map a a)
                        -> (UnionFind a, Map a a)
_convertUfRoot aSet k info (uf, rootMap) =
    if Set.member (root info) aSet then
        -- root needs to be modified
        if Map.member (root info) rootMap then
            -- can find mapping to newRoot
            let newRoot = Map.lookup (root info) rootMap
            in case newRoot of
                Just nr ->
                    let newInfo = info{ root = nr }
                    in (Map.insert k newInfo uf, rootMap)
                _ -> (Map.insert k info uf, rootMap)
        else
            -- cannot find mapping to newRoot
            let newRoot = k
                rootMap' = Map.insert (root info) newRoot rootMap
                newInfo = info{ root = newRoot }
                uf' = Map.insert k newInfo uf
            in
                if Set.member k aSet
                then (uf', rootMap) -- ^ only add this mapping if k is not in aSet
                else
                    let rootMap' = Map.insert (root info) newRoot rootMap
                    in (uf', rootMap')
    else (Map.insert k info uf, rootMap)

-- Similar to above - but converting key instead
_convertUfKey :: (Ord a) => Set a -> a -> UFInfo a -> (UnionFind a, Map a a)
                        -> (UnionFind a, Map a a)
_convertUfKey aSet k info (uf, rootMap) =
    if Set.member k aSet && k /= root info
        then (uf, rootMap)
        else (Map.insert k info uf, rootMap)
    -- if Set.member k aSet && Map.member k rootMap then
    --     -- can find mapping to newKey
    --     let newKey = Map.lookup k rootMap
    --     in case newKey of
    --         Just nk -> (Map.insert nk info uf, rootMap)
    --         _       -> (Map.insert k info uf, rootMap)
    -- else
    --     -- (uf, rootMap) -- ^TODO: Verify this!
    --     (Map.insert k info uf, rootMap)

-- Similar to above - but filtering out item that is in aSet and its key and
-- root are same
_filterUfItems :: (Ord a) => Set a -> a -> UFInfo a -> UnionFind a -> UnionFind a
_filterUfItems aSet k info uf =
    if Set.member k aSet && k == root info
    then uf
    else Map.insert k info uf
