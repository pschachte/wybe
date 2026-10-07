--  File     : PointsToGraph.hs
--  Author   : Saumitra Lohokare
--  Purpose  : Field- and direction-sensitive Points-To Graph (Andersen-style)
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  This module defines the intraprocedural Points-To Graph (PTG) used by the
--  alias analysis, replacing the old Steensgaard/union-find alias
--  representation.  It provides the graph data types and the pure graph
--  operations -- construction, field edges, reachability queries, and the
--  fork/call merge -- that the transfer function in "AliasAnalysis" composes.
--
--  'FieldKey' is defined in "AST" (so the serialized interprocedural summary
--  'ProcPTGSummary' can reference it without an import cycle -- PointsToGraph
--  imports AST) and re-exported here.

{-# LANGUAGE DeriveGeneric #-}

module PointsToGraph (
    -- * Core types
    NodeOrigin(..), Node(..), FieldKey(..), PointsToGraph(..),
    -- * Construction / lookup
    emptyPTG, varNodes, setVarNodes, addVarNodes, dropVars,
    freshLocalNode, nodeOrigin, seedParam, addMaybeAliasParam,
    seedAliasedParam, seedOwnedParam,
    -- * Field edges (field-sensitive, with FieldAny fallback)
    keyOfOffset, readField, writeField, readFieldMat,
    -- * Origins / classification
    isExternalOrigin, rootParamOfOrigin, allNodes, externalNodes,
    -- * Reachability support
    reachableNodes,
    -- * Queries (reachability-based, replacing the DisjointSet queries)
    queryUnaliased, queryEscaped,
    -- * Merge (fork / call combine)
    joinPTG
    ) where

import           AST         (PrimVarName, GlobalInfo, StructID, FieldKey(..))
import qualified Data.List    as List
import           Data.Map    (Map)
import qualified Data.Map    as Map
import           Data.Maybe   (isNothing)
import qualified Data.Maybe   as Maybe
import           Data.Set    (Set)
import qualified Data.Set    as Set
import           Flow        ((|>))
import           GHC.Generics (Generic)


-- | Origin and identity of an abstract memory node.  The origin classifies a
-- node as local or external: a LocalNode is private to the procedure,
-- while ParamNode/ReturnNode/GlobalNode are visible outside it and so
-- drive the conservative side of the aliasing queries.
data NodeOrigin
    = LocalNode  PrimVarName   -- ^ born at an `lpvm alloc`, keyed by its SSA out-var
    | ParamNode  PrimVarName   -- ^ external node reachable from a formal parameter
    | ReturnNode PrimVarName   -- ^ external node written to an output parameter
    | GlobalNode GlobalInfo    -- ^ a resource / global sink
    | ConstNode  StructID      -- ^ a constant memory block (ArgConstRef)
    | PhantomNode NodeOrigin FieldKey
        -- ^ stand-in for the unknown memory a field of an external node points
        -- to (keyed by base origin + field, so the same (node, field) always
        -- yields the same phantom -- bounding their number per proc).
    deriving (Eq, Ord, Show, Generic)


-- | An abstract memory node, identified by its origin: all the cells born at one
-- site (an alloc, param, return, global, or const) collapse to a single node
-- (allocation-site abstraction), keeping the node set finite.
newtype Node = Node NodeOrigin
    deriving (Eq, Ord, Show, Generic)


-- | The intraprocedural Points-To Graph.
--
--   * 'ptgEnv'    maps each variable to the set of nodes it may point to.
--   * 'ptgEdges'  maps each (node, field) to the set of nodes that field may
--                 point to (field sensitivity).
--   * 'ptgMaybeAliasParams' are parameters whose external aliasing is unknown;
--                 'isArgUnaliased' reports them as the `requiredParams` a caller
--                 must prove non-aliased to unlock a specialization.
data PointsToGraph = PointsToGraph
    { ptgEnv              :: Map PrimVarName (Set Node)
    , ptgEdges            :: Map Node (Map FieldKey (Set Node))
    , ptgMaybeAliasParams :: Set PrimVarName
    } deriving (Eq, Ord, Show, Generic)


----------------------------------------------------------------
-- Construction / lookup
----------------------------------------------------------------

-- | The empty graph.
emptyPTG :: PointsToGraph
emptyPTG = PointsToGraph Map.empty Map.empty Set.empty


-- | The nodes a variable may point to (empty if unknown).
varNodes :: PointsToGraph -> PrimVarName -> Set Node
varNodes ptg v = Map.findWithDefault Set.empty v (ptgEnv ptg)


-- | Set a variable's points-to set, replacing any previous binding.
setVarNodes :: PrimVarName -> Set Node -> PointsToGraph -> PointsToGraph
setVarNodes v ns ptg = ptg { ptgEnv = Map.insert v ns (ptgEnv ptg) }


-- | Add nodes to a variable's points-to set (union with any existing binding).
addVarNodes :: PrimVarName -> Set Node -> PointsToGraph -> PointsToGraph
addVarNodes v ns ptg =
    ptg { ptgEnv = Map.insertWith Set.union v ns (ptgEnv ptg) }


-- | Remove a set of (dead) variables from the environment.  Nodes and edges are
-- retained only the var->node bindings go.
dropVars :: Set PrimVarName -> PointsToGraph -> PointsToGraph
dropVars vs ptg =
    ptg { ptgEnv = Map.filterWithKey (\v _ -> not (Set.member v vs)) (ptgEnv ptg) }


-- | Create a fresh 'LocalNode' for an `lpvm alloc` output variable.
-- Returns the node and the updated graph.
freshLocalNode :: PrimVarName -> PointsToGraph -> (Node, PointsToGraph)
freshLocalNode out ptg =
    let n    = Node (LocalNode out)
        ptg' = ptg { ptgEnv   = Map.insert out (Set.singleton n) (ptgEnv ptg)
                   , ptgEdges  = Map.insertWith (\_ old -> old) n Map.empty
                                     (ptgEdges ptg) }
    in (n, ptg')


-- | Unwrap a node to its origin.
nodeOrigin :: Node -> NodeOrigin
nodeOrigin (Node o) = o


-- | Seed a formal parameter at proc entry: bind its variable to its 'ParamNode'
-- and record the parameter as "maybe aliased"
seedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedParam name ptg =
    setVarNodes name (Set.singleton (Node (ParamNode name)))
        (addMaybeAliasParam name ptg)


-- | Record a parameter as still "maybe aliased".
addMaybeAliasParam :: PrimVarName -> PointsToGraph -> PointsToGraph
addMaybeAliasParam name ptg =
    ptg { ptgMaybeAliasParams = Set.insert name (ptgMaybeAliasParams ptg) }


-- | Seed a *definitely* aliased parameter (used at transform time, once the
-- specialization has fixed which params are aliased)
seedAliasedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedAliasedParam name =
    setVarNodes name (Set.singleton (Node (ParamNode name)))


-- | Seed a proven-unaliased ("owned") parameter (transform time)
seedOwnedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedOwnedParam name = snd . freshLocalNode name


----------------------------------------------------------------
-- Field edges
----------------------------------------------------------------

-- | Turn a (maybe-constant) byte offset into a 'FieldKey'.
keyOfOffset :: Maybe Int -> FieldKey
keyOfOffset (Just k) = Field k
keyOfOffset Nothing  = FieldAny


-- | Read a field of a node.  Returns the field's own pointees unioned with the
-- 'FieldAny' bucket (an earlier unknown-offset write may have landed there)
readField :: PointsToGraph -> Node -> FieldKey -> Set Node
readField ptg n key =
    let fields  = Map.findWithDefault Map.empty n (ptgEdges ptg)
        anyBkt  = Map.findWithDefault Set.empty FieldAny fields
    in case key of
        FieldAny   -> Map.foldr Set.union Set.empty fields
        Field _    -> Set.union (Map.findWithDefault Set.empty key fields) anyBkt
        -- 'FieldIdent' is a summary-only identity edge; a local graph never holds
        -- one, so a read just returns its (empty) bucket.
        FieldIdent -> Map.findWithDefault Set.empty key fields


-- | Write into a field of a node: @writeField n key S@ adds @S@ to the field's
-- pointees.  When writing through 'FieldAny', the values fan out into every
-- existing field bucket of the node AND the 'FieldAny' bucket, so a later read
-- of any specific field still sees them.
writeField :: Node -> FieldKey -> Set Node -> PointsToGraph -> PointsToGraph
writeField n key ns ptg
    | Set.null ns = ptg
    | otherwise   =
        let fields  = Map.findWithDefault Map.empty n (ptgEdges ptg)
            fields' = case key of
                FieldAny ->
                    -- fan out into all existing buckets + the FieldAny bucket
                    Map.insertWith Set.union FieldAny ns
                        (Map.map (Set.union ns) fields)
                Field _  ->
                    Map.insertWith Set.union key ns fields
                FieldIdent ->
                    Map.insertWith Set.union key ns fields
        in ptg { ptgEdges = Map.insert n fields' (ptgEdges ptg) }


-- | Read a pointer field.  A recorded field returns its precise contents; a
-- field with no edge is *unknown*, not empty, so it must not read as "points
-- nowhere" (that would make a sub-cell of a live structure look unaliased and
-- updatable in place).
--
-- Pointer-typed fields only; non-pointer reads carry no edges.
readFieldMat :: Node -> FieldKey -> PointsToGraph -> (Set Node, PointsToGraph)
readFieldMat n@(Node o) key ptg =
    let existing = readField ptg n key
    in if not (Set.null existing)
        then (existing, ptg)
        else if isExternalOrigin o
            then let ph  = Node (PhantomNode o key)
                     phs = Set.singleton ph
                 in (phs, writeField n key phs ptg)
            else (Set.singleton n, ptg)


----------------------------------------------------------------
-- Origins / classification
----------------------------------------------------------------

-- | Is this origin visible outside the procedure?
isExternalOrigin :: NodeOrigin -> Bool
isExternalOrigin LocalNode{}   = False
isExternalOrigin _             = True


-- | If this origin ultimately roots at a formal parameter (directly, or as a
-- phantom successor of one), return that parameter's id.  A phantom rooted at a
-- global/const/return has no such param.  Used to attribute a maybe-aliased
-- external contact to the parameter that must be non-aliased for a destructive
-- update (the `requiredParams` of 'queryUnaliased').
rootParamOfOrigin :: NodeOrigin -> Maybe PrimVarName
rootParamOfOrigin (ParamNode p)      = Just p
rootParamOfOrigin (PhantomNode o _)  = rootParamOfOrigin o
rootParamOfOrigin _                  = Nothing


-- | Every node mentioned anywhere in the graph (env targets, edge sources, edge
-- targets).
allNodes :: PointsToGraph -> Set Node
allNodes ptg = Set.unions
    [ Set.unions (Map.elems (ptgEnv ptg))
    , Map.keysSet (ptgEdges ptg)
    , Set.unions (concatMap Map.elems (Map.elems (ptgEdges ptg))) ]


-- | Every external node present in the graph, regardless of whether a variable
-- currently binds it.
externalNodes :: PointsToGraph -> Set Node
externalNodes = Set.filter (isExternalOrigin . nodeOrigin) . allNodes


----------------------------------------------------------------
-- Queries (reachability-based -- replacing the DisjointSet queries)
----------------------------------------------------------------

-- | Reachability-based aliasing query.  @v@ is aliased both by what points into it
-- and by what it transitively contains, so both directions of the directed graph are walked.
queryUnaliased :: PointsToGraph -> PrimVarName -> Maybe [PrimVarName]
queryUnaliased ptg v =
    let vNodes     = varNodes ptg v
        -- all other live variables' nodes
        otherRoots = Map.foldrWithKey
                        (\u ns acc -> if u == v then acc else Set.union ns acc)
                        Set.empty (ptgEnv ptg)
        -- all external sink nodes
        exts       = externalNodes ptg
        -- everything v embeds: its own cells plus what they transitively contain
        fReach     = reachableNodes ptg vNodes
        -- contamination in either direction (something points into v, or v embeds
        -- it): internal = shared with another live var; external = an external sink
        internalContam = Set.union
            (Set.intersection vNodes (reachableNodes ptg otherRoots))
            (Set.intersection fReach otherRoots)
        externalContam = Set.union
            (Set.intersection vNodes (reachableNodes ptg exts))
            (Set.intersection fReach exts)
        -- the maybe-alias param an external contaminant roots at, if any
        classify (Node o) = case rootParamOfOrigin o of
            Just p | p `Set.member` ptgMaybeAliasParams ptg -> Just p
            _                                               -> Nothing
    in if not (Set.null internalContam)
        then Nothing
        else if Set.null externalContam
            then Just []
            else let classified = List.map classify (Set.toList externalContam)
                 in if any isNothing classified
                        then Nothing
                        else Just (List.nub (Maybe.catMaybes classified))


-- | Escape query (the alloc-site @escapedByAlias@ check).  @v@ escapes if any
-- node reachable from it is external (crosses the proc boundary or is a shared
-- sink).  Constants and non-variables are conservatively escaped.
queryEscaped :: PointsToGraph -> PrimVarName -> Bool
queryEscaped ptg v =
    any (isExternalOrigin . nodeOrigin) (reachableNodes ptg (varNodes ptg v))


----------------------------------------------------------------
-- Reachability support
----------------------------------------------------------------

-- | The set of nodes forward-reachable from a set of roots, following every
-- field edge (field-sensitively -- all buckets).  Includes the roots.
reachableNodes :: PointsToGraph -> Set Node -> Set Node
reachableNodes ptg = go Set.empty
  where
    go seen frontier
        | Set.null frontier = seen
        | otherwise =
            let seen'    = Set.union seen frontier
                nexts    = frontier
                            |> Set.toList
                            |> concatMap successors
                            |> Set.fromList
                frontier' = Set.difference nexts seen'
            in go seen' frontier'
    successors n =
        Map.findWithDefault Map.empty n (ptgEdges ptg)
        |> Map.elems
        |> Set.unions
        |> Set.toList


----------------------------------------------------------------
-- Merge
----------------------------------------------------------------

-- | Merge two graphs (least upper bound), used to combine fork branches and to
-- fold in a callee summary's effect.  Environments and edges are unioned
-- pointwise; maybe-alias params are unioned.
joinPTG :: PointsToGraph -> PointsToGraph -> PointsToGraph
joinPTG a b = PointsToGraph
    { ptgEnv    = Map.unionWith Set.union (ptgEnv a) (ptgEnv b)
    , ptgEdges  = Map.unionWith (Map.unionWith Set.union)
                                (ptgEdges a) (ptgEdges b)
    , ptgMaybeAliasParams =
        Set.union (ptgMaybeAliasParams a) (ptgMaybeAliasParams b)
    }
