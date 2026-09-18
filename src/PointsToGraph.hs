--  File     : PointsToGraph.hs
--  Author   : Saumitra Lohokare
--  Purpose  : Field- and direction-sensitive Points-To Graph (Andersen-style)
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  This module defines the intraprocedural Points-To Graph (PTG) that replaces
--  the Steensgaard/union-find alias representation.
--
--  MILESTONE 1 (scaffold): this module provides the data types and the pure
--  graph operations only.  It is deliberately NOT wired into AliasAnalysis /
--  Transform / AST yet -- that is Milestone 2 onwards.  The types and helpers
--  here are the building blocks the transfer function and queries will compose.
--
--  NOTE on FieldKey / EscapeState: for this scaffold they live here.  In
--  Milestone 3 (when the serialized interprocedural summary ProcPTGSummary is
--  introduced in AST.hs) FieldKey and EscapeState move to AST.hs and this
--  module imports them, because AST.hs cannot import PointsToGraph (PointsToGraph
--  imports AST) without an import cycle.

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module PointsToGraph (
    -- * Core types
    NodeOrigin(..), Node(..), FieldKey(..), EscapeState(..), PointsToGraph(..),
    -- * Construction / lookup
    emptyPTG, varNodes, setVarNodes, addVarNodes, dropVars,
    freshLocalNode, nodeOrigin, seedParam, addMaybeAliasParam,
    seedAliasedParam, seedOwnedParam,
    -- * Directional copy (Andersen inclusion)
    copyVar,
    -- * Field edges (field-sensitive, with FieldAny fallback)
    keyOfOffset, readField, writeField, readFieldMat,
    -- * Escape
    joinEscape, escapeOf, raiseEscape, raiseEscapeReachable,
    -- * Origins / classification
    isExternalOrigin, rootParamOfOrigin, allNodes, externalNodes,
    -- * Reachability / queries support
    reachableNodes, originsOf, varsReferencing,
    -- * Queries (reachability-based, replacing the DisjointSet queries)
    queryUnaliased, queryEscaped,
    -- * Summary projection
    paramAliasPairs,
    -- * Merge (fork / call combine)
    joinPTG
    ) where

import           AST         (PrimVarName, GlobalInfo, StructID,
                              FieldKey(..), EscapeState(..))
import qualified Data.List    as List
import           Data.Map    (Map)
import qualified Data.Map    as Map
import           Data.Maybe   (isNothing)
import qualified Data.Maybe   as Maybe
import           Data.Set    (Set)
import qualified Data.Set    as Set
import           Flow        ((|>))
import           GHC.Generics (Generic)


-- | Origin and identity of an abstract memory node.  The origin drives escape
-- classification: LocalNode is a candidate to be captured (stack-allocatable),
-- while ParamNode/ReturnNode/GlobalNode are visible outside the procedure.
-- Note (Phase A): ParamNode/ReturnNode and ptgMaybeAliasParams are keyed by the
-- param's SSA variable name, not its ParameterID.  Phase A keeps the serialized
-- summary as the name-based @AliasMap@ (@DisjointSet PrimVarName@), so the queries
-- return names directly and need no proto.  Phase C (deferred) migrates node
-- identity to ParameterID for the portable @ProcPTGSummary@.
data NodeOrigin
    = LocalNode  PrimVarName   -- ^ born at an `lpvm alloc`, keyed by its SSA out-var
    | ParamNode  PrimVarName   -- ^ external node reachable from a formal parameter
    | ReturnNode PrimVarName   -- ^ external node written to an output parameter
    | GlobalNode GlobalInfo    -- ^ a resource / global sink (always escaping)
    | ConstNode  StructID      -- ^ a constant memory block (ArgConstRef)
    | PhantomNode NodeOrigin FieldKey
        -- ^ a materialized successor of an external node's pointer field: the
        -- unknown external memory that (external-origin).f may point to.  Keyed
        -- canonically by its base origin and the field, so re-reading the same
        -- (node, field) yields the same phantom (bounded per proc).  See TODO 8.
    deriving (Eq, Ord, Show, Generic)


-- | An abstract memory node.  A newtype over its origin so that node identity is
-- exactly its origin (allocation-site abstraction: one node per alloc site /
-- param / return / global / const).
newtype Node = Node NodeOrigin
    deriving (Eq, Ord, Show, Generic)


-- 'FieldKey' and 'EscapeState' now live in "AST" (so the serialized
-- 'ProcPTGSummary' can reference them without an import cycle) and are
-- re-exported here for the intraprocedural code that used to find them local.


-- | The intraprocedural Points-To Graph.
--
--   * 'ptgEnv'    maps each variable to the set of nodes it may point to.
--   * 'ptgEdges'  maps each (node, field) to the set of nodes that field may
--                 point to -- the (node, field-offset) key IS the field
--                 sensitivity.
--   * 'ptgEscape' records the escape state of each node (absent = 'NoEscape').
--   * 'ptgMaybeAliasParams' are the parameters whose external aliasing is still
--                 unknown; they are the source of the `requiredParams` that
--                 `isArgUnaliased` reports (feeding multi-specialization).
data PointsToGraph = PointsToGraph
    { ptgEnv              :: Map PrimVarName (Set Node)
    , ptgEdges            :: Map Node (Map FieldKey (Set Node))
    , ptgEscape           :: Map Node EscapeState
    , ptgMaybeAliasParams :: Set PrimVarName
    } deriving (Eq, Ord, Show, Generic)


----------------------------------------------------------------
-- Construction / lookup
----------------------------------------------------------------

-- | The empty graph.
emptyPTG :: PointsToGraph
emptyPTG = PointsToGraph Map.empty Map.empty Map.empty Set.empty


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
-- retained -- they are the persistent aliasing substrate -- only the var->node
-- bindings go.  Mirrors the old `removeDeadVar`.
dropVars :: Set PrimVarName -> PointsToGraph -> PointsToGraph
dropVars vs ptg =
    ptg { ptgEnv = Map.filterWithKey (\v _ -> not (Set.member v vs)) (ptgEnv ptg) }


-- | Create a fresh 'LocalNode' for an `lpvm alloc` output variable: bind the
-- variable to the new node (replacing any prior binding, since SSA guarantees a
-- single definition), give the node an empty field map and 'NoEscape'.  Returns
-- the node and the updated graph.
freshLocalNode :: PrimVarName -> PointsToGraph -> (Node, PointsToGraph)
freshLocalNode out ptg =
    let n    = Node (LocalNode out)
        ptg' = ptg { ptgEnv    = Map.insert out (Set.singleton n) (ptgEnv ptg)
                   , ptgEdges  = Map.insertWith (\_ old -> old) n Map.empty
                                     (ptgEdges ptg)
                   , ptgEscape = Map.insertWith (\_ old -> old) n NoEscape
                                     (ptgEscape ptg) }
    in (n, ptg')


-- | Unwrap a node to its origin.
nodeOrigin :: Node -> NodeOrigin
nodeOrigin (Node o) = o


-- | Seed a formal parameter at proc entry: bind its variable to its 'ParamNode'
-- and record the parameter as "maybe aliased" (its external aliasing is unknown
-- until proven otherwise -- the source of the `requiredParams` that
-- 'queryUnaliased' reports).  Mirrors the old
-- @unionTwoInDS (LiveVar p) (MaybeAliasByParam p)@ seeding.
seedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedParam name ptg =
    setVarNodes name (Set.singleton (Node (ParamNode name)))
        (addMaybeAliasParam name ptg)


-- | Record a parameter as still "maybe aliased".
addMaybeAliasParam :: PrimVarName -> PointsToGraph -> PointsToGraph
addMaybeAliasParam name ptg =
    ptg { ptgMaybeAliasParams = Set.insert name (ptgMaybeAliasParams ptg) }


-- | Seed a *definitely* aliased parameter (used at transform time, once the
-- specialization has fixed which params are aliased): a 'ParamNode' that is NOT
-- a maybe-alias param, so the queries report it unconditionally aliased -- the
-- analogue of the old @AliasByParam@.
seedAliasedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedAliasedParam name =
    setVarNodes name (Set.singleton (Node (ParamNode name)))


-- | Seed a proven-unaliased ("owned") parameter (transform time): a fresh local
-- node, so the parameter root is unaliased (destructively updatable) while reads
-- of its unknown fields stay conservatively aliased to it (the 'readFieldMat'
-- local fallback).  This mirrors the old transform seeding, which added nothing
-- for a non-aliased param.
seedOwnedParam :: PrimVarName -> PointsToGraph -> PointsToGraph
seedOwnedParam name = snd . freshLocalNode name


----------------------------------------------------------------
-- Directional copy (Andersen inclusion)
----------------------------------------------------------------

-- | Andersen copy for a value-preserving assignment `dst = src`:
-- @pts(dst) ⊇ pts(src)@.  Direction-sensitive: @src@ does not acquire @dst@'s
-- other pointees.  Used for `llvm move` and `lpvm cast`.
copyVar :: PrimVarName -> PrimVarName -> PointsToGraph -> PointsToGraph
copyVar dst src ptg = addVarNodes dst (varNodes ptg src) ptg


----------------------------------------------------------------
-- Field edges
----------------------------------------------------------------

-- | Turn a (maybe-constant) byte offset into a 'FieldKey'.  A known constant
-- offset becomes 'Field'; anything else becomes 'FieldAny'.
keyOfOffset :: Maybe Int -> FieldKey
keyOfOffset (Just k) = Field k
keyOfOffset Nothing  = FieldAny


-- | Read a field of a node.  Returns the field's own pointees unioned with the
-- 'FieldAny' bucket (an earlier unknown-offset write may have landed there);
-- and, when reading through 'FieldAny', the union over ALL of the node's field
-- buckets.  This is the sound gather semantics for the field-insensitive
-- fallback (Balatsouras-Smaragdakis generalization order).
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
                -- 'FieldIdent' is a summary-only identity edge, never written into
                -- a local graph; store it in its own bucket for totality.
                FieldIdent ->
                    Map.insertWith Set.union key ns fields
        in ptg { ptgEdges = Map.insert n fields' (ptgEdges ptg) }


-- | Read a *pointer* field, supplying a conservative result when the field has
-- no recorded contents.  A field with no edge is *unknown*, not empty, and must
-- not read as "points nowhere" -- that would make a sub-cell of a live structure
-- look unaliased and get updated in place (silent corruption).  The old
-- union-find got this for free by merging the read result into the struct's
-- equivalence class; the field-sensitive graph records an edge instead, so this
-- must re-derive the same conservatism:
--
--   * base is external (param/return/global/const/phantom): materialize a
--     canonical 'PhantomNode' for @(origin, key)@ (TODO 8), record the edge, and
--     return it -- the read result is external / maybe-aliased.
--   * base is external (param/return/global/const/phantom): materialize a
--     canonical 'PhantomNode' for @(origin, key)@ (TODO 8), record the edge, and
--     return it -- the read result is external / maybe-aliased.
--   * base is a local node with an unknown field: fall back to the base node
--     itself, so the read result stays aliased to the structure it came from
--     (and becomes unaliased only once that structure dies) -- exactly the old
--     union-find member~struct connection.
--
-- When the field *is* recorded (e.g. a structure we built with `mutate`), the
-- precise contents are returned -- the field-sensitivity gain.  Callers must
-- only use this for pointer-typed fields; non-pointer reads carry no edges.
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
-- Escape
----------------------------------------------------------------

-- | Lattice join of two escape states (the more-escaping wins).
joinEscape :: EscapeState -> EscapeState -> EscapeState
joinEscape = max


-- | The escape state of a node (absent = 'NoEscape').
escapeOf :: PointsToGraph -> Node -> EscapeState
escapeOf ptg n = Map.findWithDefault NoEscape n (ptgEscape ptg)


-- | Raise the escape state of a set of nodes to at least the given state.
raiseEscape :: EscapeState -> Set Node -> PointsToGraph -> PointsToGraph
raiseEscape st ns ptg =
    ptg { ptgEscape =
            Set.foldr (\n -> Map.insertWith joinEscape n st) (ptgEscape ptg) ns }


-- | Raise the escape state of a set of nodes AND every node forward-reachable
-- from them (through 'ptgEdges').  This is what a global store / opaque-call
-- argument does: the escape taints everything reachable.
raiseEscapeReachable :: EscapeState -> Set Node -> PointsToGraph -> PointsToGraph
raiseEscapeReachable st ns ptg = raiseEscape st (reachableNodes ptg ns) ptg


----------------------------------------------------------------
-- Origins / classification
----------------------------------------------------------------

-- | Is this origin visible outside the procedure?  Every origin except a
-- 'LocalNode' is external: params/returns cross the call boundary, globals and
-- consts are shared sinks, and a 'PhantomNode' stands in for unknown external
-- memory.  External nodes drive the conservative side of the queries.
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
-- targets, escape keys).
allNodes :: PointsToGraph -> Set Node
allNodes ptg = Set.unions
    [ Set.unions (Map.elems (ptgEnv ptg))
    , Map.keysSet (ptgEdges ptg)
    , Set.unions (concatMap Map.elems (Map.elems (ptgEdges ptg)))
    , Map.keysSet (ptgEscape ptg) ]


-- | Every external node present in the graph, regardless of whether a variable
-- currently binds it.  These are always potential co-reference roots (a value
-- stored into a global may be reachable only through the global's edges, not
-- through any live variable -- see TODO 1).
externalNodes :: PointsToGraph -> Set Node
externalNodes = Set.filter (isExternalOrigin . nodeOrigin) . allNodes


----------------------------------------------------------------
-- Queries (reachability-based -- replacing the DisjointSet queries)
----------------------------------------------------------------

-- | Reachability-based aliasing query (TODO 1), the correctness fulcrum for
-- destructive mutate and dead-cell reuse.  This re-derives what the old
-- union-find had implicitly: its class was the *undirected* connected component,
-- so a value was aliased both by what points into it AND by what it transitively
-- contains.  The field-sensitive graph records directed edges, so both
-- directions must be walked:
--
--   * Forward (what @v@ contains): every node forward-reachable from @v@.  A
--     contained constant/global/return node, an already-aliased param, or a
--     phantom rooted at any of those means @v@'s structure embeds shared/external
--     memory -> aliased.  Contained *owned* local nodes are fine (they are @v@'s
--     own cells).  A contained maybe-alias param contributes a `requiredParam`.
--     (Missing this direction let a freshly-built structure that embeds a shared
--     constant read as unaliased, so a destructive spec clobbered the constant.)
--   * Co-reference (what points into @v@): @v@'s own nodes that are also
--     reachable from another live variable or an external sink are shared -> a
--     shared local means aliased; a maybe-alias param that reaches them
--     contributes a `requiredParam`.
--
-- @'Just' ps@ means unaliased provided the params @ps@ are non-aliased (feeds
-- multi-spec); @'Nothing'@ means unconditionally aliased.
queryUnaliased :: PointsToGraph -> PrimVarName -> Maybe [PrimVarName]
queryUnaliased ptg v =
    let vNodes     = varNodes ptg v
        otherRoots = Map.foldrWithKey
                        (\u ns acc -> if u == v then acc else Set.union ns acc)
                        Set.empty (ptgEnv ptg)
        -- Two kinds of co-reference must be told apart (the old union-find
        -- conflated them, and so did an earlier version of this query):
        --   * Internal: one of @v@'s nodes is reachable from ANOTHER live
        --     variable.  That variable is a concrete, live co-referent (e.g.
        --     `?out = param` binds @out@ to the param's own node), so a
        --     destructive reuse of @v@ would clobber it.  This is unconditional
        --     aliasing -- it must NOT be attributed to a parameter just because
        --     the shared node happens to be that param's node, since the sharer's
        --     liveness, not the param's entry-aliasing, is what blocks reuse.
        --     Mirrors the old analysis blocking on any `LiveVar` in @v@'s class.
        --   * External: one of @v@'s nodes is reachable from an external sink
        --     (param/return/global/const seeding).  This is conditional on the
        --     maybe-alias param(s) it roots at -> a `requiredParam`.
        exts       = externalNodes ptg
        -- What @v@ forward-reaches (embeds): its own cells plus everything they
        -- transitively contain.  A destructive operation on @v@ may recurse into
        -- this embedded memory (e.g. printing a `slice(base,range)` string
        -- iterates -- and destructively consumes -- the embedded range), so it
        -- must be treated as aliasing exactly as the co-reference direction is.
        -- The old union-find got this for free (embedding was a union); the
        -- field-sensitive graph records a directed edge, so BOTH directions must
        -- be walked (points_to_graph.md TODO 1, the query's own doc comment).
        fReach     = reachableNodes ptg vNodes
        -- Co-reference (something points INTO v) + forward (v embeds something):
        --   * internal: shared with another *live* variable -> unconditional.
        --   * external: reaches / reached-from an external sink -> conditional
        --     on the maybe-alias param(s) it roots at.
        internalContam = Set.union
            (Set.intersection vNodes (reachableNodes ptg otherRoots))
            (Set.intersection fReach otherRoots)
        externalContam = Set.union
            (Set.intersection vNodes (reachableNodes ptg exts))
            (Set.intersection fReach exts)
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
-- sink) or has been tainted to escape (global store / opaque call).  Constants
-- and non-variables are conservatively escaped, matching the old contract.
--
-- This may only *add* escapes relative to reality (it sits in an @||@ with the
-- authoritative mutation-chain check in Transform.hs), so it cannot make an
-- alloc unsoundly stack-allocatable.
queryEscaped :: PointsToGraph -> PrimVarName -> Bool
queryEscaped ptg v =
    let reach = reachableNodes ptg (varNodes ptg v)
    in any (isExternalOrigin . nodeOrigin) reach
        || any (\n -> escapeOf ptg n >= ArgEscape) (Set.toList reach)


----------------------------------------------------------------
-- Summary projection
----------------------------------------------------------------

-- | Project the final graph onto parameter aliasing: the pairs of maybe-aliased
-- parameters whose reachable node sets intersect.  Two params alias iff the
-- body linked them (embedded one in the other's field, or aliased them to a
-- common node); merely reading both never links them (distinct param nodes and
-- distinct phantom subtrees).  This is the coarse, field-insensitive summary
-- the old union-find recorded (@AliasMap@), so keeping it preserves the callee
-- interface while the *local* analysis gains field/direction sensitivity.
paramAliasPairs :: PointsToGraph -> Set (PrimVarName, PrimVarName)
paramAliasPairs ptg =
    let params = Set.toList (ptgMaybeAliasParams ptg)
        -- A param's memory is what its variable currently points to (which
        -- captures copies/moves recorded in the environment, e.g. `?out = in`
        -- gives out's binding the input's node) together with its own param
        -- node (in case the variable was dropped as dead).  Two params alias
        -- iff the memory reachable from their bindings overlaps -- catching both
        -- environment-level aliasing (copy) and edge-level aliasing (embedding).
        rootsOf p = Set.insert (Node (ParamNode p)) (varNodes ptg p)
        reachOf p = reachableNodes ptg (rootsOf p)
        reaches   = [ (p, reachOf p) | p <- params ]
    in Set.fromList
        [ (p, q)
        | ((p, rp) : rest) <- List.tails reaches
        , (q, rq) <- rest
        , not (Set.null (Set.intersection rp rq)) ]


----------------------------------------------------------------
-- Reachability / query support
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


-- | The origins of a set of nodes.
originsOf :: Set Node -> Set NodeOrigin
originsOf = Set.map nodeOrigin


-- | The variables whose points-to set intersects the given node set -- i.e. the
-- variables that (may) refer to any of those nodes.  Used by the alias queries
-- to find what a value is co-referenced with.
varsReferencing :: PointsToGraph -> Set Node -> Set PrimVarName
varsReferencing ptg ns =
    ptgEnv ptg
    |> Map.filter (not . Set.null . Set.intersection ns)
    |> Map.keysSet


----------------------------------------------------------------
-- Merge
----------------------------------------------------------------

-- | Merge two graphs (least upper bound), used to combine fork branches and to
-- fold in a callee summary's effect.  Environments and edges are unioned
-- pointwise; escape states are joined with 'max'; maybe-alias params are unioned.
joinPTG :: PointsToGraph -> PointsToGraph -> PointsToGraph
joinPTG a b = PointsToGraph
    { ptgEnv    = Map.unionWith Set.union (ptgEnv a) (ptgEnv b)
    , ptgEdges  = Map.unionWith (Map.unionWith Set.union)
                                (ptgEdges a) (ptgEdges b)
    , ptgEscape = Map.unionWith joinEscape (ptgEscape a) (ptgEscape b)
    , ptgMaybeAliasParams =
        Set.union (ptgMaybeAliasParams a) (ptgMaybeAliasParams b)
    }
