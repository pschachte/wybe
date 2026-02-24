# Escape Analysis and Stack Allocation Implementation Plan

To turn non-escaping heap allocations into stack allocations in the Wybe compiler, we essentially need to detect when the pointer returned by an `alloc` instruction is strictly confined to the lifetime of the currently executing procedure and doesn't "escape" via global state or output parameters. 

Here is the exact set of changes and the detailed descriptions of what needs to be implemented. 

## 1. [AliasAnalysis.hs](./src/AliasAnalysis.hs)

The compiler already does a bottom-up alias analysis pass over each module, calculating an `AliasMapLocal` (which is a Disjoint Set mapping variables to their aliases). The items placed into the disjoint set include:
- `LiveVar` (local variables)
- `AliasByParam` (which covers function return values / output arguments)
- `AliasByGlobal`
- `MaybeAliasByParam`
- `AliasByConstant`

When a variable **escapes**, it means its pointer is aliased to something external to the execution of the current procedure body. Therefore, an `alloc` result escapes if and only if its local `LiveVar` connects to an `AliasByParam`, `AliasByGlobal`, or `MaybeAliasByParam` inside the disjoint set mapping for that procedure.

**Change:** Expose a new helper function `isArgEscaped` that checks the elements of the disjoint subset a variable belongs to. Add this function near the existing `isArgUnaliased`.

```haskell
-- | Check if the argument is escaped. It returns True if it's aliased by something
-- outside the local scope, such as a global variable or an output parameter.
isArgEscaped :: AliasMapLocal -> PrimArg -> Bool
isArgEscaped aliasMap ArgVar{argVarName=varName} =
    let items = connectedItemsInDS (LiveVar varName) aliasMap |> Set.toList in
    any (\case
            AliasByGlobal _ -> True
            AliasByParam _ -> True
            MaybeAliasByParam _ -> True
            _ -> False
        ) items
isArgEscaped _ _ = True -- Constants/Globals are conservatively considered "escaped"
```

*Note: Be sure to export `isArgEscaped` in the module block at the top of [AliasAnalysis.hs](./src/AliasAnalysis.hs).*

## 2. [Transform.hs](./src/Transform.hs)

The `Transform` module is run after alias analysis. Currently, it already looks at `PrimForeign "lpvm" "alloc"` instructions and attempts to eliminate them if it can reuse a dead cell (`assignDeadCellsByAllocArgs`). 

If dead-cell reuse fails, we want to perform our Escape Analysis. If the allocation's result doesn't escape, AND its allocation size is a known compile-time constant, we can safely mutate the LPVM primitive to tell the LLVM backend to stack-allocate it.

**Change:** In `transformPrim`, update the mapping from the original `prim` down to the new `primc'`. If `assignDeadCellsByAllocArgs` produces `Nothing`, we fallback to checking if the struct allocation escapes. We can signal stack allocation to the backend by adding a `"stack"` flag to the instruction.

```haskell
            PrimForeign "lpvm" "alloc" flags args  -> do
                let (result, deadCells') =
                        assignDeadCellsByAllocArgs deadCells args
                let primc' = case result of
                        Nothing -> 
                            -- [Escape Analysis Check]
                            -- If we couldn't reuse a dead cell, check if the variable escapes.
                            -- We also require a constant size so we can use LLVM `alloca`.
                            let [sizeArg, outVar] = args in
                            if not (isArgEscaped aliasMap outVar) && argIsConst sizeArg
                            then PrimForeign "lpvm" "alloc" ("stack":flags) args
                            else primc
                        Just ((selectedCell, startOffset), []) ->
                            -- avoid "alloc" by reusing the "selectedCell".
                            let [_, varOut] = args in
                            PrimForeign "llvm" "sub" []
                                    [selectedCell, startOffset, varOut]
                        _ -> shouldnt "invalid aliasMap for transform"
                when (Maybe.isJust result) $
                        lift $ logTransform "avoid using [alloc]."
                return (primc', deadCells')
```

## 3. [LLVM.hs](./src/LLVM.hs)

In [LLVM.hs](./src/LLVM.hs), the compiler maps LPVM instructions down to LLVM IR. The module already contains a `stackAlloc :: PrimArg -> Int -> LLVM ()` helper function which writes `alloca i8, i64 <size>` and marks `doesAlloca = True` on the state (which is essential for disabling `musttail` recursion optimizations on functions with stack allocations).

**Change:** Update the `writeLPVMCall "alloc"` case to intercept the `"stack"` flag we added during the transformation pass. Extract the integer from the constant allocation size, and call `stackAlloc` instead of `heapAlloc`.

```haskell
writeLPVMCall "alloc" flags args pos = do
    releaseDeferredCall
    args' <- partitionArgs "lpvm alloc instruction" args
    case args' of
        ([sz],[out]) -> do
            if "stack" `elem` flags
            then case argIntVal sz of 
                -- We checked it was constant during Transform, so this should match
                Just sizeVal -> stackAlloc out (fromIntegral sizeVal)
                Nothing      -> shouldnt "stack alloc with non-constant size"
            else heapAlloc out sz pos
        _            -> shouldnt $ "lpvm alloc with arguments " ++ show args
```

## Summary of the Transformation

With these three small, localized changes:
1. Alias boundaries are accurately checked through pre-computed disjoint sets. 
2. Safely scoped heap allocations of a fixed size are flagged. 
3. The LLVM emitter replaces `wybe_malloc` with `alloca` for flagged variables. 

These changes will greatly reduce memory-management overhead on short-lived objects without breaking existing memory semantics.
