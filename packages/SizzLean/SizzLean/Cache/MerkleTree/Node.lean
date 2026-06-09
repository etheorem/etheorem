/-!
# `SizzLean.Cache.MerkleTree.Node`: persistent binary Merkle tree node

ARCHITECTURE.md §6.1. A two-constructor inductive underpinning
the production fast-path for `hash_tree_root`:

```lean
inductive Node where
  | leaf : ByteArray → Node                            -- 32 bytes
  | pair : Node → Node → Option ByteArray → Node       -- left, right, cached root
```

The cache slot on `pair` is the only mutable-feeling state in the
data structure: cleared by `setAt` along the updated spine, filled
by `merkleRootWithCache` on first walk. `Node` itself stays purely
functional, sharing comes from Lean's reference-counting runtime
(off-path subtrees survive `setAt` by value-equality).

## Why a separate Tree layer at all

`Spec/HashTreeRoot.lean` is the verified reference: total,
parametric over `[Hasher H]`, validated against 38991 upstream
test vectors. It is also *slow*. Every `hash_tree_root` call
re-runs the
entire spec recursion. Production beacon-chain code mutates `BeaconState`
slot-by-slot; recomputing every root from scratch would burn a sizeable
fraction of slot time on hashing.

The Tree layer is the cache. Each `pair` node remembers its root; an
incremental `setAt` only invalidates the spine, leaving the rest of
the tree's roots intact. The contract, that the cached root equals
the spec root, is the load-bearing property tested by the
`TreeBackedCoherence` and `TreeBackedSetField` gates.

## Lean idioms used here

* `inductive` with two constructors of different arity. Lean infers
  the eliminator and structural-recursion principle automatically.
* `Option ByteArray` on `pair`'s third field rather than a separate
  `cached`/`uncached` distinction in the type. Keeps the inductive
  small and lets us pattern-match `some r` / `none` cleanly in
  `merkleRootWithCache`.

## Where `Node.ofLeaves` lives

`ofLeaves` builds a balanced binary tree to a target depth, padding
the right with `zeroLeaf` subtrees as needed, mirroring the spec's
`merkleize`'s padding semantics. It depends on `ZERO_HASHES` /
`zeroLeaf`, so the constructor lives in `Tree/Zero.lean` next to
those definitions; this file declares only the inductive itself
plus the cache accessor.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

/-- A persistent binary Merkle-tree node. Leaves carry their
32-byte value directly; pairs carry left and right children plus
an optional cached root (filled on first walk by
`merkleRootWithCache`, cleared along the spine by `setAt`).

Construction-time deferral (so the per-value tree-shape work
doesn't run until a root walk needs it) is handled *outside*
this type, by wrapping a `Node` in `Thunk Node` at the
`TreeBacked.treeBase` field. Lean's `Thunk` provides exactly the
"compute once, memoise" semantics the cache wants, and keeps the
`Node` ADT pure leaf/pair without an extra constructor for
deferred subtree builders. -/
inductive Node where
  /-- A 32-byte leaf. Carries the leaf bytes verbatim; the "cache"
  is the leaf value itself. -/
  | leaf : ByteArray → Node
  /-- An interior node. `left` and `right` are the two children;
  the third slot is the cached root if previously computed, `none`
  otherwise. -/
  | pair : Node → Node → Option ByteArray → Node
  deriving Inhabited

/-- The cached root of `n`, if known. For `leaf`s, the leaf bytes
*are* the root (always known). For `pair`s, the cached root is
populated by `merkleRootWithCache` on its first walk and cleared by
`setAt` along the updated spine.

This is the only public observer that distinguishes "we have a root"
from "we'd have to recompute it", useful for instrumentation and
for `merkleRootWithCache`'s short-circuit. -/
def Node.cached : Node → Option ByteArray
  | .leaf b      => some b
  | .pair _ _ c  => c

end SizzLean.Cache.MerkleTree
