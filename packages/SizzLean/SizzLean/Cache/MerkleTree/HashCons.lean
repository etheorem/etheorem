import Lean.Data.PersistentHashMap
import SizzLean.Cache.MerkleTree.Node

/-!
# `SizzLean.Cache.MerkleTree.HashCons`: bounded dedup for identical subtrees

A global per-process cache mapping 32-byte roots to the populated
`Node.pair` cell whose `merkleRoot` equals that root. When a second
tree construction produces a pair with the same root, the cache
returns the cell it already holds, and the fresh cell becomes
garbage. Lean's reference-counting runtime then makes the dedup
observable as shared structure across trees.

The win is inter-tree. Two `BeaconState`s that hold the same
validator-list prefix share one copy of that prefix once both
went through the cache. A single resident state gets no hits and
pays a hash-map lookup per interior cell, so the cache is off by
default. `SSZ.FastBox v (consing := true)` turns it on for one
box; see `Cache/TreeBacked.lean` for where the toggle applies.

## The shape rule

Same root does not mean same shape. SSZ merkleization equates a
container with the vector of its field roots: a `BeaconBlock` and
the `BeaconBlockHeader` that summarises it have the same root, but
the block's tree holds `body` as a subtree where the header holds
`body_root` as one leaf. Substituting the header's cell into the
block's tree would drop every later write that descends into
`body`, because `setAtBits` stops at a leaf.

So a cache hit is accepted only when `Node.shapeEq` holds between
the cached cell and the fresh one: leaf against leaf, pair against
pair, at every position. Equal roots then give equal leaf bytes
(collision resistance of the hasher, which the whole SSZ design
already assumes), so kinds are all that has to match. The check is
O(1) when the two cells' children are the same objects, which is
the common case once children were consed first, and it never
hashes.

## What the cache holds

* A global `IO.Ref`-backed `Lean.PersistentHashMap ByteArray Node`,
  bounded by `capacity` (default 4096). When an insertion would
  exceed the bound, the map is wiped and the new entry starts the
  next generation. Zero per-access bookkeeping; correctness does
  not depend on a hit.
* Hit and miss counters, for the multi-state bench and for tests
  that want to confirm the cache took part.

The map is persistent (path-copying) on purpose. The ref is
created by `initialize`, so the runtime treats it as shared
between threads and marks every value stored into it as shared
too. A `Std.HashMap` stored that way copies its whole bucket
array on each insert, which turned a cold fill into quadratic
work. `PersistentHashMap` is what the Lean compiler itself keeps
in its global refs for the same reason: an insert allocates one
short path and leaves the rest of the map untouched, whether or
not the map is shared.

The same marking applies to the cells the cache holds: once a
cell has been stored, the runtime counts its references
atomically. That is a small per-touch cost on consed trees and a
further reason the flag is off by default.

The default capacity is small on purpose. A cache that holds a
mainnet state has to be sized by the workload; call
`HashCons.setCapacity` before the first consing box is built.

## Two entry points

* `Node.consCell : Node → BaseIO Node` is the primitive. It looks
  up a pair cell by its cached root and returns the shape-equal
  cell the cache already holds, or inserts and returns the input.
  Cells without a cached root pass through untouched.
* `Node.consTree : Node → Node` walks a fresh tree and conses
  every pair cell, top-down with an early exit: a hit at a
  subtree's top returns the shared subtree without touching its
  interior. On a miss the children are consed first, then the
  rebuilt parent is inserted. `Node.consPair` is the one-cell
  form the fused commit walk uses for spine cells.

Both pure functions are `@[implemented_by]` wrappers over the
`BaseIO` primitive. The kernel sees the identity and the plain
`.pair` allocation; the compiled code consults the cache. This is
allowed because a substituted cell is observationally equal to the
fresh one: same root, same shape, same leaf bytes.

## Trust footprint

Four `@[implemented_by]` wrappers: `consCell`, `consTree`,
`consPair`, and the diagnostic `HashCons.statsSnapshot`, the
last three running `unsafeBaseIO`. No axiom. The
`SizzLeanTests/HashConsCoherence.lean` gates check the root
against the spec oracle with consing on, and check the shape rule
on the block-versus-header case above.

## Out of scope

Weak references. Lean 4 has no weak-ref API, so the bounded map
with wipe-all eviction stays. If a workload later justifies weak
refs, the swap is local to this file.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

/-- Maximum number of entries in the global hash-cons cache.
Bounds resident size at a few hundred KB per process (each entry
is a 32-byte key, one `Node` pointer, and hash-map overhead). A
workload that keeps whole states resident should raise it with
`HashCons.setCapacity` before any cache traffic begins. -/
def HashCons.defaultCapacity : Nat := 4096

/-- Mutable state for the hash-cons cache: the map, its entry
count (the persistent map does not track one), the capacity
bound, and the hit / miss counters. -/
structure HashConsState where
  cache    : Lean.PersistentHashMap ByteArray Node
  count    : Nat
  capacity : Nat
  hits     : Nat
  misses   : Nat
  deriving Inhabited

private def hashConsInitial : HashConsState :=
  { cache := {}, count := 0, capacity := HashCons.defaultCapacity,
    hits := 0, misses := 0 }

initialize hashConsRef : IO.Ref HashConsState ← IO.mkRef hashConsInitial

/-- Reset the cache to empty and zero the counters, keeping the
capacity. Call at the start of a benchmark or test for a
consistent measurement. -/
def HashCons.clear : BaseIO Unit := do
  hashConsRef.modify fun s =>
    { s with cache := {}, count := 0, hits := 0, misses := 0 }

/-- Set the capacity. Wipes existing entries so the new bound
holds. Capacity 0 disables the cache: every cell passes through
as a miss and nothing is stored. -/
def HashCons.setCapacity (n : Nat) : BaseIO Unit := do
  hashConsRef.modify fun s => { s with cache := {}, count := 0, capacity := n }

/-- Current entry count, for diagnostics and bench reporting. -/
def HashCons.size : BaseIO Nat := do
  return (← hashConsRef.get).count

/-- Hit and miss counts since the last `clear`. A hit is a lookup
that returned a shape-equal cached cell; every other lookup is a
miss, including a same-root cell the shape rule rejected. -/
def HashCons.stats : BaseIO (Nat × Nat) := do
  let s ← hashConsRef.get
  return (s.hits, s.misses)

/-- Pure snapshot of `HashCons.stats`, for gates that run under
`native_decide` and cannot sequence `BaseIO`. Returns
`(tag, hits, misses)`. The tag is echoed on purpose: it makes the
`BaseIO` action depend on the argument, so the compiler cannot
extract `unsafeBaseIO` of a closed action into a constant that is
evaluated once. Threading a value from the step under test into
`tag` also fixes the order two snapshots are taken in. -/
unsafe def HashCons.statsSnapshotImpl (tag : Nat) : Nat × Nat × Nat :=
  unsafeBaseIO do
    let s ← hashConsRef.get
    return (tag, s.hits, s.misses)

/-- See `statsSnapshotImpl`. The kernel sees `(tag, 0, 0)`. -/
@[implemented_by HashCons.statsSnapshotImpl]
def HashCons.statsSnapshot (tag : Nat) : Nat × Nat × Nat := (tag, 0, 0)

/-- Shape equality with a pointer short-circuit. Two cells are
shape-equal when they are the same object, or both leaves, or
both pairs with shape-equal children. Leaf bytes are not compared:
the caller only asks this of two cells with equal roots, where
equal roots already give equal leaf bytes at every position.

`ptrEq` is Lean core's unsafe pointer comparison. The short-circuit
is what keeps a hit O(1) once the children were consed first: they
are then the same objects and the walk stops at once. -/
unsafe def Node.shapeEq (a b : Node) : Bool :=
  if ptrEq a b then true
  else
    match a, b with
    | .leaf _,        .leaf _        => true
    | .pair al ar _,  .pair bl br _  => Node.shapeEq al bl && Node.shapeEq ar br
    | _,              _              => false

/-- Insert `r ↦ n`, wiping the map first when the insertion would
exceed `capacity`. Capacity 0 stores nothing. -/
private def HashConsState.insertBounded (s : HashConsState) (r : ByteArray)
    (n : Node) : HashConsState :=
  if s.capacity == 0 then s
  else if s.count + 1 > s.capacity then
    { s with cache := ({} : Lean.PersistentHashMap ByteArray Node).insert r n
             count := 1 }
  else
    { s with cache := s.cache.insert r n, count := s.count + 1 }

/-- Look one pair cell up in the cache by its cached root. Returns
the shape-equal cell the cache already holds on a hit; on a miss,
inserts `n` and returns it. A cell whose cache slot is `none` has
no key and passes through untouched, as does a leaf.

The lookup, the shape check, and the insert run inside one
`modifyGet` so concurrent callers see a consistent map. -/
unsafe def Node.consCellUnsafe (n : Node) : BaseIO Node :=
  match n with
  | .pair _ _ (some r) =>
      hashConsRef.modifyGet fun s =>
        match s.cache.find? r with
        | some existing =>
            if Node.shapeEq existing n then
              (existing, { s with hits := s.hits + 1 })
            else
              -- Same root, different shape: the block-versus-header
              -- case. Keep the first occupant and hand back `n`.
              (n, { s with misses := s.misses + 1 })
        | none =>
            let s := { s with misses := s.misses + 1 }
            (n, s.insertBounded r n)
  | _ => return n

/-- The safe face of `consCellUnsafe`. The kernel-visible body is
`pure n`; compiled code runs the cache lookup. -/
@[implemented_by Node.consCellUnsafe]
def Node.consCell (n : Node) : BaseIO Node := return n

/-- Smart constructor for `Node.pair` that consults the cache. The
`BaseIO` form kept for callers that hold a root in hand; the pure
`Node.consPair` below is what the commit walk uses. -/
def Node.mkPair (left right : Node) (root : Option ByteArray) : BaseIO Node :=
  Node.consCell (.pair left right root)

/-- Cons every pair cell of a fresh tree, top-down with an early
exit. See the module docstring for why the top-first order is
cheaper than bottom-up on a tree whose shared subtrees are large. -/
unsafe def Node.consTreeUnsafe (n : Node) : BaseIO Node :=
  match n with
  | .leaf _ => return n
  | .pair l r c => do
      let hit ← Node.consCellUnsafe n
      if !(ptrEq hit n) then
        -- The cache already held a shape-equal subtree: share it.
        return hit
      let l' ← Node.consTreeUnsafe l
      let r' ← Node.consTreeUnsafe r
      if ptrEq l l' && ptrEq r r' then
        -- Every child was a miss; `n` is already in the cache.
        return n
      -- Some child was replaced by a shared cell. Rebuild the parent
      -- around the shared children and make the cache hold that
      -- copy, so later hits on this root also share them.
      let rebuilt : Node := .pair l' r' c
      match c with
      | some root => hashConsRef.modify (·.insertBounded root rebuilt)
      | none      => pure ()
      return rebuilt

/-- Pure entry for `consTreeUnsafe`, used for the initial
`Node.ofShape` build and for each pending subtree at commit. -/
unsafe def Node.consTreeImpl (n : Node) : Node :=
  unsafeBaseIO (Node.consTreeUnsafe n)

/-- Cons every pair cell of a fresh tree. The kernel sees the
identity; compiled code shares subtrees through the cache. The
result has the same root and the same shape as `n`. -/
@[implemented_by Node.consTreeImpl]
def Node.consTree (n : Node) : Node := n

/-- Pure one-cell form: allocate a pair with its root and cons it.
Used by `Node.commitAndHash` for the spine cells it allocates when
its `consing` flag is set. -/
unsafe def Node.consPairImpl (left right : Node) (root : ByteArray) : Node :=
  unsafeBaseIO (Node.consCellUnsafe (.pair left right (some root)))

/-- Allocate `.pair left right (some root)` and cons it. The
kernel sees the plain allocation; compiled code may return a
shape-equal cell the cache already holds. -/
@[implemented_by Node.consPairImpl]
def Node.consPair (left right : Node) (root : ByteArray) : Node :=
  .pair left right (some root)

end SizzLean.Cache.MerkleTree
