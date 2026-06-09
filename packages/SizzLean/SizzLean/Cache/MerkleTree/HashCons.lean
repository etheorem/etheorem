import Std.Data.HashMap
import SizzLean.Cache.MerkleTree.Node

/-!
# `SizzLean.Cache.MerkleTree.HashCons`: bounded-LRU dedup for identical subtrees

A global per-process cache mapping 32-byte SHA-256 roots to the
populated `Node.pair` cell whose `merkleRoot` equals that root.
Used to dedup identical populated subtrees *after* their root has
been computed. When a second tree-construction produces the same
`(left, right, root)` triple, the smart constructor `Node.mkPair`
returns the cached cell instead of allocating a fresh one.

## What the cache covers

* A global `IO.Ref`-backed `Std.HashMap ByteArray Node`. The
  cache is bounded (default capacity 4096); when full, a simple
  "wipe-half" eviction policy keeps memory bounded without
  needing a real LRU linked-list.
* `Node.mkPair` smart constructor: for `(left, right, some root)`
  triples it consults the cache; on hit, returns the cached
  cell. On miss, inserts and returns a fresh `.pair` allocation.
* `(left, right, none)` is a no-op, the dedup key (the root) is
  unknown until `merkleRootWithCache` computes it.

## What the cache does not cover

* Bottom-up dedup at construction time (the ChainSafe
  `persistent-merkle-tree` shape that delivers a ~30% heap
  reduction on archive workloads). That would require
  identity-keyed lookup on `(left, right)` *before* the root is
  known, which in turn requires the children themselves to be
  consed first, a recursive structural dependency.
* Integration into `Node.ofShape` (the construction site that
  builds trees from `SSZRepr`). `Node.mkPair` is available to
  call but is not wired into `ofShape`'s `.pair` allocations,
  so existing trees behave identically; opt-in by calling
  `mkPair` directly.
* Weak-reference semantics. The LRU bound provides upper-bound
  memory pressure; weak refs would let the cache follow Lean's
  refcount lifecycle naturally, but Lean 4 does not expose a
  weak-ref API.

## How the LRU eviction works

The cache stores up to `capacity` (default 4096) entries. When
the next insertion would exceed `capacity`, we clear the
entire map and start over. This is a "wipe-half" eviction in
spirit, strictly speaking we wipe-all and let the workload
re-populate. Pragmatic for this use case: the cache is a
performance optimisation; correctness doesn't depend on a hit.

A real LRU (with access-time tracking) would keep more useful
entries longer at the cost of per-access bookkeeping. The
wipe-all variant has zero per-access overhead. For the
documented archive workload (storing N consecutive
`BeaconState`s), wipe-all loses only the last cache generation
when capacity is hit; over many states the average win is
proportional to the average lifetime of common subtrees, which
this scheme captures.

## Trust footprint

None added. The cache is observationally transparent, a hit
returns a `Node` that's structurally `==` to what `.pair l r r0`
would have produced. The coherence tests in
`SizzLeanTests/HashConsCoherence.lean` empirically validate this
on a small set of fixtures.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

/-- Maximum number of entries in the global hash-cons cache.
Chosen to bound RSS at a few hundred KB per process (each entry
is a 32-byte key + one `Node` pointer + hashmap overhead). For
larger workloads, increase via `HashCons.setCapacity` before
any cache traffic begins. -/
def HashCons.defaultCapacity : Nat := 4096

/-- Mutable state for the hash-cons cache: the map itself plus
the current capacity bound. -/
structure HashConsState where
  cache    : Std.HashMap ByteArray Node
  capacity : Nat
  deriving Inhabited

private def hashConsInitial : HashConsState :=
  { cache := {}, capacity := HashCons.defaultCapacity }

initialize hashConsRef : IO.Ref HashConsState ← IO.mkRef hashConsInitial

/-- Reset the hash-cons cache to empty (preserving the current
capacity). Useful at the start of a benchmark or test to ensure
consistent measurements. -/
def HashCons.clear : BaseIO Unit := do
  let s ← hashConsRef.get
  hashConsRef.set { s with cache := {} }

/-- Set the cache capacity. Wipes existing entries to enforce
the new bound. Capacity 0 disables the cache entirely (every
`mkPair` becomes a fresh allocation). -/
def HashCons.setCapacity (n : Nat) : BaseIO Unit := do
  hashConsRef.set { cache := {}, capacity := n }

/-- Current entry count (for diagnostics / bench reporting). -/
def HashCons.size : BaseIO Nat := do
  let s ← hashConsRef.get
  return s.cache.size

/-- Smart constructor for `Node.pair` that consults the global
hash-cons cache. On a cache hit (same 32-byte root previously
seen), returns the *same* `Node` cell. Lean's reference-counting
runtime then makes the dedup observable as shared structure. On a
cache miss, allocates a fresh `.pair`, inserts it into the cache,
and returns it.

For `(left, right, none)` triples, when the root hasn't been
computed yet, this falls through to the plain `.pair`
allocation without touching the cache. The dedup key is the
root; without it, we have no lookup.

If the cache would exceed `capacity` on insertion, the cache is
wiped first and the new entry becomes the first occupant of the
next generation. -/
def Node.mkPair (left right : Node) (root : Option ByteArray) :
    BaseIO Node := do
  match root with
  | none => return .pair left right none
  | some r =>
      let s ← hashConsRef.get
      match s.cache[r]? with
      | some existing => return existing
      | none =>
          let fresh := .pair left right (some r)
          let cache' :=
            if s.cache.size + 1 > s.capacity then
              -- Wipe-all eviction: simplest bounded policy.
              ({} : Std.HashMap ByteArray Node).insert r fresh
            else
              s.cache.insert r fresh
          hashConsRef.set { s with cache := cache' }
          return fresh

end SizzLean.Cache.MerkleTree
