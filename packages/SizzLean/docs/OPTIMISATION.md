# SizzLean: Cache & performance architecture

This document is the implementation-level companion to
[`ARCHITECTURE.md`](ARCHITECTURE.md) §6 and the design-research
notes in [`research/cache-research.md`](research/cache-research.md).
ARCHITECTURE.md states *what* the cache layer is and *why* it
exists; this document explains *how* the current code is
organised (Phase 14, shipped) and *what the open Stage 17
sub-stages would actually do* (more detail than PLAN.md carries).

Pointers to prior art live throughout, most importantly
[`protolambda/remerkleable`](https://github.com/protolambda/remerkleable),
the Python persistent-Merkle-tree library whose `PairNode` /
`RootNode` design SizzLean inherits, and Lighthouse / Lodestar /
Teku for the optimisation patterns that production clients
converged on.

## Contents

1. [Scope](#scope)
2. [Phase 14: what's implemented](#phase-14--whats-implemented)
   1. [`Node` representation](#node-representation)
   2. [`ZERO_HASHES` precomputation](#zero_hashes-precomputation)
   3. [Cached root computation (`merkleRootWithCache`)](#cached-root-computation-merklerootwithcache)
   4. [Structural-sharing updates (`setAt` / `setManyAt`)](#structural-sharing-updates-setat--setmanyat)
   5. [`TreeBacked` / `CachedSSZ` value wrapper](#treebacked--cachedssz-value-wrapper)
   6. [The `sszUpdate` macro (write side)](#the-sszupdate-macro-write-side)
   7. [The `sszGet` macro (read side)](#the-sszget-macro-read-side)
   8. [The `sszModify` macro (read-modify-write)](#the-sszmodify-macro-read-modify-write)
   9. [Coherence invariant and its safety net](#coherence-invariant-and-its-safety-net)
3. [Phase 17: open optimisations](#phase-17--open-optimisations)
   1. [Stage 17a: Deferred-update overlay](#stage-17a--deferred-update-overlay-viewdu-style)
   2. [Stage 17b: Batched SHA-256](#stage-17b--batched-sha-256)
   3. [Stage 17c: Hash-consing](#stage-17c--hash-consing)
   4. [Stage 17d: Profile-guided `@[specialize]`](#stage-17d--profile-guided-specialize)
   5. [Stage 17e: Serialised-form caching](#stage-17e--serialised-form-caching)
4. [The cross-stage invariant: the pure path stays kernel-reducible](#the-cross-stage-invariant--the-pure-path-stays-kernel-reducible)
5. [Benchmarking and gating](#benchmarking-and-gating)
6. [Where to find what](#where-to-find-what)

## Scope

The library's central correctness path is the verified spec
recursion on `SSZType` (Layer 1). It is *complete on its own*:
`SSZ.hashTreeRoot Sha256 v` on a plain `T` reads a 32-byte root
out without ever touching this document's machinery.

What the cache layer adds is *production performance*: a
hash-tree root after a single-field mutation should walk
`O(depth)` nodes (40-ish SHA-256 calls for `BeaconState`),
not the whole tree (millions of leaves). The Layer 4 cache is
therefore a *performance layer*, not a verification layer,
asserted equivalent to the spec, validated empirically against
`ethereum/consensus-spec-tests` plus the in-library
`SizzLeanTests/TreeBackedCoherence.lean` property test. None of
this document's contents enters the proof obligation; none of
its optimisations changes what `rfl` / `decide` close on the
plain-`T` / `SSZ.PureBox` paths.

## Phase 14: what's implemented

Stages 12, 13, 14a–e shipped. The end-to-end story is:

* SSZ values live in a persistent binary Merkle tree (`Node`)
  alongside a value-level `view : T`.
* Each interior node carries an optional cached root, filled
  lazily on first walk.
* Updates allocate one fresh `pair` per level along the path
  from the changed leaf to the root; everything off-path stays
  shared by reference (Lean 4's reference-counted runtime does
  the work without explicit `Arc`).
* The cached root is cleared (set to `none`) along the updated
  spine; the next root read re-fills it walking only the dirty
  spine.

This section walks the implementation file by file.

### `Node` representation

`packages/SizzLean/SizzLean/Cache/MerkleTree/Node.lean`.

```lean
inductive Node where
  | leaf : ByteArray → Node
  | pair : Node → Node → Option ByteArray → Node
  deriving Inhabited
```

Two constructors:

* `leaf b`: a 32-byte leaf. The leaf bytes *are* its root.
* `pair l r c`: an interior node. `c : Option ByteArray` is the
  cached root: `some r` after `merkleRootWithCache` has walked
  this subtree, `none` after the most recent `setAt` cleared the
  cache along the updated spine.

This mirrors `remerkleable`'s `PairNode(left, right, root :
Optional[Root])` and `RootNode(root)` precisely, with the
single departure that we lift `RootNode` to be `leaf` (always-
populated 32 bytes), and represent "depth-`d` empty subtree" as
`zeroLeaf H d` (= `leaf ZERO_HASHES[d]`), not as a separate
constructor. The two-constructor model keeps the inductive small
enough that `Node.cached`, `merkleRootWithCache`, and `setAt`
each pattern-match on three or four cases, which the kernel
unfolds cleanly during the property tests in
`SizzLeanTests/SetAtRandom.lean`.

The `Option ByteArray` cache slot is *morally const* mutation:
filling `none → some r` doesn't change the logical value
(`merkleRoot` is a pure function of `(left, right)`), only the
observation cost. `remerkleable` calls this "lazy root caching";
Lighthouse's Milhouse and ChainSafe's persistent-merkle-tree do
the same in mutable form. In Lean the slot is an inductive field
that an update writes to a fresh `pair` cell, same observable
semantics, different memory model.

### `ZERO_HASHES` precomputation

`packages/SizzLean/SizzLean/Cache/MerkleTree/Zero.lean`.

A length-65 vector indexed by depth `d ∈ [0, 64]`:

```lean
def ZERO_HASHES (H : Type) [Hasher H] : Vector ByteArray 65
```

The recurrence is `ZERO_HASHES[0] = 32 zero bytes` and
`ZERO_HASHES[d + 1] = Hasher.combine ZERO_HASHES[d]
ZERO_HASHES[d]`. The cap of 64 covers every SSZ tree depth that
appears through Gloas (`BeaconState.validators` is `List
Validator (2 ^ 40)`, depth 40 + 1 for the length mix-in).

The single most-important property this buys: a `List[Validator,
2 ^ 40]` with 1M populated entries, typical mainnet, is
representable in O(populated × depth) Node allocations *plus
constant zero-subtree pointers*. Every unpopulated subtree is a
single `zeroLeaf H d` allocation reusing the precomputed bytes.
Without this, the tree representation would have to materialise
2^40 leaves; with it, the unpopulated subtree's "leaf-ness" is
inherited from a precomputed digest.

`zeroLeaf` and `Node.ofLeaves` are the two consumers; both are
purely structural and recurse on the leaf array's length.

### Cached root computation (`merkleRootWithCache`)

`packages/SizzLean/SizzLean/Cache/MerkleTree/Merkle.lean`.

```lean
def Node.merkleRootWithCache (H : Type) [Hasher H] :
    Node → ByteArray × Node
  | .leaf b => (b, .leaf b)
  | .pair l r (some root) => (root, .pair l r (some root))
  | .pair l r none =>
      let (rootL, l') := Node.merkleRootWithCache H l
      let (rootR, r') := Node.merkleRootWithCache H r
      let root := Hasher.combine (H := H) rootL rootR
      (root, .pair l' r' (some root))
```

Three arms:

* `leaf b`: root is `b`, return the node unchanged.
* `pair _ _ (some r)`: **cache hit**; return the cached root,
  return the node unchanged. This is the line that makes
  Lighthouse's "BeaconState root in 9 ms after a single
  validator update" performance achievable.
* `pair l r none`: **cache miss**; recurse both children, combine
  their roots via the chosen `Hasher H` instance, return a fresh
  `pair` with the freshly cached root. The fresh-pair allocation
  is unavoidable in the immutable representation, but it's only
  along the dirty spine, never the off-spine subtrees, which the
  caller passed in by reference and the recursion returns by
  reference.

`Node.merkleRoot H n := (n.merkleRootWithCache H).1` is the
convenience wrapper that drops the cache-filled `Node` when the
caller wants only the digest.

The cache hit on `pair _ _ (some r)` is what makes the
optimisation worthwhile. Without it, every root computation
would re-walk the whole tree; with it, only dirty subtrees walk.
After a single-field update, only `depth` nodes are dirty along
the spine; the other `2^depth − depth` subtrees serve their
cached root in O(1).

### Structural-sharing updates (`setAt` / `setManyAt`)

`packages/SizzLean/SizzLean/Cache/MerkleTree/SetAt.lean`.

Updates walk the tree by *generalised index* (gindex), the
standard SSZ scheme that addresses any tree position by the
binary representation of its level-by-level path.

```lean
def gindexBits (g : Nat) : List Bool       -- gindex → path bits, MSB-first

def Node.setAt (n : Node) (g : Nat) (newSubtree : Node) : Node
def Node.setManyAt : Node → List (List Bool × Node) → Node
```

`setAt` recurses on `gindexBits g`, allocating one new `pair`
per level (left or right child rebound; the other shared) and
clearing the cache slot (`none`) for the new pair. Sibling
subtrees on the off-path side are returned by reference, so the
allocation count for one field update is exactly
`depth(structure) + 1` `pair` cells.

The single recursion on a `List Bool` of bits, instead of an
arithmetic gindex traversal, was deliberately chosen so that
the **Nimbus February 2025 mainnet gindex bug** (off-by-one on
list-length leaf positions) is *unrepresentable* in our walker.
There is no integer arithmetic on the gindex once the bits are
extracted; the walker pattern-matches on the bit list.

`setManyAt` is the batched form. The naïve approach, calling
`setAt` once per write, would allocate fresh spine cells for
*each* write, even when two writes share path prefixes. The
batched walker partitions the writes by their first bit at each
level and recurses once per partition, so writes that share a
prefix share the corresponding spine allocations.

For a multi-field update on a container of depth `d` with `k`
writes and `s` levels of shared spine, this drops the allocation
count from `k · d` to roughly `d + k · (d − s)`. That's the
optimisation Lodestar's `ViewDU` and Lighthouse's
`with_updates_leaves` ship; we ship it as a single call site
because the `sszUpdate` macro batches the writes at expansion
time.

### `TreeBacked` / `CachedSSZ` value wrapper

`packages/SizzLean/SizzLean/Cache/TreeBacked.lean`.

```lean
structure TreeBacked (H : Type) (T : Type) [Hasher H] [SSZRepr T] where
  view : T
  tree : Node

abbrev CachedSSZ := TreeBacked
```

Two fields: the value-level `view : T` (so reads bypass the
cache entirely, see `sszGet` below) and the persistent
Merkle-tree `tree : Node`. The hasher `H` is part of the *type*,
so mixing hashers within one cached value is a type error rather
than a silent root mismatch. The cache cells were filled by
`H`'s `combine`, and a subsequent read with a different `H'`
would observe wrong bytes.

`CachedSSZ` is the *user-facing* alias; the user constructs
through `CachedSSZ.ofValue Sha256 v`, reads via dot notation /
`sszGet`, and updates via `sszUpdate`. `TreeBacked` is the
*internal* name retained where the gindex / spine vocabulary
matters (in `setManyAt`, in the macro's emission paths). Both
names refer to the same `structure`.

### The `sszUpdate` macro (write side)

`packages/SizzLean/SizzLean/Cache/Update.lean`.

User syntax:

```lean
sszUpdate t with
  epoch                          := 42,
  message.slot                   := newSlot,
  blockRoots[i]                  := r,
  validators[i].effectiveBalance := newBalance
```

The term elaborator (`elabSszUpdate`) inspects the base term `t`'s
type at expansion time and emits one of three specialised forms:

* **Cached path** (`TreeBacked H T` / `CachedSSZ H T`). The
  elaborator computes path bits for each clause at expansion
  time (the structure reflection is fully known), groups them
  into a single `List (List Bool × Node)`, and emits one call
  to `Node.setManyAt`. The view side becomes a chained
  `{ t.view with f := v, … }`. Net result: one `setManyAt`
  walk per `sszUpdate` statement.

* **Uncached path** (`UncachedSSZ H T`). Emits a plain
  `{ view := { t.view with f := v, … } }` struct rewrite. No
  Merkle vocabulary; closes by `rfl` in proofs.

* **Box path** (`SSZ.Box H T`). Emits a two-arm `match` on the
  Box constructor, dispatching each arm to the corresponding
  per-flavour emission above. The Box value's flavour is
  preserved across updates.

The macro emits structural-sharing-friendly code regardless of
the input shape: an `SSZ.FastBox`-built value stays Fast through
every chain of `sszUpdate`s, and the cached spine stays
`Node.setManyAt`-batched even across the box dispatch.

For Vector / SSZList element updates with *composite* element
types (the index syntax `vec[i] := v` on `Vector Validator n` /
`SSZList Validator n`), the cached path is fully supported. For
*basic-packed* elements (`Vector UInt64 n[i] := bal`) the cached
path is rejected at expansion time, because basic packing
requires a chunk-rebuild that the flat macro doesn't ship.
Whole-vector replacement (`balances := balances.set! i bal`) is
the current workaround; targeted basic-packed indexing is a
planned Sub-F follow-up gated on measured need.

### The `sszGet` macro (read side)

The read-side companion in the same file. Identical path syntax
to `sszUpdate`, expanding purely syntactically to
`base.view.<path>`:

```lean
sszGet b epoch                          -- → b.view.epoch
sszGet b message.slot                   -- → b.view.message.slot
sszGet b validators[i]                  -- → b.view.validators[i]
sszGet b validators[i].effectiveBalance -- → b.view.validators[i].effectiveBalance
```

Reads bypass the tree side entirely; they project the
value-level `view : T` and walk Lean's standard struct /
array accessors. The cached and uncached flavours give
*observationally identical* read behaviour.

The macro is a one-line `macro_rules` rewrite. It adds no
typeclass dispatch, no elaborator branching, no overhead. The
post-expansion term is a chain of Lean's built-in projection
notation, so `rfl` / `decide` / `simp` proofs about reads close
exactly as if the user had typed `.view.f.g[i].h` directly. The
only thing the macro buys is hiding `.view` from the
documented user surface; the user types `sszGet`, never
`.view`.

### The `sszModify` macro (read-modify-write)

`sszModify` (same file) names a path once for a read-modify-write,
`sszModify b f[i]! := g` to apply a function and
`sszModify b f[i]! as x => body` to rewrite the bound current value
(`fun`-free, for `{ x with … }` bodies). It is a purely syntactic
rewrite to `sszUpdate b with f[i]! := (let x := sszGet b f[i]!; …)`,
so it inherits the write side's single-leaf cached update and the
read side's projection with no extra cost; performance is exactly
that of the `sszUpdate` / `sszGet` pair it expands to. It applies on
the total `[i]!` and field paths, where the read returns the bare
element.

### Coherence invariant and its safety net

The single invariant on the cache layer:

> For every `t : TreeBacked H T`, `t.hashTreeRootCached =
> SSZ.hashTreeRoot H t.view`.

This is *not* a kernel-checked theorem. Per
[`research/cache-research.md`](research/cache-research.md) §5,
the cache is intentionally outside the formal-verification
frontier. The verified spec layer is what closes the
correctness story, and the cache is asserted equivalent to it.
The safety net is two property tests:

* `SizzLeanTests/TreeBackedCoherence.lean`:
  `t.hashTreeRootCached = SSZ.hashTreeRoot Sha256 t.view`
  on the example containers, fired via `native_decide` at
  build time.
* `SizzLeanTests/TreeBackedSetField.lean` /
  `MultiSetterIndex.lean`: PRNG-driven property tests for the
  `sszUpdate` emission paths, against the spec oracle.

Plus the cross-implementation `ssz_static` upstream-vector
sweep (the `EthCLSpecs` pytest harness in
`packages/EthCLSpecs/PySpecTests/`), which exercises the
production cached path against the consensus-spec-tests release
for the Fulu and Gloas forks.

This is the same safety-net shape `remerkleable` ships
(`tests/test_roundtrip.py` plus consensus-spec-tests
integration in `eth2spec`).

## Phase 17: open optimisations

Five sub-stages with a microbenchmark in
`packages/SizzLean/SizzLeanBench/` (run via `just sizzlean-bench`). Status:

| Sub-stage | What | Status |
|---|---|---|
| 17a | Pending overlay (closure-based, read-from-view at commit) | **shipped** |
| 17b.0 | Batched FFI primitive `sha256BatchCombine` + named axiom | **shipped** |
| 17b.1 | Multi-buffer inner loop in the C shim (ISA-L on x86_64 Linux) | **shipped** |
| 17b.2 | Rank-frontier Lean walker that batches `sha256BatchCombine` by readiness rank | **not done** |
| 17c | Hash-consing on the cached path, opt-in at `Box` construction | **shipped; default off** |
| 17d | `@[specialize]` on the three SSZ surfaces | **shipped (pass 1)**; per-type hints profiled and declined (pass 2) |
| 17e | Fused commit walk (`Node.commitAndHash`) + pre-cached `Node.ofShape` builders | **shipped** |

The measured-need gate that originally fronted Stage 17 has been
crossed in two directions: the benches now show *which* of the
shipped optimisations deliver real wins (17a + 17e together are
the headline cache-vs-pure ratio on realistic workloads, see
S6/S7 in the bench) and *which* ship infrastructure pending a
follow-up to light up (17b.0 + 17b.1, the batched primitive and
its multi-buffer shim, wait on the 17b.2 rank-frontier walker). Each section below records both the
design and the measured result; the per-sub-stage details
remain accurate as implementation references. They document what
the optimisation does, the data structure it needs, the prior
art we're learning from, the specific Lean integration shape,
and the proof-side invariant each must respect.

### End-to-end win: pure vs all-optimisations-on

For the *combined* effect across a realistic workload, what
the library delivers when a user just uses its default surface
rather than reaching for the spec, see
`SizzLeanBench/Pipeline.lean`. It compares a pure-spec pipeline
(plain `T`, Lean record-updates, spec calls for every read /
serialise) against the same workload run through `TreeBacked` +
`sszUpdate` + `TreeBacked.serialize`, on two shapes:

| Workload | Pure | Optimised | Speedup |
|---|---|---|---|
| state-transition (8 writes, 8 reads, 1 serialise) | ~283 µs | ~89 µs | **3.2×** |
| process-then-emit (8 writes, 1 read, 1 serialise) | ~53 µs | ~45 µs | 1.2× |

The state-transition pattern shows the dramatic win because
every per-update root read in the pure path pays a full re-hash
(~28 µs × 8 = ~224 µs), while the cached path only walks the
dirty spine (~10 µs each) plus the serialised cache trims the
final emit. The process-then-emit pattern shows a smaller win
because there's only one root read. The SHA-256 work itself is
the dominant cost, the same in both paths.

`@[specialize]` (17d) fires in both columns (compile-time, can't
be toggled at runtime). 17b batched SHA-256 is *not* exercised by
the default cached path; it is opt-in through `sha256BatchCombine`.
17c hash-consing is on the cached path but off by default;
`SSZ.FastBox v (consing := true)` turns it on per box, and its
own bench (`ssz_multistate`) measures the multi-state workload it
exists for.

The ordering below is the default sequence (highest-impact-
first per Lighthouse's Milhouse benchmarks and Lodestar's
`ViewDU` paper); profiling on a specific workload may re-order.

### Stage 17a: Pending overlay (closure-based, read-from-view): **shipped**

The pending overlay is folded into the existing `TreeBacked`
structure rather than exposed as a separate `ViewDU` type. Every
`TreeBacked H T` carries:

```lean
def PendingWrite (T : Type) : Type := T → Option Node

structure TreeBacked (H : Type) (T : Type) [Hasher H] [SSZRepr T] where
  view     : T                                          -- always current
  treeBase : Thunk Node                                 -- deferred until first root
  pending  : Std.TreeMap Nat (PendingWrite T) := {}     -- gindex → closure
```

The deferral lives at two levels:

* **`treeBase : Thunk Node`**: `TreeBacked.ofValue` builds it as
  `Thunk.mk (fun _ => Node.ofShape …)`. No tree-shape work runs
  at construction; the first `hashTreeRoot` forces it once and
  `Thunk`'s memo carries the result.
* **`pending`**: each `sszUpdate` clause emits a *closure*
  (`T → Option Node`) that, at commit time, projects the
  relevant sub-value out of the **current** `view` and builds
  the matching sub-tree via `Node.ofShape`. Closures that
  return `none` (most commonly because a runtime index was OOB
  and `Array.set!` was a view-side no-op) are dropped at commit.

`hashTreeRootCached` runs every closure against the current
`view`, hands the surviving `(gindexBits, Node)` pairs to
`Node.commitAndHash` (§17e), and stores the cached output back
into `treeBase` for the next commit's starting point.

The win is threefold:

1. **Automatic cross-statement batching.** A chain of N
   single-clause `sszUpdate`s + one root read produces *one*
   `commitAndHash` walk, not N spine walks.
2. **No work on overwritten writes.** Two `sszUpdate`s at the
   same gindex collapse via `TreeMap.insert`; only the last
   closure ever runs.
3. **Parent/child coherence for free.** Closures all share one
   `view`. A parent's closure projects `view.field` which already
   reflects every later child write the user issued. The
   `commitAndHash` "drop deeper write at same level as a `[]`-path
   write" rule then drops the redundant child entry without
   semantic loss, because the parent already encoded it.

**Why read from view at commit rather than capture at insert.**
An earlier design captured `(shape, value)` snapshots at insert
time. That broke on parent/child gindex relations: write
`parent := y` then `parent.child := z` left both in pending; at
commit the parent's snapshot `y` had no `z` in it, and the
commit-time drop discarded the child entry, so the committed
root reflected `y` while the view reflected `y` with
`child := z`. Reading from view at commit closes that gap by
construction.

**OOB-aware closures.** The macro emits a bounds check around
each index step in the projection path: `xs[i]!` becomes
`if i < xs.size then some (Node.ofShape … xs[i]!) else none`.
This mirrors view-side `Array.set!`-on-OOB-is-a-no-op so the
cache stays in lockstep with the view regardless of the
element type's `Inhabited` default.

**Measured result.** Benchmarks at `packages/SizzLean/bench/`:

* **S6 BlockProcessingLarge** (32 slots × 8 writes on
  `ValidatorSet256`): cached ~43 ms, pure ~102 ms, **2.4×
  cached faster**.
* **S7 FuluStateTransition** (mainnet preset, ~1024 validators,
  16-slot state-transition simulation): cached ~2.6 s, pure
  ~5.2 s, **2.0× cached faster**.

Regression coverage:

* `SizzLeanTests/PendingPrefixConflict.lean`: 5 cases on
  parent/child gindex prefix relations.
* `SizzLeanTests/PendingListShrink.lean`: 8 cases on
  list-shrink + stale-index writes (including a non-zero
  `Inhabited` element that surfaces the bounds-check requirement).
* `SizzLeanTests/WidthsAndLists.lean`: 32 cases on basic widths
  (Bool, UInt8/16/32/64, BitVec 128/256) × list-size changes.

**Original design sketch follows**, kept for historical
context; the shipped form removes the separate `ViewDU`
wrapper.

**What it does.** Accumulate pending writes in an ordered map
keyed by gindex; on `commit`, replay them in gindex-ascending
order through `Node.setManyAt`, batching across path prefixes
just like the existing within-statement `sszUpdate` already
does, but now *across* statements.

The current `sszUpdate` already batches writes within one
statement: `sszUpdate s with x := v, y := w` shares the
spine work between `x` and `y`. What it doesn't batch is the
common state-transition pattern of

```lean
let s := sszUpdate s with x := 1
let s := sszUpdate s with y := 2
let s := sszUpdate s with z := 3
-- then read the root
```

That is three separate `setManyAt` calls walking three separate
spines. With `ViewDU`, those three writes are accumulated into a
`Std.TreeMap Nat Node` and committed in one walk on the
subsequent root read (or the first time a function asks for the
committed shape).

**Data structure.** A new module
`SizzLean/Cache/Overlay.lean`:

```lean
structure ViewDU (H T : Type) [Hasher H] [SSZRepr T] where
  base    : TreeBacked H T
  pending : Std.TreeMap Nat Node    -- gindex → replacement subtree
```

**Commit.**

```lean
def ViewDU.commit (v : ViewDU H T) : TreeBacked H T :=
  let updates := v.pending.toList.map fun (g, n) => (gindexBits g, n)
  { v.base with tree := v.base.tree.setManyAt updates }
```

The `toList` traversal of an ordered map yields entries in
gindex-ascending order, which means `setManyAt`'s
partition-by-first-bit step sees the writes in a path-grouped
order naturally, every shared prefix appears as a contiguous
run of writes.

**Prior art.**

* `remerkleable` does not ship a deferred-update overlay
  (single-threaded write-through). The pattern below is lifted
  from Lodestar's `View` / `ViewDU` distinction
  (`lodestar/packages/state-transition/src/cache/view-du.ts`),
  which adds a "deferred update" wrapper on top of the
  underlying persistent tree.
* Lighthouse's Milhouse `with_updates_leaves`
  (`milhouse/src/tree.rs`) is the same concept, batching leaf
  updates into a single tree walk. The cited speedup over
  per-leaf updates is 5–10× on a 1000-validator slashing
  scenario.
* Teku's `MutableSchemaList` does it differently, by
  duplicating the spine into a writeable copy and rebatching at
  the end. We're following the immutable-base + pending-map
  shape because it matches Lean's reference-counted runtime
  semantics better.

**Microbenchmark target.** `bench/`: 1000 sequential
`setField`-style writes on a `BeaconState`-shaped container
should commit in close to one full-spine walk's worth of
hashing. That is, the per-write cost in the ViewDU pipeline should
be near-zero once the deferral is in effect.

**Proof-side invariant.** `ViewDU` doesn't touch
`UncachedSSZ` / plain `T` / `SSZ.PureBox`. The overlay is a
strictly cached-path optimisation. The pure / proof path stays
single-statement-typed and continues to use Lean's built-in
record-update syntax for any chained "write then read" pattern.

**Risk.** Medium. Spine deduplication is the tricky part, two
writes whose gindex paths share a prefix should share the
intermediate `pair` allocations the underlying `setManyAt` makes.
That's already what `setManyAt` does, so the ViewDU layer is
mostly "accumulate, sort, hand off to `setManyAt`". The risk is
on the read interface: any read between a `setField` and the
commit must observe the *would-be-committed* value, not the
underlying `base.view`. The straightforward fix is to mirror
the pending writes on the view side too, but that requires
either a second `Std.TreeMap String Dynamic`-shaped pending-view
map (not pleasant) or running the commit on every read (defeats
the deferral). Both are surveyed in
[`research/cache-research.md`](research/cache-research.md) §7.

### Stage 17b: Batched SHA-256

This sub-stage now tracks three pieces of work separately, in
parallel with PLAN.md §Stage 17b.

#### Stage 17b.0: FFI primitive + Lean wrapper + axiom: **shipped**

The FFI primitive `sha256BatchCombine`
(`csrc/sha256_batch.c`), the Lean wrapper
(`SizzLean/Hasher/Sha256Batch.lean`), the named equivalence
axiom `sha256BatchCombine_eq_spec`, and seven empirical-
equivalence test cases (`SizzLeanTests/Sha256BatchEquivalence.lean`).
The first-cut C shim shares one `EVP_MD_CTX` across the pair
array, avoiding N × allocation cycles.

**Measured result.** On a 128-pair (depth-7 SSZ bottom layer)
fixture:

| Path | Time |
|---|---|
| **pure-Lean (128 `LeanSha256.combine` calls)** | **~34 ms** |
| 128 scalar `sha256Combine` calls (FFI) | ~41 µs |
| `sha256BatchCombine` (one FFI call) | ~41 µs |

FFI scalar and FFI batched are within noise of each other,
both ~830× faster than the pure-Lean reference. The empirical
finding for the batched path: shared-EVP-context batching alone
doesn't beat scalar because OpenSSL's per-pair SHA-256
compression work (~300 ns × 128 = ~40 µs) dominates the
context-allocation amortisation (~10 ns × 127 saved calls =
~2 µs).

The pure-Lean column matters for proof-side code that pins
`H := Sha256Spec`, kernel-reducible but slower; the gap to
the FFI columns measures the FFI's value at hash work. Proofs
about state-transition functions don't pay this cost because
they reduce structurally and don't actually compute hashes.

#### Stage 17b.1: Cross-platform SIMD shim: **shipped**

**What shipped.** `LeanHazmatSha256/csrc/sha256_batch.c` carries two
backends behind the one `lean_hazmat_sha256_batch_combine` symbol,
and `LeanHazmatSha256/lakefile.lean` picks one per build host
(`useIsal`) and passes the choice to the C file as a single define:

* **x86_64 Linux (Intel + AMD)**: Intel **ISA-L crypto** `sha256_mb`
  (BSD-3-Clause), vendored at a pinned tag by
  `just hazmat-sha256-vendor` and built through ISA-L's own
  `Makefile.unx` for the one `sha256_mb` unit (needs `nasm`). Its
  job manager hashes 4 (SSE) / 8 (AVX2) / 16 (AVX-512) buffers in
  lock-step, or two streams on SHA-NI parts, auto-dispatched via
  CPUID at run time. The shim concatenates each pair into a 64-byte
  lane buffer, submits with `ISAL_HASH_ENTIRE`, drains, and
  serialises the eight host-order digest words big-endian. The
  manager's scratch lives per thread, so even one pair goes through
  ISA-L. The ISA-L objects are folded into the family's single
  archive, so no dependent package gains a link flag.
* **Everything else** (ARM64, macOS, other): the OpenSSL EVP loop,
  two `EVP_DigestUpdate` calls per pair on one shared context. On
  ARMv8 SHA-Ext CPUs (Apple M-series, Graviton 3+) OpenSSL already
  uses the hardware instructions, so this is hardware single-stream
  and the batch amortises the per-call overhead.

ISA-L is used because OpenSSL's public EVP API hashes one buffer per
call and cannot fill SIMD lanes; its internal `sha256_multi_block` is
private to the TLS stitched ciphers. Distributions do not package
ISA-L crypto (Debian's `libisal` is the storage library, without
`sha256_mb`), so it is vendored like blst and c-kzg.

**Measured** (`sha256BatchCombine`, one call, 32-byte siblings; x86_64
Linux, SHA-NI + AVX2, no AVX-512; scalar = the OpenSSL loop on the
same host):

| Pairs | OpenSSL loop | ISA-L | Speedup |
|---|---|---|---|
| 1 | ~1.7 µs | ~0.6 µs | ~2.7× |
| 16 | ~6.9 µs | ~4.2 µs | ~1.6× |
| 128 | ~35 µs | ~13 µs | ~2.8× |
| 1024 | ~274 µs | ~85 µs | ~3.2× |

Expected on other hosts, not measured: AVX-512 parts fill 16 lanes
and should sit nearer ~13× on the 128-pair row; ARM64 with SHA-Ext
keeps the ~1.5× amortisation win of the loop; hosts without hardware
SHA are unchanged.

**Trust footprint.** No change. The named axiom
`sha256BatchCombine_eq_spec` still asserts pointwise agreement with
the pure-Lean reference, and `Sha256BatchEquivalence` runs the same
cases against whichever backend the build host compiled in. ISA-L
sits in the same trust position as the OpenSSL shim.

#### Stage 17b.2: Rank-frontier batched walker: **not done; depends on 17b.1**

**Goal.** Feed the now-fast batched primitive from the cache's
own root walk. The walk groups every sibling pair that becomes
ready to hash at the same moment, wherever it sits in the tree,
and issues one `sha256BatchCombine` per group. "One batch per
geometric tree level" is the special case that holds when the
whole tree is a single perfect binary tree. SizzLean's trees are
not always that shape, so the walker batches by *readiness rank*,
which subsumes level order and packs the SIMD lanes fuller.

**Readiness already lives in the node type.** The `Node` cache
slot does double duty:

```lean
inductive Node where
  | leaf : ByteArray → Node
  | pair : Node → Node → Option ByteArray → Node   -- left, right, cached root
```

`none` means "needs recompute", `some root` means "already
computed", and `Node.cached` reads the slot in O(1). A `pair l r
none` is ready the instant both `l.cached` and `r.cached` are
`some`. There is no separate dirty set and no version counter;
the `Option` is the dirty bit and the readiness flag at once.
`setManyAt` / `setAtBits` confine the `none` cells to the touched
spines, and off-path children stay `some`, so the walk descends
only the dirty region and prunes resolved branches in O(1)
through `Node.rootOf`, the same pruning `commitAndHash` already
performs.

**Rank, not geometric level.** Give each dirty `pair` a *rank*,
the height of its tallest unresolved input:

```
rank(pair l r none) = 1 + max(rankOf l, rankOf r)
  rankOf child       = if child.cached.isSome then 0 else rank child
```

A leaf, and any node whose slot is already `some`, has rank 0.
Two pairs of equal rank are mutually independent: each input is
either cached or was produced by a strictly lower rank that
flushed earlier. One rank is therefore one batch. Rank coincides
with geometric level exactly when the tree is one perfect binary
tree. Across a heterogeneous container, whose fields are subtrees
of different heights, and across the incremental case, where
dirty leaves scatter through the tree, rank merges ready pairs
from different depths in different subtrees into a single batch.
That fills more lanes than per-subtree level batching, which
flushes each subtree's bottom row on its own. The `mix_in_length`
pair, whose children are a deep data-subtree root and a shallow
length leaf, falls out for free: the length leaf is `some` from
construction, so the mix-in pair takes rank `1 + rank(dataRoot)`.

**Deliverable.** `SizzLean/Cache/MerkleTree/MerkleBatch.lean`, a
`commitAndHash`-shaped walk restructured into three phases over
an explicit schedule, replacing the current single inline
recursion:

1. **Descend and schedule.** One post-order pass over the dirty
   region that hashes nothing. For each `pair _ _ none` it
   allocates an integer id and records
   `(id, leftSource, rightSource, rank)`, where each source is
   `Sum (cached digest) (id of another scheduled pair)`.
   Post-order yields children before parents, so a pair's rank is
   known when it is recorded. Records bucket by rank.
2. **Flush by rank.** For rank `0, 1, …, maxRank`: resolve the
   bucket's `inr id` inputs from results filled by earlier ranks,
   call `sha256BatchCombine` once on the whole bucket, and write
   each digest into an id-indexed results array.
3. **Rebuild.** Thread the computed roots back into the matching
   `none` slots, yielding the cached `Node` the recursive walk
   would have produced plus the root digest.

The schedule decouples hashing order from the immutable tree,
which the wave model needs. A pure-functional `Node` cannot have
a slot flipped in place mid-wave, so results sit in the id-indexed
array until the single rebuild pass. Wired as the cached-Box
path's default walk, or `@[implemented_by]` on
`merkleRootWithCache` when the signatures line up.

**Cost shape.** One schedule descent, plus `maxRank + 1` batched
calls, plus one rebuild, against today's single fused recursion
in `commitAndHash`. The extra descent and the id-indexed array
buy full batches on a pure-functional tree. They are dead weight
until the shim underneath is genuinely parallel, which 17b.1
delivered on x86_64 Linux.

After this lands, the scenarios bench's `S1`/`S3`/`S4`/`S6`
ValidatorSet rows should drop on x86 with AVX-512 (approx 3–5×
faster cached column) and modestly on ARM (~1.5×).

**Dependency on 17b.1.** The rank walker only pays off over a
genuinely parallel shim: on the OpenSSL loop, FFI batched ≈ FFI
scalar at ~40 µs / 128 pairs. With 17b.1 shipped (~13 µs / 128
pairs on a SHA-NI + AVX2 host, see above), the walker is now the
open piece.

**Prior art.**

* `gohashtree` (Prysm's hashing backend) is the reference
  implementation of the AVX-512 multi-buffer path. Its
  `sha256_avx_x4` hashes four message blocks in parallel and is
  the shape `sha256BatchCombine` dispatches into.
* `remerkleable` does not batch; Python-side it would be
  pointless. Batching is a C-level concern, and the rank-frontier
  traversal that *feeds* it is the new contribution here.
* Lighthouse's Milhouse uses `gohashtree`'s `HashChunks` for
  bulk-leaf hashing only, not interior nodes. The rank walker
  pushes batching one step further, up through every interior
  level of the dirty region.

**Dependency on Stage 15 (trust).** The Stage 15 conformance
story is "FFI `Sha256` ≡ pure-Lean `Sha256Spec` on 185 cases".
The batched primitive already carries the parallel assertion
shipped in 17b.0, the named axiom `sha256BatchCombine_eq_spec`,
which asserts `sha256BatchCombine lefts rights` equals the
pointwise `Sha256Spec.combine` of the zipped inputs, validated by
the seven `Sha256BatchEquivalence` cases. The rank walker adds no
new axiom: it only changes which pairs land in which FFI call,
and every call still answers to that one assertion. The batched
primitive stays a performance shim in the TCB behind its own
assertion, the same standing as the scalar FFI shim.

**Microbenchmark target.** Cold-root of a fully-populated
mainnet-preset `BeaconState` (~1M validators) should drop from
`gohashtree`-comparable scalar timing to within ~50% of
`gohashtree`'s batched implementation.

**Proof-side invariant.** Wired as an `@[implemented_by]` swap on
`merkleRootWithCache`, or as a new opt-in entry point, never as a
change to the `Hasher` typeclass. The abstract `Hasher Sha256Spec`
instance, which the `SSZ.PureBox` / `UncachedWith Sha256Spec`
paths use, sees no change and stays kernel-reducible.

**Risk.** Medium. The schedule-collect and rebuild phases are
mechanical. The design lever is keeping batches full: rank
bucketing already merges across subtrees, so the remaining
question is the small-tree tail, where the top ranks hold one or
two pairs and underfill the lanes. A threshold that hashes
sub-`N` ranks with the scalar `combine` and reserves
`sha256BatchCombine` for ranks above the lane width keeps the
underfilled tail off the SIMD path. 17b.1 owns where that
threshold sits; 17b.2 owns producing buckets big enough to clear
it.

### Stage 17c: Hash-consing: **shipped; default off, opt-in at `Box` construction**

**What ships.** A global `IO.Ref`-backed bounded cache
(`SizzLean/Cache/MerkleTree/HashCons.lean`, default capacity
4096, wipe-all eviction) keyed by 32-byte root, and a per-box
toggle: `SSZ.FastBox v (consing := true)` (also on `CachedBox`,
`CachedSSZ.ofValue`, `TreeBacked.ofValue`, and the two cached
`deserialize` helpers). `SSZ.FastBox v` stays consing-off. The
flag is stored on the `TreeBacked` and follows the box through
every `sszUpdate`.

**Where the cache is consulted.** The three sites that allocate
fresh cells on the cached path, and only when the flag is on:

* the initial `Node.ofShape` build inside `treeBase`, consed by
  `Node.consTree` when the thunk is forced;
* each pending subtree at commit, consed by `Node.consTree`
  before `commitAndHash` installs it;
* the spine cells `commitAndHash` allocates, through its own
  `consing` flag and `Node.consPair`.

`merkleRootWithCache`, `setAt`, `Build.lean`, `Sha256Spec`, the
uncached flavour, and plain `T` are untouched. With the flag off
the three sites run exactly as before. The two pure entry points
are `@[implemented_by]` wrappers over the `BaseIO` primitive; the
kernel sees the identity and the plain allocation.

**The shape rule.** Equal roots do not imply equal shapes: a
container and the vector of its field roots merkleize to the same
root (`BeaconBlock` versus `BeaconBlockHeader`), and a same-root
cell of the wrong shape would swallow later writes at a leaf. A
hit is accepted only when `Node.shapeEq` holds, leaf against leaf
and pair against pair at every position, with a pointer
short-circuit so the check is O(1) once children were consed
first. `SizzLeanTests/HashConsCoherence.lean` gates both the root
coherence and the shape rule through `SSZ.FastBox`.

**Measured result.** `ssz_multistate` (`just
sizzlean-bench-multistate`) keeps `N` fresh `ValidatorSet256`
states resident, each one validator away from a shared base, and
counts the distinct tree cells the `N` trees reach:

| N | consing off: pairs / leaves | consing on: pairs / leaves | est. bytes off → on |
|---|---|---|---|
| 1 | 2303 / 2304 | 2041 / 1787 | 405 KB → 341 KB |
| 10 | 23030 / 23040 | 2123 / 1794 | 4.05 MB → 350 KB |
| 50 | 115150 / 115200 | 2445 / 1794 | 20.3 MB → 383 KB |
| 100 | 230300 / 230400 | 2846 / 1794 | 40.5 MB → 425 KB |

Resident cells grow by about eight pairs per extra state with
consing on (one validator subtree plus one spine), against 2303
pairs per state without. The first state pays the cold fill,
about 2.2× its consing-off build time on the bench host; from
then on a top-level hit skips the whole subtree below it, and the
100-state run lands within a few percent of consing off. The
cache capacity has to fit the workload: the bench raises it to
2^20 because the default 4096 is smaller than one of these trees.

The cache lives in a global `IO.Ref`, and the runtime marks every
value stored into such a ref as shared between threads. The map
is therefore a `Lean.PersistentHashMap`, whose insert path-copies
in O(log n) whether or not it is shared; a `Std.HashMap` in the
same position copied its bucket array on every insert and made
the cold fill quadratic. The consed cells carry the same marking,
so later touches on them count references atomically.

The scenarios bench (`ssz_bench`) is the guard that the default
path is unchanged; its rows carry no consing column because a
single resident state gains nothing from it.

**Deferred.** Weak-reference semantics. Lean 4 has no weak-ref
API, so the bounded map with wipe-all eviction stays. For
workloads that justify weak refs, the swap is local to
`HashCons.lean`.

**Original design notes follow**, the prior-art map and the
weak-ref design discussion both still apply.

**What it does.** Dedupe identical populated subtrees globally
via a weak `HashMap (Hash32) Node`. Complements `ZERO_HASHES`'s
zero-subtree dedup (which handles only the canonical zero
case): if two distinct `BeaconState`s end up with identical
`validators[42:50]` ranges, both can share the same `pair`
allocation across the tree.

**Data structure.** A new module
`SizzLean/Cache/MerkleTree/HashCons.lean`:

```lean
private opaque hashConsCache : IO.Ref (Std.HashMap ByteArray Node)

def Node.mkPairConsed (left right : Node) (root : Option ByteArray) :
    BaseIO Node := do
  match root with
  | none => pure (.pair left right none)
  | some r =>
      let cache ← hashConsCache.get
      match cache.find? r with
      | some existing => pure existing
      | none =>
          let n := .pair left right (some r)
          hashConsCache.set (cache.insert r n)
          pure n
```

(weak-reference semantics omitted in the sketch, Lean's
runtime needs a real `IO.Ref` with the appropriate
`@[implemented_by]` swap to `lean_alloc_cached_weak`.)

**Prior art.**

* `remerkleable` does not hash-cons (Python's reference
  semantics make it awkward; a single-state usage doesn't show
  the win).
* ChainSafe's `persistent-merkle-tree` *does*; it ships a
  global `WeakMap<Root, Node>` and consults it on every `pair`
  construction. Their measurement: a 30% reduction in heap
  usage on a `BeaconState` archive workload (storing 100
  consecutive states), because validator-list prefixes are
  highly redundant across slots.
* Lighthouse-Milhouse holds back from hash-consing because the
  Rust-side ref-counted persistent tree already shares spines
  intra-state; the inter-state win is the lever.

**Microbenchmark target.** Memory: storing N consecutive
`BeaconState`s should use proportionally less heap than `N ×
fresh-state` once `N ≥ 50`. CPU: a `merkleRootWithCache` hit on
an interned `Node` should be the same `pair _ _ (some r)` short-
circuit it is today, no extra work on the hot path.

**Proof-side invariant.** Pure cache substitution. `Sha256Spec`
/ uncached / plain-`T` paths never allocate `Node` cells; the
hash-cons cache is invisible to them. Two `Node` values that
hash-cons to the same allocation must be observationally
indistinguishable (`merkleRoot` and `setAt` agree on both);
that's automatic since interning happens only when the cached
root is *already* known.

**Risk.** Medium. Lean's runtime reference-counting interacts
with weak references non-trivially. Getting the lifecycle right
needs care, a `WeakRef` API would be cleaner, but Lean
currently lacks one. The fallback is a bounded-LRU cache (no
weak references), which loses the unbounded-archive case but
keeps the common-case win.

### Stage 17d: Profile-guided `@[specialize]`: **shipped (pass 1); pass 2 measured, no hints kept**

**Shipped.** `@[specialize]` attributes on the three
deriving-handler-emitted user-facing surfaces in
`SizzLean/Repr/Class.lean`: `SSZ.serialize`, `SSZ.deserialize`,
`SSZ.hashTreeRoot`. The compiler now monomorphises these at
each consensus type that calls them.

**Measured result.** On a `ValidatorShape` fixture (eight
fixed-size fields, ~144 bytes), 1000 iterations:

| Path | Time |
|---|---|
| **pure (`SSZ.hashTreeRoot Sha256` on plain `T`)** | **~7.4 µs** |
| cached (`TreeBacked.ofValue + .hashTreeRootCached`) | ~8.5 µs |

Pure wins by ~1 µs because the cached path adds `TreeBacked.ofValue`'s
`Node.ofShape` construction cost on every iteration. The
cache is for amortising across *multiple* reads on the same
value, which this single-shot bench doesn't exercise. For the
ValidatorShape's size, the post-`@[specialize]` baseline is
recorded; future hint changes compare against these columns.

**Pass 2: profiled, and no hint earns its place.** The profiling
the pass-1 note asked for is now done, on a real workload, and it
says the hints do not pay. The tool is
`packages/EthCLSpecs/EthCLSpecsBench/`, driven by

```
just ethcl-profile            # the Gloas mainnet sanity/blocks case
just ethcl-profile <case-dir> # any extracted vector directory
```

It decodes an upstream **Gloas mainnet** `sanity/blocks` vector (a
3.17 MB `BeaconState`, 256 validators) and times each SSZ operation
per container type. The TSV it writes shares
`SizzLeanBench.Runner`'s column shape, so
`just sizzlean-bench-diff` compares two profiles.

**Where the time goes** (median of 20 samples,
`bench/specs-profile-20260912T041020Z.tsv`; per-type rows cover 1000
distinct values):

| Row | Median |
|---|---|
| `serialize BeaconState` | 3438.9 ms |
| `ForkInterface.runBlocks` (whole vector) | 363.0 ms |
| `ForkInterface.stateRoot BeaconState` | 282.8 ms |
| `FastBox.hashTreeRoot BeaconState` (first root) | 186.6 ms |
| `htr BeaconState` (pure) | 164.7 ms |
| `deserialize BeaconState` | 117.8 ms |
| `htr Attestation ×1000` | 30.3 ms |
| `deserialize Attestation ×1000` | 11.4 ms |
| `serialize Attestation ×1000` | 10.7 ms |
| `htr Validator ×1000` | 7.5 ms |
| `htr BeaconBlockHeader ×1000` | 7.3 ms |
| `serialize BeaconBlockHeader ×1000` | 4.5 ms |
| `serialize Validator ×1000` | 4.2 ms |
| `deserialize BeaconBlockHeader ×1000` | 4.3 ms |
| `deserialize Validator ×1000` | 3.8 ms |
| `htr Checkpoint ×1000` | 2.2 ms |

**How to read these numbers.** Absolute medians track what else the
machine is doing: a repeat run with one competing CPU-bound process
moved every row, touched or not, by about 28%. So compare rows *within*
one run, and compare a change against a paired run taken back to back
on the same machine. That is how the hint experiment below was
measured.

**The dispatch a hint would remove costs nothing measurable.** Two
rows price it directly. `ForkInterface.stateRoot` runs through the
seam the pyspec driver uses, where the preset arrives as a runtime
value and every `SSZRepr` instance resolves through a dictionary. The
`deserialize BeaconState` and `htr BeaconState` rows do the same two
operations with the preset as a statically known instance:

| Path | Median |
|---|---|
| `deserialize` + `htr`, preset statically known | 117.8 + 164.7 = 282.5 ms |
| `ForkInterface.stateRoot`, preset injected at runtime | 282.8 ms |

The seam costs 0.3 ms on 282 ms, which is 0.1%. There is no dispatch
overhead left for a `@[specialize]` hint to remove.

**The hint experiment, and why it was reverted.** The one genuinely
preset-generic layer in a fork body is the `ForkInterface` implementation
set, whose members take the preset and the config as explicit value
arguments. `@[specialize]` on Gloas's `decodeState`, `stateRootImpl`,
and `runBlocksImpl` is therefore the strongest pass-2 hint available.
Measured back to back on one machine
(`bench/specs-profile-20260912T041020Z-specialize-interface-impls.tsv`):

| Row | No hint | Hinted | Change |
|---|---|---|---|
| `ForkInterface.stateRoot BeaconState` | 282.8 ms | 281.5 ms | −0.5% |
| `ForkInterface.runBlocks` (whole vector) | 363.0 ms | 360.0 ms | −0.8% |

Both moves sit inside this machine's run-to-run drift. Rows no hint
can touch move further across the same pair: `deserialize
BeaconBlockHeader ×1000` by +4.7%, `deserialize Attestation ×1000` by
−2.5%. Three repeat runs per configuration put the spread at roughly
±2%, so a 0.5% move is not a win. Under this section's own rule, keep
a hint only when it shows a win, the hints are reverted and pass 2
lands no annotation.

**Why the ceiling is this low.** Pass 1 already removed the
instance dispatch at the three entry points, and the cost that
remains inside them is the `SSZType` interpreter walking a *runtime
value*: `SSZ.hashTreeRoot` dispatches on `r.shape`, a term, not on a
type. No attribute monomorphises a function over a value argument.
Removing that layer needs the shape resolved at elaboration time,
which is a change to the deriving handler's output rather than an
annotation, and a separate stage.

**What the profile found instead: `serialize` is quadratic in
element count.** The largest row is not a dispatch cost at all.
`serialize BeaconState` takes 3.4 s, 21 times the 164.7 ms its
hash-tree-root costs, for a 3.17 MB value. `SSZType.serializeFixedElems`
(`Spec/Serialize.lean`) is a right fold of `ByteArray.append`:

```lean
| t, x :: xs => SSZType.serialize t x ++ SSZType.serializeFixedElems t xs
```

Every `++` copies the whole accumulated suffix, so a vector of `n`
fixed-size elements copies `O(n²)` bytes. `BeaconState.randaoMixes` is
a `Vector Bytes32 65536` at mainnet, which alone accounts for tens of
gigabytes of copying. The fix is an accumulator that appends into one
buffer, and it belongs to a SizzLean stage of its own: the function
carries proof obligations, and the change is library-side, outside
this sub-stage's scope. Recorded here as the profile's finding, with
its measurement, rather than folded into pass 2.

**Original design notes follow.**

**What it does.** Monomorphise the `SSZType`-driven generic
interpreter at the concrete consensus types that dominate the
profile. Each specialization removes one level of dispatch
overhead. The `Spec/HashTreeRoot.lean` recursion is currently
polymorphic in `s : SSZType`, and the generic code path pays a
dispatch tag check at every constructor.

**Data structure.** Pure attribute changes; no new module.

* `@[specialize]` annotations on the generic functions surfaced
  by the deriving handler (`packages/SizzLean/SizzLean/Repr/Deriving.lean`).
* `@[specialize SSZ.hashTreeRoot]`-style hints in the
  consensus-spec containers, which go in `EthCLSpecs`.

**Prior art.**

* `remerkleable` does not specialise (Python; nothing to
  monomorphise). The pattern is borrowed from Lean's own stdlib
  (`Array.usize`, `USize.repr`) and from Coq's `Extraction
  Inline`.
* `gohashtree` and `fastssz` (the Go implementations) get the
  same effect via Go's per-call-site inlining, which is
  automatic; we need the explicit annotation because Lean's
  compiler is more conservative.

**Microbenchmark target.** At least one hot-path consensus type
(`Validator`, `BeaconBlockHeader`, `BeaconState`'s per-fork
variants) shows a measurable encode/decode/root-cost win after
the specialization. Realistic target: 1.5–2× on a single-type
microbench.

**Proof-side invariant.** Critical. `@[specialize]` is a
*recommendation to the compiler*; Lean's kernel still sees the
unspecialised definition for proof reduction. `rfl` / `decide`
close identically before and after. This is why 17d is the
only sub-stage that can touch shared deriving-handler output
without breaking the cross-stage invariant, the attribute
lands at runtime, not at proof-check time.

**Risk.** Low. `@[specialize]` is a hint; worst case it's
ignored by the compiler. No correctness consequence.

### Stage 17e: Fused commit walk + pre-cached `Node.ofShape` builders: **shipped**

**Shipped.** Two related optimisations that fuse work and trim
allocations on the cache layer's hot path:

* **`Node.commitAndHash`** (`Cache/MerkleTree/SetAt.lean`):
  replaces the two-pass `setManyAt` → `merkleRootWithCache`
  sequence at commit time. One walk over the touched spine; each
  cell allocated once with its root computed inline.
  `commitAndHash` is what `hashTreeRootCached` calls when
  `pending` has writes; an empty overlay falls through to plain
  `merkleRootWithCache`.
* **Pre-cached `Node.ofShape` builders.** `Node.ofLeaves`,
  `Node.ofSubtrees`, `Node.mixInLength` now compute the parent's
  root inline (via `Node.rootOf` on the children, O(1) when the
  child is cached) and embed it as `(some root)` in the parent
  pair. A subsequent `merkleRootWithCache` on a fresh
  `Node.ofShape` output short-circuits at the top in O(1).

The serialisation cache originally planned for 17e was dropped:
`TreeBacked.serialize` is a pure function of `view`, with no
internal memo. Callers that need to broadcast the same bytes to
many consumers bind the result once and reuse it. The historical
design notes for that approach follow at the end of this section.

**Measured result.** S6 BlockProcessingLarge cached vs pure
moves from a 1.5× ratio (pre-fusion) to a 2.4× ratio
(post-fusion); the fused walk eliminates the per-spine duplicate
allocation that previously dominated S5's write-heavy column.

Coherence preserved: every cached-path coherence test
(`TreeBackedCoherence`, `PendingOverlayCoherence`,
`MultiSetterIndex`, `PendingPrefixConflict`, `PendingListShrink`,
`WidthsAndLists`) closes unchanged across the fusion.

**Historical design notes (serialisation cache, dropped) follow.**

**What it does.** Add an `Option ByteArray` slot to
`TreeBacked` that caches the most-recently-computed
serialisation. Any `setField` invalidates the slot; `SSZ.serialize`
consults the slot first. This is the targeted optimisation for
the gossip layer: re-encoding an unchanged block to push it
upstream becomes a `byte-copy` rather than a re-walk of the
tree.

**Data structure.** Extend the existing structure in
`Cache/TreeBacked.lean`:

```lean
structure TreeBacked (H T : Type) [Hasher H] [SSZRepr T] where
  view       : T
  tree       : Node
  serialized : Option ByteArray   -- new
```

* `TreeBacked.ofValue` sets `serialized := none`.
* `setField` and the `sszUpdate` cached emission set
  `serialized := none` on the result.
* `SSZ.serialize` is taught to check `t.serialized` first; if
  populated, the byte-copy returns immediately; otherwise the
  spec serialiser runs and the result is written back into the
  slot.

**Prior art.**

* `remerkleable` has a `to_obj` convention but does not cache
  the bytes. Adding the cache here is an Ethereum-specific
  optimisation aimed at the gossip layer (where the same block
  is re-encoded for every peer).
* Lighthouse's Beacon API cache and Lodestar's `messageBytes`
  cache do exactly this, a byte-form pinned to the SSZ value,
  invalidated on mutation. The invariant they maintain ("if
  `serialized = some b`, then `SSZ.serialize view = b`") is the
  one we're lifting.

**Microbenchmark target.** A microbench in `bench/` showing
that 1000 re-encodes of an unchanged `BeaconState` use O(bytes)
work instead of O(tree size).

**Proof-side invariant.** The new field is on `TreeBacked` only.
`UncachedSSZ` and `SSZ.PureBox` paths don't see it; the spec
`SSZ.serialize : T → ByteArray` on a plain `T` value doesn't
either. The cache is consulted only inside the cached
representation's serializer; the proof-side semantics is
unchanged.

**Risk.** Low. Mostly mechanical. The one wrinkle is `sszUpdate`:
the emission path on the cached side currently writes
`{ t with view := …, tree := … }`; it now writes
`{ t with view := …, tree := …, serialized := none }`. That's
one extra field per emission, fine.

## The cross-stage invariant: the pure path stays kernel-reducible

The whole point of `SSZ.PureBox` / `UncachedSSZ` / plain `T`
operating through `SSZ.hashTreeRoot Sha256Spec` is that proofs
about state-transition functions reduce in the Lean kernel
*with no cache invariant to thread through, no FFI to trust, no
opacity to hide behind `native_decide`*. Every Phase 17
optimisation preserves that property:

| Stage | Why the pure path is unaffected |
|---|---|
| 17a Overlay | Touches `TreeBacked` directly. `UncachedSSZ` has no spine to defer; plain `T` doesn't have a pending-writes map either. |
| 17b Batched SHA-256 | Wired as an `@[implemented_by]` swap on `merkleRootWithCache` (or behind `Hasher Sha256`). The abstract `Hasher` typeclass and the `Sha256Spec` instance are unchanged. |
| 17c Hash-consing | Operates on `Node` allocations behind a per-box flag. The pure spec path doesn't allocate `Node`s, it hashes through the `SSZType` recursion directly. |
| 17d `@[specialize]` | Compile-time recommendation. Lean's kernel sees the unspecialised definition for proof reduction; `rfl` / `decide` close identically before and after. |
| 17e Serialised cache | Slot on `TreeBacked` only. `UncachedSSZ` doesn't have it; `SSZ.serialize` on plain `T` doesn't consult it. |

Concretely: a theorem like `(bumpEpoch (SSZ.PureBox f0) 42).view
= { f0 with epoch := 42 }` closes by `rfl` today. After any or
all of 17a–e land, it must still close by `rfl`. Any change to
a Stage 17 deliverable that breaks that test belongs in a
different stage with a separate trust budget.

## Benchmarking and gating

Every Stage 17 sub-stage ships a microbenchmark in
`packages/SizzLean/SizzLeanBench/Scenarios/` showing before /
after numbers for its specific lever. The phase-wide target is
parity with `fastssz` on encode/decode and with `gohashtree` on
cached `hash_tree_root` (per ARCHITECTURE.md §2), but no
individual sub-stage carries that as its gate, each closes when
its specific optimisation lands with a measured win.

The bench scenarios:

| # | Scenario | Fixture | What it measures |
|---|---|---|---|
| S1 | ColdRoot | Validator / VS16 | First-walk overhead on small fixtures |
| S2 | BatchedWrites | Validator / VS16 | One slot's worth of writes + one root, small fixture |
| S3 | BlockProcessing | Validator / VS16 | 8 slots × (4 writes, root, serialise), small fixture |
| S4 | ColdRootLarge | VS256 | First-walk overhead at depth 12 |
| S5 | BatchedWritesLarge | VS256 | 512 writes + one root |
| S6 | BlockProcessingLarge | VS256 | 32 slots × (8 writes, root, serialise), best single-number predictor of the cache win at scale |
| S7 | FuluStateTransition | `SizzLeanBench.Fulu.BeaconState` (mainnet preset, ~1024 validators) | Full state-transition simulation touching every major field shape |

Headline cached vs pure ratios on dev hardware:

* **S6 BlockProcessingLarge**: ~2.4× cached faster than pure
  (43 ms vs 102 ms); the production-shaped large workload.
* **S7 FuluStateTransition**: ~2.0× cached faster than pure
  (2.6 s vs 5.2 s); the realistic mainnet-shape regression gate.

S7's `BeaconState` types live in `SizzLeanBench/Fulu.lean` as a
bench-local reference copy so `SizzLeanBench` doesn't need an
`EthCLSpecs` dependency (`EthCLSpecs` already depends on
`SizzLean`, so the reverse would close a cycle).

The default ordering above is highest-impact-first per
Lighthouse and Lodestar benchmarks; profiling on a specific
workload may justify reordering. **Do not start a sub-stage
until a measurement says it's the next bottleneck on your
workload**. The cache backbone (Phase 14) is already enough
for most pipelines, and any of 17a–e adds maintenance surface
that should be paid for by measured gain.

## Where to find what

| Concern | File |
|---|---|
| `Node` representation, cache slot | `Cache/MerkleTree/Node.lean` |
| `ZERO_HASHES` table + `zeroLeaf` | `Cache/MerkleTree/Zero.lean` |
| `merkleRootWithCache`, `merkleRoot` | `Cache/MerkleTree/Merkle.lean` |
| `gindexBits`, `setAt`, `setManyAt`, `asLeafArray` | `Cache/MerkleTree/SetAt.lean` |
| `Node.ofShape`, `mixInLength`, `subtreesFor*` | `Cache/MerkleTree/Build.lean` |
| `TreeBacked` / `CachedSSZ` structure + accessors | `Cache/TreeBacked.lean` |
| `UncachedSSZ` (internal, see its prominent warning) | `Cache/Uncached.lean` |
| `SSZ.Box` + four smart constructors | `Cache/Box.lean` |
| `sszUpdate` / `sszGet` macros + elaborator | `Cache/Update.lean` |
| Coherence property test | `SizzLeanTests/TreeBackedCoherence.lean` |
| Setter / index property tests | `SizzLeanTests/TreeBackedSetField.lean`, `MultiSetterIndex.lean` |
| Cache research notes (deeper rationale) | [`research/cache-research.md`](research/cache-research.md) |
| SizzLean microbenchmarks (`just sizzlean-bench`) | `SizzLeanBench/` |
| Consensus container profile (`just ethcl-profile`) | `packages/EthCLSpecs/EthCLSpecsBench/` |
| Bench and profile TSVs | `bench/` |
