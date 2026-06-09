import Std.Data.TreeMap
import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Cache.MerkleTree.SetAt
import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Cache.TreeBacked`: the **fast (cached) backend**

This file is the home of `CachedSSZ H T`, the **fast** branch
of the two-backend story documented in `Cache/Box.lean`. The
companion **pure (uncached)** backend lives in
`Cache/Uncached.lean`; `Cache/Box.lean`'s `SSZ.Box` sum closes
the two together and defines the four user-facing smart
constructors (`SSZ.FastBox` / `SSZ.PureBox` and the
hasher-explicit `SSZ.CachedBox` / `SSZ.UncachedBox`). Start with
`Cache/Box.lean`'s module docstring for the brand framing.

ARCHITECTURE.md §6.3. The user-facing pairing of a Lean value
`view : T` with a `Node`-shaped Merkle backing
`tree : Node`. The smart constructor `TreeBacked.ofValue` builds the
tree from a value; `hashTreeRootCached` returns the cached root in
constant time on a fully-cached tree.

## Coherence invariant

`hashTreeRootCached t = SSZ.hashTreeRoot t.view` for every
`t : TreeBacked H T`. This is *maintained by the smart constructors*,
not encoded as a Lean proposition. The value/tree coupling can
diverge under a hand-rolled `TreeBacked.mk` without it being a
type error. Smart constructors plus the acceptance property test
(`Conformance/TreeBackedCoherence.lean`) are the discipline.

## Hasher pinning + parameter order

`TreeBacked H T` carries the hasher `H` in the *type*: the tree was
built with `H`'s `combine` operation, and every subsequent update
must use the same `H` or the cache slots go out of sync with the
spec's root. Encoding `H` in the type makes wrong-hasher use a
type error rather than a silent root mismatch. The user picks `H`
once at `ofValue` time, and downstream `sszUpdate` /
`hashTreeRootCached` calls infer it from the value's type.

The hasher `H` comes *first* in the parameter order so a
particular `H` can be partially applied to yield a single-arg type
constructor: `abbrev Sha256Cached (T : Type) [SSZRepr T] :=
TreeBacked Sha256 T` becomes the natural shortcut for the common
case of fixing one hasher across many content types.

## How the tree is built

`ofValue` delegates to `Node.ofShape` (in `MerkleTree/Build.lean`),
which walks the SSZ shape from `r.shape` and the value's
`SSZType.interp r.shape` projection, producing a `Node` whose
interior structure mirrors the SSZ shape:

* Container fields → balanced sub-trees with one leaf (or sub-tree)
  per field.
* Composite-element vectors / lists → balanced sub-trees with one
  sub-tree per element.
* Basic-element vectors / bitvectors → chunk-packed bytes as
  leaves, exactly matching the spec's `merkleize` shape.
* `bitlist` / `list` → wrap the body sub-tree with a
  `mix-in-length` sibling.

Each interior `pair` starts with `cache = none`; the first call to
`merkleRootWithCache` fills every cache slot on its walk. Subsequent
field-mutation operations invalidate only the spine, leaving
off-path cached roots intact. This is the cache layer earning
its name.

## When the cache short-circuits

After one full root walk, the entire tree is cached. A subsequent
`hashTreeRootCached` returns in O(1) (one `.leaf` / `.pair` cache
read). After a single field mutation, `merkleRootWithCache` walks
only the dirty spine, O(depth) hashes, because every off-path
`pair` still carries its cached root.

## Lean idioms used here (annotated on first appearance)

* `Thunk α` (Lean core): a one-shot lazy value. `Thunk.mk
  (fun _ => e)` wraps `e` unevaluated; the first `Thunk.get`
  forces it, the result is memoised on the heap, and every
  subsequent access returns the cached result. Used below to
  defer the initial `Node.ofShape` build until the first root
  read, so a `TreeBacked` that's only inspected on the `view`
  side never pays for tree construction.
* `Std.TreeMap k v` (from `Std.Data.TreeMap`): a sorted-key
  immutable map backed by a balanced tree; `insert` and
  iteration in key order are both O(log n). Used as the
  `pending` accumulator below, keyed by gindex so the
  `setManyAt` walk receives writes in ascending tree position.
* `@[specialize]` (used on hot helpers further down): tells the
  compiler to monomorphise this function for each concrete type
  it is applied to at call sites. The polymorphic-Lean fallback
  reads the typeclass dictionary at runtime; the specialised
  copy inlines it, removing the dispatch.
* `abbrev`: a reducible `def` that the elaborator unfolds
  transparently during typeclass synthesis and dot notation.
  Used for the user-facing alias `CachedSSZ` below.

## Pending-overlay: deferred tree-side writes

Each `TreeBacked` carries a third field, `pending : Std.TreeMap
Nat Node`, that accumulates tree-side writes from `sszUpdate`
without immediately walking the spine. The `view` side stays
eager: every `sszUpdate` write the user types is reflected in
`view` *immediately* and is observable by `t.view.f` reads.
Only the *tree* side defers. The actual `Node.setManyAt` spine
walk runs on demand inside `commit`, which every root reader
(`hashTreeRootCached`, `serialize`, …) calls automatically
before consulting the cache.

The win is cross-statement batching: a chain
`let s := sszUpdate s with x := 1`, `let s := sszUpdate s with
y := 2`, `let s := sszUpdate s with z := 3`, then
`s.hashTreeRootCached` produces *one* `setManyAt` walk at the
read, not three. The three writes accumulate in `pending` and
are replayed in gindex-ascending order at commit, feeding
`setManyAt`'s partition-by-first-bit step efficient runs.

`treeBase` is the field documented as *pre-commit*; library
code that needs the up-to-date tree shape (root walk,
serialisation, etc.) goes through `committedTree` so the pending
map is always applied first. The two-state shape is named:

* `view`:     always current (eager view-side update).
* `treeBase`: the tree before pending is replayed.
* `pending`:  gindex → replacement subtree, accumulated since
              the last `commit`.

## File placement

This file lives under `SizzLean/Cache/` alongside its sibling
`Cache/Uncached.lean`. The two are parallel implementations of the
cache abstraction: `TreeBacked` is the Merkle-cached production
flavour; `UncachedSSZ` is the pure-Lean proof-friendly flavour.
`SSZ.Box` (`Cache/Box.lean`) is the closed sum that unifies the two
flavours, and the `sszUpdate t with …` syntax (`Cache/Update.lean`)
elaborates to a per-flavour optimal emission. -/

set_option autoImplicit false

namespace SizzLean.Cache

open SizzLean.Hasher

open SizzLean.Cache.MerkleTree
open SizzLean.Spec

/-- A pending tree-side write: a closure that, at commit time,
extracts the relevant sub-value from the **current** `view : T`
and builds the matching sub-tree via `Node.ofShape`. Returns
`Option Node` so the closure can signal `none` for writes that
ended up as no-ops on the view side (e.g. an `xs[i] := v`
whose `i` is out-of-bounds, `Array.set!` silently leaves the
array unchanged, and the cache must mirror that decision).

Reading the value from `view` at commit (rather than capturing
it at insert time) is what makes overlapping parent/child writes
mutually consistent. Two `sszUpdate` statements with a strict-
prefix gindex relation both leave entries in `pending`; at
commit, each entry's closure projects the latest sub-value out
of `view`, so the parent's sub-tree already incorporates every
later child override and vice-versa. The downstream
`commitAndHash` rule that drops a non-empty-path entry when an
ancestor (`[]`-path) entry is at the same level then becomes a
correct optimisation, because the ancestor's sub-tree is built
from a `view` that already reflects the child write.

The `Option` return also handles **stale index entries** when a
later write shrinks the surrounding list. The macro-emitted
closure walks the same projection path the user wrote; for any
index step `xs[i]`, it emits a bounds check (`i < xs.size`) and
returns `none` when the index is OOB. Combined with the
`view`-side `Array.set!` no-op semantics, this keeps the cache
in lockstep with the view regardless of the element type's
`Inhabited` default.

Parameterised by the container type `T` of the owning
`TreeBacked`. The closure's input has type `T`; the output is
`Option Node`. -/
def PendingWrite (T : Type) : Type := T → Option Node

/-- A value `view` paired with a `Node`-shaped Merkle backing
`treeBase`, plus a deferred-write overlay (`pending`) that
batches `sszUpdate`s between root reads. Parameterised by the
hasher `H` that produced any cache slots in `treeBase`; pinning
`H` in the type prevents combining caches built with different
hashers. The coupling between `view`, `treeBase`, and `pending`
is maintained by smart constructors, not by a Lean-level
invariant proof.

The deferred overlay is what makes the cache layer faster than
eager-tree designs: by collecting writes into `pending` first,
the eventual `hashTreeRoot` walk does *one* `setManyAt` that
shares spine allocations across all writes, instead of N
independent walks per write. Overwritten writes (where
`TreeMap.insert` replaces an entry at the same gindex) save
their `Node.ofShape` cost entirely. The dropped `PendingWrite`
closure goes to GC without ever running. -/
structure TreeBacked (H : Type) (T : Type) [Hasher H] [SSZRepr T] where
  /-- The user-observable Lean value. Always current; every
  `sszUpdate` write reflects here immediately. -/
  view : T
  /-- The Merkle-tree backing, *before* the pending overlay is
  applied. Wrapped in `Thunk` so the initial `Node.ofShape` build
  is deferred to the first `hashTreeRoot` call. After the first
  walk, `treeBase` holds a `Thunk.pure cachedTree` with cell-level
  cache slots filled. Repeat reads of the post-commit `TreeBacked`
  hit the top-level `.pair _ _ (some r)` arm of
  `merkleRootWithCache` and short-circuit in O(1). -/
  treeBase : Thunk Node
  /-- Pending tree-side writes accumulated since the last commit.
  Keyed by gindex (ascending order is the natural feed for
  `Node.setManyAt`'s partition-by-first-bit step). Each entry is
  a closure `view → Node` that, at commit time, reads the latest
  sub-value out of `view` and builds the sub-tree via
  `Node.ofShape`. The view-driven materialisation is what keeps
  parent/child overlapping writes consistent. See
  `PendingWrite`. -/
  pending : Std.TreeMap Nat (PendingWrite T) := {}

/-- `CachedSSZ H T` is the *public-facing* name for a cached SSZ-
encoded value of `T` hashed with `H`. Implementation-wise it is
exactly `TreeBacked H T` (an `abbrev`, so the two are definitionally
equal and either name accepts the other), but it reads as a
value-level abstraction, *"a cached SSZ value"*, without
committing the reader to the Merkle-tree mechanism that underpins
the cache.

Library code that talks about the cache mechanism (cache slots,
gindex paths, `Node.setManyAt`) uses `TreeBacked`; library code
exposed to users prefers `CachedSSZ`. Both live in
`SizzLean.Cache`; pick whichever fits your audience. -/
abbrev CachedSSZ (H T : Type) [Hasher H] [SSZRepr T] := TreeBacked H T

namespace TreeBacked

/-- Convert a gindex bit-path back to a `Nat` gindex. Used by
`setAtBits` and `addPendingMany` to project the bit-path
representation (which the spec functions use) into the
`pending`-map key space. The conversion is the inverse of
`gindexBits`: a leading `true` bit marks the implicit `2^depth`,
the remaining bits are the level-by-level path. -/
private def gindexOfBits (bits : List Bool) : Nat :=
  bits.foldl (init := 1) fun acc b => if b then 2 * acc + 1 else 2 * acc

/-- Build a `TreeBacked H T` from a plain `T`. The hasher `H` is
pinned into the result's type. The initial tree is deferred
inside `treeBase : Thunk Node`. The `Node.ofShape` build runs
on the first `hashTreeRoot` call and is memoised by the `Thunk`
for all subsequent accesses. -/
def ofValue (H : Type) [Hasher H] {T : Type} [r : SSZRepr T] (v : T) :
    TreeBacked H T :=
  { view := v
    treeBase := Thunk.mk (fun _ => Node.ofShape H r.shape (r.toRepr v))
    pending := {} }

/-- Accumulate one tree-side write into `pending` and update
`view` eagerly. The `PendingWrite` closure is invoked against
the *latest* `view` at commit time, so the value it sees always
matches the final user state, even when intervening writes
modified ancestors or descendants of `g`. Overwritten closures
(at the same gindex `g`) are dropped before they ever run; the
`TreeMap.insert` dedup saves real `Node.ofShape` work, not just
a result we'd compute and discard. -/
def addPending {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) (g : Nat) (d : PendingWrite T) (newView : T) :
    TreeBacked H T :=
  { view := newView
    treeBase := t.treeBase
    pending := t.pending.insert g d }

/-- Accumulate many tree-side writes in one go. The macro emits
this for multi-clause `sszUpdate` statements; the clauses are
folded into `pending` keyed by gindex, with "most recent wins"
semantics matching `TreeMap.insert`'s replace-on-key behaviour. -/
def addPendingMany {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) (updates : List (List Bool × PendingWrite T)) (newView : T) :
    TreeBacked H T :=
  let newPending := updates.foldl (init := t.pending) fun acc (bits, d) =>
    acc.insert (gindexOfBits bits) d
  { view := newView
    treeBase := t.treeBase
    pending := newPending }

/-- Cached Merkle root of `t`, plus an updated `TreeBacked` that
*commits the read*: `pending` is materialised into `treeBase` via
`setManyAt`, then the tree is walked once via
`merkleRootWithCache` to fill cell-level cache slots. `pending` is
emptied in the returned value; `treeBase` becomes `Thunk.pure
cachedTree` so subsequent reads on the post-commit `TreeBacked`
hit the top-level `.pair _ _ (some r)` arm in O(1).

This is the *single* tree-walk for the whole batch, the cross-
statement amortisation that makes deferred-update designs
substantially faster than eager-tree at scale. Threading the
returned value forward is the user's responsibility:
`let (root, t) := t.hashTreeRootCached`. -/
def hashTreeRootCached {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) : ByteArray × TreeBacked H T :=
  let base := t.treeBase.get
  let (root, cachedTree) :=
    if t.pending.isEmpty then
      -- No updates: just fill cache slots if needed (O(1) at the
      -- top when `base` is already cached).
      base.merkleRootWithCache H
    else
      -- Run each `PendingWrite` closure against the latest
      -- `view`. Closures returning `none` are dropped here (the
      -- write turned out to be a no-op on the view side, most
      -- commonly an OOB index whose `Array.set!` silently did
      -- nothing). Surviving `some` entries materialise into
      -- sub-trees to commit at their respective gindices.
      --
      -- Because every closure shares one `view`, overlapping
      -- parent/child writes are mutually consistent: a parent's
      -- sub-tree already incorporates any later child overrides
      -- (extracted from the same `view`), and `commitAndHash`'s
      -- "drop deeper write at the same level as a whole-
      -- replacement" rule then drops the redundant child entry
      -- without loss of information.
      let updates := t.pending.toList.filterMap fun (g, d) =>
        (d t.view).map fun n => (gindexBits g, n)
      if updates.isEmpty then base.merkleRootWithCache H
      else base.commitAndHash H updates
  (root, { t with
            treeBase := Thunk.pure cachedTree,
            pending := {} })

/-- SSZ-serialise `t.view`. A pure function of `t.view`, no
state change, no return of a new `TreeBacked`. Callers that need
to broadcast the same bytes to many consumers should bind the
result once (`let bs := t.serialize`) and reuse it; the library
doesn't memoise inside the box because (a) the user owns the
lifetime decision better than the library does, and (b) the
`serialize` operation is genuinely a read with no work to commit,
so the return type matches. -/
def serialize {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) : ByteArray :=
  SSZ.serialize t.view

/-! ## Generic gindex-driven field updates

These helpers are agnostic to the specific container type. They
work on any `T` with an `SSZRepr` instance. The `sszUpdate` term
elaborator (in `Cache/Update.lean`) routes through them on the
cached path.

* `setFieldAt t N k newSub newView`: gindex
  `2 ^ chunkDepth(N) + k`, container with N fields, field index k.
* `setAtBits  t bits newSub newView`: pre-composed path bits for
  nested updates (e.g. vector position inside a container field).
-/

open SizzLean.Cache.MerkleTree
open SizzLean.Spec

/-- Update the k-th field of a container-backed `TreeBacked H T`.
Accumulates one pending entry; the spine walk is deferred to the
next `commit`. See the comment block above for the gindex
convention. -/
def setFieldAt {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) (fieldCount : Nat) (k : Nat)
    (newSubtree : PendingWrite T) (newView : T) : TreeBacked H T :=
  let g := 2 ^ chunkDepth fieldCount + k
  t.addPending g newSubtree newView

/-- Like `setFieldAt`, but the caller supplies the path bits
directly. Used for *nested* updates (e.g. an element inside a
vector inside a container) where the gindex path is the
concatenation of the outer and inner paths. -/
def setAtBits {H T : Type} [Hasher H] [SSZRepr T]
    (t : TreeBacked H T) (bits : List Bool)
    (newSubtree : PendingWrite T) (newView : T) : TreeBacked H T :=
  t.addPending (gindexOfBits bits) newSubtree newView

end TreeBacked

/-! ### `CachedSSZ` namespace: user-facing aliases

`CachedSSZ` is an `abbrev` for `TreeBacked`, so dot notation
(`s.tree`, `s.view`) and instance lookup already see through it.
Lean's namespace resolution, however, does *not* follow the
abbrev when looking up `CachedSSZ.ofValue`. You'd land in
`TreeBacked.ofValue` only by typing `TreeBacked` directly. The
two short aliases below restore the symmetry with
`UncachedSSZ.ofValue` / `UncachedSSZ.hashTreeRoot` so one-flavour
user code never has to mention `TreeBacked` (the internal name)
or the `hashTreeRootCached` suffix. -/

namespace CachedSSZ

/-- Build a `CachedSSZ H T` from a plain `T`. Alias of
`TreeBacked.ofValue` exposed on the user-facing namespace. -/
def ofValue (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    CachedSSZ H T :=
  TreeBacked.ofValue H v

/-- Cached Merkle root of `s`. Same as `TreeBacked.hashTreeRootCached`;
the alias drops the `Cached` suffix so the call mirrors
`UncachedSSZ.hashTreeRoot` and the dot-notation `s.hashTreeRoot`
reads identically across both flavours. -/
def hashTreeRoot {H T : Type} [Hasher H] [SSZRepr T] (s : CachedSSZ H T) :
    ByteArray × CachedSSZ H T :=
  s.hashTreeRootCached

end CachedSSZ

end SizzLean.Cache
