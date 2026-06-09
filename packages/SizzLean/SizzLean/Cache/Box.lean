import SizzLean.Hasher.Class
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Hasher.Sha256

/-!
# `SizzLean.Cache.Box`: closed sum over the cache flavours

A single inductive type that wraps *either* the production cache
(`CachedSSZ H T`) *or* the proof-side cache (`UncachedSSZ H T`).
Spec code that needs to operate uniformly on both flavours takes
an `SSZ.Box H T` argument and pattern-matches; the `sszUpdate`
macro recognises the type and expands to a two-arm match
automatically.

## A closed two-constructor sum

`Box` is a plain inductive with exactly two constructors, so the set
of cache flavours is *closed* and dispatch is resolved at compile
time:

* The two constructors enumerate the entire design space, so the
  `sszUpdate` elaborator's two-arm match is exhaustive, every call
  site is handled at compile time, with no instance-resolution
  machinery in the way.
* Dispatch exposes no Merkle-shaped `Patch` field in a public
  interface: each arm rewrites a *concrete* cache type, so the cache
  representation never leaks past the `Box`.
* `sszUpdate s with f := v` on an `SSZ.Box H T` expands to:
    `match s with`
    `| .cached t   => .cached (sszUpdate t with f := v)`
    `| .uncached t => .uncached (sszUpdate t with f := v)`
  so the cached arm keeps its O(log N) spine-sharing update and the
  uncached arm keeps its trivial struct rewrite.

## Trade-off

The flavour set is closed by design: a new flavour would mean adding
a constructor to `Box` plus an arm to the `sszUpdate` box emission.
Production (cached) and proof (uncached) are the two required, and
fixing them at the type level keeps the dispatch exhaustive.

## Smart-constructor naming

Four Sha256-pinned and hasher-explicit constructors live below:
`SSZ.FastBox` / `SSZ.PureBox` (Sha256-pinned shortcuts) plus
`SSZ.CachedBox` / `SSZ.UncachedBox` (hasher-explicit forms). The
underlying raw cache types `CachedSSZ H T` / `UncachedSSZ H T`
are the right name when a function specialises to one flavour
and skips the box wrapper entirely. `Box` is the right name when
the function is flavour-generic and wants the two-arm dispatch.
-/

set_option autoImplicit false

namespace SizzLean.Cache

open SizzLean.Hasher
open SizzLean.Spec (SSZError)

namespace SSZ

/-- An SSZ-encoded `T` value in *one of two flavours*: the cached
production layer (`CachedSSZ H T`) or the uncached proof layer
(`UncachedSSZ H T`). Spec functions that should work over either
take `SSZ.Box H T` and pattern-match; the `sszUpdate` macro
recognises the type and expands to a two-arm match.

The two constructors enumerate the entire flavour space, closed-
world, so a `match s with | .cached _ | .uncached _` is provably
exhaustive at compile time.

Type parameters:
* `H`: the hasher tag, kept parametric so post-quantum hashers
  (Poseidon2, …) can plug in without changing the user-facing
  type.
* `T`: the Lean value type with an `SSZRepr` instance. -/
inductive Box (H : Type) (T : Type) [Hasher H] [SSZRepr T] where
  | cached   : CachedSSZ   H T → Box H T
  | uncached : UncachedSSZ H T → Box H T

namespace Box

/-- Wrap a value in the cached flavour with an explicit hasher.
The user-facing smart constructors `SSZ.FastBox` (Sha256-pinned)
and `SSZ.CachedBox` (hasher-explicit) are the more ergonomic
entry points. -/
private def ofCached (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    Box H T :=
  .cached (TreeBacked.ofValue H v)

/-- Wrap a value in the uncached flavour with an explicit hasher.
The user-facing smart constructors `SSZ.PureBox` (Sha256-pinned)
and `SSZ.UncachedBox` (hasher-explicit) are the more ergonomic
entry points. -/
private def ofPure (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    Box H T :=
  .uncached (UncachedSSZ.ofValue H v)

/-- Project out the underlying Lean value. Pattern-matches on the
flavour; both arms return the wrapped `t.view`. -/
def view {H T : Type} [Hasher H] [SSZRepr T] : Box H T → T
  | .cached t   => t.view
  | .uncached t => t.view

/-- Hash-tree root, however the wrapped flavour computes it.

The cached arm consumes/produces a fresh `Box` carrying the
committed cache state (post-`setManyAt`, post-`merkleRootWithCache`),
matching `TreeBacked.hashTreeRootCached`'s `(root, t')` signature.
The user threads the returned box forward; subsequent reads on it
hit the `rootMemo` directly. The uncached arm recomputes through
the spec each call and returns `(root, b)` unchanged (no state).

The two flavours are *observationally* equal on the root,
that's the coherence invariant validated by
`Conformance.TreeBackedCoherence`. -/
def hashTreeRoot {H T : Type} [Hasher H] [SSZRepr T] :
    Box H T → ByteArray × Box H T
  | .cached t   =>
      let (r, t') := t.hashTreeRootCached
      (r, .cached t')
  | .uncached t => (t.hashTreeRoot, .uncached t)

/-- SSZ-serialise the wrapped value. Pure function of `box.view`;
no state change, no Box-threading. Callers that need to reuse
the bytes should bind the result once and pass it forward. -/
def serialize {H T : Type} [Hasher H] [SSZRepr T] :
    Box H T → ByteArray
  | .cached t   => t.serialize
  | .uncached t => SSZ.serialize t.view

end Box

/-! ## Smart constructors for building an `SSZ.Box`

Four user-facing entry points, all returning an `SSZ.Box`:

* `SSZ.FastBox v`: cached flavour, Sha256-pinned (the production
  default, FFI-hashed, O(log N) updates).
* `SSZ.PureBox v`: uncached flavour, Sha256-pinned (the proof-
  friendly default, no cache invariant to thread through
  theorems).
* `SSZ.CachedBox H v`: cached flavour with a caller-chosen
  `Hasher` instance.
* `SSZ.UncachedBox H v`: uncached flavour with a caller-chosen
  `Hasher` instance.

The `Box` suffix is present in all four because the return is
always `SSZ.Box H T`, that's what makes these constructors
substitutable when a spec function takes a single
`SSZ.Box`-typed argument.

### Naming axes

* **`Fast` / `Pure`** are *brands* that bundle a flavour decision
  with the default Sha256 hasher. `Fast` is about runtime cost
  (cached + FFI); `Pure` is about formal status (uncached + no
  coherence invariant). The two adjectives are deliberately on
  different axes, they don't read as Fast-vs-Slow (which would
  undersell the proof side) or Production-vs-Test (which would
  imply `Pure` is only for testing).
* **`Cached` / `Uncached`** describe *only* the cache flavour;
  the hasher is whatever the caller passes in. These are the
  right names when the hasher is the variable: writing
  `FastBox Sha256Spec` would contradict itself (`Fast` already
  implies FFI), but `CachedBox Sha256Spec` reads cleanly.
-/

/-- Build a *cached* `SSZ.Box` over Sha256, the production
flavour. Wraps the value in the structurally-shared Merkle tree,
hashed via the FFI SHA-256 instance, so subsequent root reads
are O(1) and `sszUpdate`s rehash only the path from a changed
field to the root. -/
abbrev FastBox {T : Type} [SSZRepr T] (v : T) : Box Sha256 T :=
  Box.ofCached Sha256 v

/-- Build an *uncached* `SSZ.Box` over Sha256, the proof
flavour. Just stores the view; `hashTreeRoot` runs through the
spec each call, with no cache invariant to thread through
theorems. -/
abbrev PureBox {T : Type} [SSZRepr T] (v : T) : Box Sha256 T :=
  Box.ofPure Sha256 v

/-- Cached `SSZ.Box` over an explicit hasher. Wraps the value in
the structurally-shared Merkle tree, with the caller-chosen
`Hasher` instance at every hash site. Use this when a spec
function is written generic in `H` and a call site needs a
non-default hasher (e.g. `Sha256Spec` for kernel-reducible
proofs of concrete root bytes, or a future Poseidon2 instance). -/
abbrev CachedBox (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    Box H T :=
  Box.ofCached H v

/-- Uncached `SSZ.Box` over an explicit hasher. Just stores the
view; `hashTreeRoot` runs through the spec each call, with the
caller-chosen `Hasher` instance. The companion of `CachedBox`
for hasher-flexible spec functions. -/
abbrev UncachedBox (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    Box H T :=
  Box.ofPure H v

/-! ### Deserialisers: IO-side companions to the four constructors

`SSZ.deserialize` decodes wire bytes into a plain Lean value; each
`*Box.deserialize` below threads the resulting `T` straight into
the matching `Box` flavour. Reads symmetrically with `.serialize`
on a Box: bytes go out via `box.serialize`, come back in via
`SSZ.FastBox.deserialize` (or any of the four flavours below).

Each helper preserves the `Except` shape, a malformed buffer
short-circuits to `.error e` without constructing a Box. -/

/-- Deserialise SSZ bytes straight into a `FastBox`. The IO-side
companion to `SSZ.FastBox v`. -/
def FastBox.deserialize {T : Type} [SSZRepr T] (b : ByteArray) :
    Except SSZError (Box Sha256 T) :=
  (SSZ.deserialize b).map FastBox

/-- Deserialise SSZ bytes straight into a `PureBox`. The IO-side
companion to `SSZ.PureBox v`. -/
def PureBox.deserialize {T : Type} [SSZRepr T] (b : ByteArray) :
    Except SSZError (Box Sha256 T) :=
  (SSZ.deserialize b).map PureBox

/-- Deserialise SSZ bytes straight into a `CachedBox` with the
given hasher. The IO-side companion to `SSZ.CachedBox H v`. -/
def CachedBox.deserialize (H : Type) [Hasher H] {T : Type} [SSZRepr T]
    (b : ByteArray) : Except SSZError (Box H T) :=
  (SSZ.deserialize b).map (CachedBox H)

/-- Deserialise SSZ bytes straight into an `UncachedBox` with the
given hasher. The IO-side companion to `SSZ.UncachedBox H v`. -/
def UncachedBox.deserialize (H : Type) [Hasher H] {T : Type} [SSZRepr T]
    (b : ByteArray) : Except SSZError (Box H T) :=
  (SSZ.deserialize b).map (UncachedBox H)

end SSZ

end SizzLean.Cache
