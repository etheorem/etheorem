import SizzLean.Hasher.Class
import SizzLean.Repr.Class
import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Cache.Uncached`: the **pure (uncached) backend**

This file is the home of `UncachedSSZ H T`, the **pure** branch
of the two-backend story documented in `Cache/Box.lean`. The
companion **fast (cached)** backend lives in
`Cache/TreeBacked.lean` (`CachedSSZ`); `Cache/Box.lean`'s
`SSZ.Box` sum closes the two together and defines the four
user-facing smart constructors (`SSZ.PureBox` / `SSZ.FastBox`
and the hasher-explicit `SSZ.UncachedBox` / `SSZ.CachedBox`).

> ### Most readers should not be here.
>
> `UncachedSSZ H T` is an **internal** type. Direct construction
> (`UncachedSSZ.ofValue Sha256 v`) is rarely the right thing.
> Almost always, what the caller wants is one of:
>
> * **Plain `T`**: for proof-only functions and one-shot consumers.
>   Lean's built-in `{ f with field := v }` does what a wrapped
>   update would, `SSZ.hashTreeRoot Sha256 x` reads roots directly,
>   and there's nothing to thread through theorems. This is the
>   right answer for ~every proof-side function.
> * **`SSZ.PureBox v`**: if the same function body must serve a
>   cached call site too (e.g. you also have a `SSZ.FastBox`
>   caller). Produces `SSZ.Box Sha256 T`; `sszUpdate` works on it.
> * **`SSZ.UncachedBox H v`**: same as `PureBox` but with an
>   explicit hasher (e.g. `Sha256Spec` for kernel-reducible proofs
>   of concrete root bytes).
>
> `UncachedSSZ` itself is left in the public namespace only because
> it has to be reachable from the `.uncached` constructor arm of
> `SSZ.Box`. Nothing in [`MANUAL.md`](../../MANUAL.md) names it.
> Reach for it directly only if you have a reason the three options
> above don't cover.

## What this type does

`UncachedSSZ H T` is the minimal counterpart to `CachedSSZ H T`
(= `TreeBacked H T`): both pair a value-level `view : T` with the
hasher's identity tag `H`, but `UncachedSSZ` *omits* the
`tree : Node` cache and recomputes the hash-tree root through the
spec on every call.

That makes it the right payload for the proof arm of `SSZ.Box`:

* there is no cache invariant to thread through theorems (just
  call `SSZ.hashTreeRoot H t.view`);
* the structure has a single field, so `sszUpdate` reduces to a
  trivial `{ view := newView }` rewrite, the kind of update Lean's
  kernel happily folds during `rfl` / `decide` reasoning.

The runtime cost (re-hash on every observation) is real but
irrelevant in proof contexts, which is the only place this type
should ever appear from user code.

## Parameter order

`H` comes first, parallel to `TreeBacked H T`. The hasher is part
of the type so mixing hashers within one value is a *type error*
rather than a silent root mismatch. The user-facing
Sha256-pinned smart constructor `SSZ.PureBox` (`Cache/Box.lean`)
drops `H` from the call site by defaulting it to `Sha256`; the
underlying `UncachedSSZ` keeps the parameter for the hasher-
explicit form `SSZ.UncachedBox`.

## Why no `tree` field

The whole point: this type has *no caching*. `hashTreeRoot` runs
through the spec via `SSZ.hashTreeRoot H t.view` every time. No
cache invariant exists, so no kernel proof obligation, and Lean's
kernel can reduce all the way to the concrete bytes when the
hasher is itself kernel-reducible (e.g. `Sha256Spec`). The
companion proof-side coherence theorem lives in
`Conformance.TreeBackedCoherence` (in the test library) as an
empirical `native_decide` gate; the uncached side needs no such
gate.
-/

set_option autoImplicit false

namespace SizzLean.Cache

open SizzLean.Hasher

/-- A bare SSZ-valued container tagged with hasher `H`.

Parallel to `TreeBacked H T` (= `CachedSSZ H T`) but with no
Merkle-tree cache, there's only the value-level `view : T`. The
hasher tag `H` is a phantom parameter at the type level: it
appears in the structure header but no field uses it, so the role
of `H` is purely to *select an instance* at the call site (most
notably for `hashTreeRoot` below, which inserts the chosen
`Hasher` instance into the spec call).

See the module docstring for why this type is internal and what
to reach for instead (`SSZ.PureBox`, `SSZ.UncachedBox`, or plain
`T`). -/
structure UncachedSSZ (H : Type) (T : Type) [Hasher H] [SSZRepr T] where
  /-- The wrapped Lean value. `UncachedSSZ` carries nothing else.
  There is no Merkle-tree cache and no precomputed root. Every
  call to `hashTreeRoot` reads through this field and hashes from
  scratch via the spec. -/
  view : T

namespace UncachedSSZ

/-- Build an `UncachedSSZ H T` from a plain `T`. The hasher `H` is
pinned into the result's type at construction, matching
`TreeBacked.ofValue`'s discipline, subsequent operations
(`hashTreeRoot`, `sszUpdate`) recover `H` from the value's type
and never require a separate hasher argument.

User code almost always reaches one level up, through
`SSZ.PureBox v` (Sha256-pinned) or `SSZ.UncachedBox H v`
(hasher-explicit), both of which return `SSZ.Box H T`. Direct
`UncachedSSZ.ofValue` calls live inside the library itself, where
`Cache/Box.lean`'s `Box.ofPure` delegates here. -/
def ofValue (H : Type) [Hasher H] {T : Type} [SSZRepr T] (v : T) :
    UncachedSSZ H T :=
  { view := v }

/-- Hash-tree root of the wrapped value, computed through the spec
each call.

The `H` parameter is inferred from `t`'s type (it was pinned at
`ofValue` time). The chosen `Hasher H` instance is the one
consumed by every internal `combine` / `hash` call: `Sha256`
for FFI hashing, `Sha256Spec` for kernel-reducible pure-Lean
hashing, or any future tag. With `H := Sha256` this is
observationally identical to the cached side's
`hashTreeRootCached`, just slower; with `H := Sha256Spec` the
whole computation reduces in the kernel without an FFI hop. -/
def hashTreeRoot {H T : Type} [Hasher H] [SSZRepr T]
    (t : UncachedSSZ H T) : ByteArray :=
  SSZ.hashTreeRoot H t.view

end UncachedSSZ

end SizzLean.Cache
