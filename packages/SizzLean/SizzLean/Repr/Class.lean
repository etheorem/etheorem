import SizzLean.Hasher.Class
import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.SSZError
import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.HashTreeRoot
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.BasicSupportedDecide
import SizzLean.Proofs.Roundtrip
import SizzLean.Proofs.Injective

/-!
# `SizzLean.Repr.Class`: `SSZRepr` typeclass + thin user-facing wrappers

The `SSZRepr` class declaration plus the `SSZ.serialize` /
`SSZ.deserialize` / `SSZ.hashTreeRoot` user-facing wrappers and
two per-user-type corollaries: `SSZ.roundtrip` and the
non-malleability theorem `SSZ.serialize_injective`.

ARCHITECTURE.md §5.1 specifies the class:

```
class SSZRepr (T : Type) where
  shape    : SSZType
  toRepr   : T → shape.interp
  fromRepr : shape.interp → T
  to_from  : ∀ x, fromRepr (toRepr x) = x
  from_to  : ∀ r, toRepr (fromRepr r) = r
```

A `SSZRepr T` instance carries a *shape* (the `SSZType` description
that classifies `T`'s wire format), an isomorphism between `T` and
that shape's interpretation, and proofs that the isomorphism is
genuine. Per-user-type `serialize` / `deserialize` / `hashTreeRoot`
are then thin wrappers; `SSZ.roundtrip` lifts the spec-side
`decode_encode` (`Proofs/Roundtrip.lean`) to the user type via the
`from_to` law.

## Why `SSZ.roundtrip` is gated by `BasicSupported r.shape` and `EncodedFits`

The library's `decode_encode` proof currently covers the
`BasicSupported` subset, under the value-level guard
`EncodedFits r.shape (r.toRepr x)` (`Spec/MaxByteLength.lean`): the
encoding of this value stays below `MAX_LENGTH`, which keeps every
`uint32` offset placeholder exact. The constructors carry no
schema-level guard, so shapes like `BeaconState`-scale containers
are inside the predicate, and the bound sits on the theorem, where
the actual value is known:

* `.uintN 8 / 16 / 32 / 64` and `.uintN 128 / 256`, `.bool`:
  basic primitives (the wide integers close by the `Nat`-digit
  codec proof in `Proofs/UIntWide.lean`).
* `.vector t n` / `.list t cap`: composites over a
  `BasicSupported` element type, either fixed-size (`vectorFixed` /
  `listFixed`) or variable-size via the offset-table codec
  (`vectorVar` / `listVar`, with `t.isFixedSize = false`;
  `vectorVar` also carries `0 < n`).
* `.bitvector n` (`0 < n`) / `.bitlist cap`: bit-packed shapes,
  closed by the bit-packing inverse in `Proofs/BitPack.lean`.
* `.container fs`: any field list whose fields are themselves
  `BasicSupported`, either all fixed-size (`containerFixed`) or
  mixed fixed/variable via the offset-table codec (`containerVar`,
  with `allFixedSize fs = false`).

The user-surface corollary inherits that gate: a user type whose
shape sits inside `BasicSupported` enjoys verified roundtrip for
every value whose encoding fits below `MAX_LENGTH`; a value whose
encoding is larger has no such wire form to begin with. The gate
is honest about scope and grows automatically as the proof set
widens.

The caller discharges the schema gate with `by decide`.
`Spec/BasicSupportedDecide.lean` makes `BasicSupported` decidable,
and the kernel unfolds a derived `shape` to a closed `SSZType`, so
the check runs at elaboration time. The size bound is a fact about
one value, so the caller supplies it.

## Lean idioms used here (annotated on first appearance)

* `class C T where … end`: declares a typeclass. The fields
  inside `where` are the methods; an `instance : C T := …` value
  supplies them for a particular `T`. At a call site, an
  *instance binder* `[C T]` asks the compiler to find a
  registered instance for `T`, this resolution step is called
  *instance synthesis*.
* `(H := H)`: *named-argument* syntax for passing the value `H`
  to a function's explicit parameter also called `H`. Useful
  when `H` is a *phantom tag*, a type parameter that appears in
  the function's signature but not in any of its argument or
  return types. Instance synthesis cannot recover a phantom from
  value arguments (there is nothing to look at), so the caller
  must pass it explicitly. Same idiom as `Spec/HashTreeRoot.lean`.
* `inductive … : Prop` for `BasicSupported`: the witness lives
  in `Prop`, Lean's universe of propositions whose proofs are
  erased at runtime. Using `Prop` lets `decode_encode` take a
  `BasicSupported r.shape` hypothesis without it appearing in
  the compiled binary.
-/

set_option autoImplicit false

namespace SizzLean

open SizzLean.Spec

/-- `SSZRepr T`: the user-facing typeclass bridging Lean types to
the SSZ wire format.

A type `T` carries an `SSZRepr T` instance by exhibiting:
* `shape`: the `SSZType` description that classifies `T`'s wire
  format (e.g. `.uintN 64` for a `Slot`-like wrapper, or
  `.container [.bool, .bool]` for a `Pair {a b : Bool}`).
* `toRepr` / `fromRepr`: a per-direction conversion between `T`
  values and `shape.interp` values. These are *value-level* iso
  arrows: at runtime they perform any boxing / unboxing the
  in-memory representation requires.
* `to_from` / `from_to`: the iso laws, kept on the class itself
  (not as separate theorems) so a user-supplied instance must
  commit to them at definition time. For library-provided
  instances and `deriving`-generated instances, both laws close
  by `rfl` because the iso is definitionally the identity.
-/
class SSZRepr (T : Type) where
  /-- The `SSZType` description classifying `T`'s wire format. -/
  shape    : SSZType
  /-- Forward iso: `T` → wire-form value. -/
  toRepr   : T → shape.interp
  /-- Inverse iso: wire-form value → `T`. -/
  fromRepr : shape.interp → T
  /-- Iso law (left): `fromRepr ∘ toRepr = id`. -/
  to_from  : ∀ x, fromRepr (toRepr x) = x
  /-- Iso law (right): `toRepr ∘ fromRepr = id`. The user-facing
  `SSZ.roundtrip` corollary uses this direction to convert the
  spec-level round-tripped value `toRepr (fromRepr y)` back to
  plain `y`. -/
  from_to  : ∀ r, toRepr (fromRepr r) = r

namespace SSZ

/-- User-facing serializer. Delegates to the spec-level `serialize`
through the `SSZRepr` instance's shape and forward iso.

`@[specialize]` lets the compiler monomorphise this at each
consensus type that calls it (`Validator`, `BeaconBlockHeader`,
…), removing the `SSZRepr`-instance dispatch at the hot path's
call site. The kernel still sees the unspecialised definition
for proof reduction. -/
@[specialize]
def serialize {T : Type} [r : SSZRepr T] (x : T) : ByteArray :=
  SSZType.serialize r.shape (r.toRepr x)

/-- User-facing deserializer. Decodes against the instance's shape;
on success, converts back through `fromRepr`; on failure, propagates
the `SSZError`. `@[specialize]` per `serialize` above. -/
@[specialize]
def deserialize {T : Type} [r : SSZRepr T] (b : ByteArray) :
    Except SSZError T :=
  match SSZType.deserialize r.shape b with
  | .ok (y, _) => .ok (r.fromRepr y)
  | .error e   => .error e

/-- User-facing Merkleization. Delegates to the spec-level
`hashTreeRoot` through the `Hasher` instance and the `SSZRepr`'s
shape. The `(H := H)` is needed because `Hasher`'s parameter is a
phantom tag, same idiom as `Spec/HashTreeRoot.lean`.
`@[specialize]` per `serialize` above. -/
@[specialize]
def hashTreeRoot {T : Type} (H : Type) [Hasher H] [r : SSZRepr T]
    (x : T) : ByteArray :=
  Spec.hashTreeRoot (H := H) r.shape (r.toRepr x)

/-- Per-user-type roundtrip corollary.

Given `[SSZRepr T]` with `BasicSupported r.shape`, the
`SSZ.deserialize ∘ SSZ.serialize` round-trip returns `.ok x` for any
`x : T` whose encoding stays below `MAX_LENGTH`.

The proof unfolds the wrappers, applies the spec-level `decode_encode`
on `r.toRepr x`, then uses `from_to` to fold the round-tripped
representation `toRepr (fromRepr (toRepr x))` back through to `x`.
More directly: `decode_encode` gives `deserialize r.shape
(serialize r.shape (toRepr x)) = .ok (toRepr x, _)`; our wrapper
then maps the `.ok` payload through `fromRepr`, giving
`.ok (fromRepr (toRepr x)) = .ok x` by `to_from`.

The gates: `BasicSupported r.shape`, which is `Supported` plus the
two zero-width side conditions (`Spec/BasicSupported.lean` records
that as the predicate's definition), and the value-level size bound
`h_fits`. The size form is the surface spelling of
`Spec.EncodedFits r.shape (r.toRepr x)`, the hypothesis
`decode_encode` carries; the two are interchangeable by
unfolding, so the Spec layer stays off this surface API. -/
theorem roundtrip {T : Type} [r : SSZRepr T] (x : T)
    (h_sup : SSZType.BasicSupported r.shape)
    (h_fits : (SSZ.serialize x).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize x) = .ok x := by
  unfold SSZ.deserialize SSZ.serialize
  rw [Proofs.decode_encode h_sup (r.toRepr x) h_fits]
  -- Goal: `(match .ok (toRepr x, _) with | .ok (y, _) => .ok (fromRepr y) | ...) = .ok x`.
  -- The `match` reduces because the scrutinee is a literal `.ok`;
  -- then `r.to_from` folds `fromRepr (toRepr x)` back to `x`.
  simp [r.to_from]

/-- Per-user-type non-malleability: two values of `T` with the same
encoding are equal.

The spec-level `serialize_injective` gives `toRepr x = toRepr y`, and
`to_from` carries that back to `x = y`. The gates are the ones
`roundtrip` takes: `BasicSupported r.shape`, which `by decide` closes on
any closed shape (`Spec/BasicSupportedDecide.lean`), and the size bound
on `x`. One bound is enough, since `y` shares `x`'s encoding. -/
theorem serialize_injective {T : Type} [r : SSZRepr T] {x y : T}
    (h_sup : SSZType.BasicSupported r.shape)
    (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y := by
  have h_repr : r.toRepr x = r.toRepr y :=
    Proofs.serialize_injective r.shape h_sup (r.toRepr x) (r.toRepr y) h_fits h_eq
  rw [← r.to_from x, ← r.to_from y, h_repr]

end SSZ

end SizzLean
