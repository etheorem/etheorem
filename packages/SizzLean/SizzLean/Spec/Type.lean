/-!
# `SizzLean.Spec.Type`: the SSZ type universe

Reflects the SSZ grammar from the consensus-specs *§SSZ Types* section
(`simple-serialize.md`) as a Lean inductive. A value of `SSZType` is a
*description* of an SSZ shape, basic or composite. It is not yet a
value of that shape; the latter is `SSZType.interp` in
`Spec/Interp.lean`.

## Scope

The classic forms (`uintN`, `bool`, `Vector`, `List`, `Bitvector`,
`Bitlist`, `Container`) and the progressive forms are in this
inductive:

* `ProgressiveList[T]` / `ProgressiveBitlist` (EIP-7916): no capacity.
  Serialization follows the list / bitlist rules. Merkleization uses
  `merkleize_progressive` (shelves of 1, 4, 16, 64, … leaves).
* `ProgressiveContainer(active_fields=[…])` (EIP-7495): the mask is a
  type-level `List Bool`, not a serialized prefix. Only active fields
  are on the wire. A `false` bit is a zero chunk in the progressive
  Merkle tree.

The progressive constructors sit outside `BasicSupported`. The
central theorems (`decode_encode`, `serialize_injective`,
`encode_size_le_max`) stay on the classic subset; admitting the new
arms is a separate proof.

Three spec forms are still absent:

* `Union[T₁, …, Tₙ]`.
* Legacy `StableContainer[N]` + `Profile` (the on-wire active-fields
  prefix).
* `CompatibleUnion` (EIP-8016).

`deriving SSZRepr` emits a classic `container`. A structure tagged
`@[sizzlean_progressive]` emits `progressiveContainer` with every
field active. A mask that contains holes is an `SSZType` value
written by hand: a Lean structure has a field for every component,
so it cannot describe an inactive slot.
-/

set_option autoImplicit false

namespace SizzLean.Spec


/-- The SSZ type universe, one constructor per shape SizzLean
implements. Encoded as an `inductive` (rather than `String` tags) so
the typechecker keeps every recursion total and exhaustive.

Constructor cheatsheet (matched to consensus-specs naming):

* `uintN bits`: `bits ∈ {8,16,32,64,128,256}` per the spec; we accept
  any `Nat` so the type is not stringly-restricted, and pin the legal
  set via predicates downstream.
* `bool`: single byte, `0x00` (false) or `0x01` (true).
* `vector t n`: fixed-length homogeneous, `n` elements of `t`.
* `list t cap`: variable-length up to `cap`.
* `bitvector n` / `bitlist cap`: `n` (resp. up-to-`cap`) bits.
* `container fs`: heterogeneous tuple over the given field types.
* `progressiveList t` / `progressiveBitlist`: EIP-7916, no cap.
* `progressiveContainer active fs`: EIP-7495. `fs` is the active
  fields only; `active` is the type-level mask.

See the module docstring for `Union`, legacy `StableContainer`, and
`CompatibleUnion`, which stay out of this inductive. -/
inductive SSZType where
  | uintN     : (bits : Nat) → SSZType
  | bool      : SSZType
  | vector    : SSZType → Nat → SSZType
  | list      : SSZType → Nat → SSZType
  | bitvector : Nat → SSZType
  | bitlist   : Nat → SSZType
  | container : List SSZType → SSZType
  /-- `ProgressiveList[T]`. Values are uncapped arrays. -/
  | progressiveList : SSZType → SSZType
  /-- `ProgressiveBitlist`. Values are uncapped bit arrays. -/
  | progressiveBitlist : SSZType
  /-- `ProgressiveContainer(active_fields=…)`. `fields` lists the
  active field types in order; `active` places them among zero
  chunks. The mask is not serialized. -/
  | progressiveContainer : (active : List Bool) → (fields : List SSZType) → SSZType
  deriving Hashable

-- TODO: `DecidableEq SSZType`. Lean 4.34.1's nested-inductive
-- deriving handler cannot compose `DecidableEq` through the
-- recursive `List SSZType` field in `container`, so the instance
-- has to be hand-rolled when a consumer first needs it (likely
-- fuzzing or deriving-handler caching). The Spec layer's
-- totality + three-central-theorems work doesn't depend on it.

end SizzLean.Spec
