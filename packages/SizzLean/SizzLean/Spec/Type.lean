/-!
# `SizzLean.Spec.Type`: the SSZ type universe

Reflects the SSZ grammar from the consensus-specs *§SSZ Types* section
(`simple-serialize.md`) as a Lean inductive. A value of `SSZType` is a
*description* of an SSZ shape, basic or composite. It is not yet a
value of that shape; the latter is `SSZType.interp` in
`Spec/Interp.lean`.

## Scope: what's *not* here

The full SSZ universe in `consensus-specs/ssz/simple-serialize.md`
also defines five forms that SizzLean **intentionally does not
implement**:

* `Union[T₁, …, Tₙ]`: tagged sum with a `uint8` selector.
* `ProgressiveContainer(active_fields=[…])` (EIP-7495): container
  with a `List Bool` *active-fields prefix* so future forks can add
  fields without disturbing existing gindices.
* `StableContainer[N]` + `Profile` (EIP-7495 legacy): fixed-size
  optional-field bag with named profiles.
* `ProgressiveList[T]` / `ProgressiveBitlist` (EIP-7916): capacity-
  less lists / bitlists that grow with content.
* `CompatibleUnion({sel: type, …})` (EIP-8016): union with explicit
  `uint8` selectors in `1..127` (rather than positional indices).

**Why omitted.** As of consensus-spec-tests v1.5.0 *and* the current
consensus-specs `dev` head, no consensus type from `phase0` through
`gloas` (including the experimental `eip7732` / `eip7441` tracks) uses
any of these forms. Every container in the seven mainline forks plus
Gloas is a plain `Container`; every list is a plain `List[T, N]` or
`Bitlist[N]`; no fork uses `Union`. Including the five unused forms
in `SSZType` would inflate every match expression with TODO arms and
every proof with extra cases, for zero conformance benefit. The
universal `decode_encode` / `serialize_injective` /
`encode_size_le_max` theorems are several arms smaller as a
result.

If a future fork adopts any of these forms (e.g. `BeaconBlockBody`
rewrapped as a `ProgressiveContainer` for forward-compatible field
additions), the right move is to re-add the corresponding constructor
plus its `serialize` / `deserialize` / `hashTreeRoot` arms, and at
that point, the `profile%` macro front-end sketched in
ARCHITECTURE.md §8 becomes the way users declare them. Until then,
`deriving SSZRepr` over a vanilla Lean `structure` is sufficient.
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

See the module docstring for the SSZ-spec forms intentionally omitted
(unions, progressive / stable containers, progressive lists,
compatible unions). -/
inductive SSZType where
  | uintN     : (bits : Nat) → SSZType
  | bool      : SSZType
  | vector    : SSZType → Nat → SSZType
  | list      : SSZType → Nat → SSZType
  | bitvector : Nat → SSZType
  | bitlist   : Nat → SSZType
  | container : List SSZType → SSZType
  deriving Hashable

-- TODO: `DecidableEq SSZType`. Lean 4.29.1's nested-inductive
-- deriving handler cannot compose `DecidableEq` through the
-- recursive `List SSZType` field in `container`, so the instance
-- has to be hand-rolled when a consumer first needs it (likely
-- fuzzing or deriving-handler caching). The Spec layer's
-- totality + three-central-theorems work doesn't depend on it.

end SizzLean.Spec
