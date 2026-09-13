import SizzLean.Spec.Type
import SizzLean.Spec.Constants
import SizzLean.Spec.Serialize  -- for SSZType.isFixedSize

/-!
# `SizzLean.Spec.MaxByteLength`: static upper bound on serialized size

For every `s : SSZType`, `maxByteLength s` is a `Nat` upper bound
on `(serialize s x).size`, derived from the schema alone (no value
input). This is the right-hand side of the `encode_size_le_max`
central theorem and the foundation of any pre-flight buffer
sizing in callers.

Mirrors the spec's `*_serialized_byte_length` / `byte_length` helpers
in `simple-serialize.md` *§Serialization, Byte length*. Definitions
are structural recursion over `SSZType` plus list-traversing helpers
in a `mutual` block, same shape as `Spec/Serialize.lean`'s
`isFixedSize`/`fixedByteSize` to keep the elaborator happy.

## Per-constructor reasoning

* **Basic types** (`uintN n`, `bool`, `bitvector n`): exact byte
  width determined by the schema. `uintN n` packs `⌈n/8⌉` bytes.
* **`bitlist cap`**: `⌈(cap + 1)/8⌉`, the `+1` is the trailing
  delimiter bit. See `Spec/Serialize.lean`'s `bitlistToBytes`.
* **`vector t n`**: `n` elements, each at most `maxByteLength t`.
  If `t` is variable-size the wire form also carries an offset
  table, so the bound is `n * (BYTES_PER_LENGTH_OFFSET +
  maxByteLength t)` rather than `n * maxByteLength t`.
* **`list t cap`**: `cap` elements (the *cap*, not the actual length,
  this is a static upper bound), each at most `maxByteLength t`,
  plus the same per-element offset-table term when `t` is
  variable-size.
* **`container fs`**: sum of per-field contributions. Fixed-size
  fields contribute their own `maxByteLength`. Variable-size fields
  contribute `BYTES_PER_LENGTH_OFFSET + maxByteLength` (one
  `uint32` offset plus the field's body upper bound).

## Lean idioms used here

* `mutual ... end`: needed because the `container` recursion
  descends into a `List SSZType`, and Lean 4.29.1's
  structural-recursion checker rejects higher-order recursion
  through `List.foldr`. Same workaround `Spec/Interp.lean` /
  `Spec/Serialize.lean` use; see `Spec/Interp.lean`'s docstring
  for the long form.
-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual

/-- Static upper bound on `(SSZType.serialize s x).size`, derived
from the schema `s`. -/
def SSZType.maxByteLength : SSZType → Nat
  | .uintN n      => (n + 7) / 8
  | .bool         => 1
  | .vector t n   =>
      if t.isFixedSize then n * SSZType.maxByteLength t
      else n * (BYTES_PER_LENGTH_OFFSET + SSZType.maxByteLength t)
  | .list t cap   =>
      if t.isFixedSize then cap * SSZType.maxByteLength t
      else cap * (BYTES_PER_LENGTH_OFFSET + SSZType.maxByteLength t)
  | .bitvector n  => (n + 7) / 8
  | .bitlist cap  => (cap + 1 + 7) / 8
  | .container fs => SSZType.maxByteLengthFields fs

/-- Sum of per-field max-length contributions for a `container` field
list. Each fixed-size field contributes its own bytes; each
variable-size field contributes `BYTES_PER_LENGTH_OFFSET` (the offset
table entry) plus its body upper bound. -/
def SSZType.maxByteLengthFields : List SSZType → Nat
  | []      => 0
  | t :: ts =>
      let head : Nat :=
        if t.isFixedSize then SSZType.maxByteLength t
        else BYTES_PER_LENGTH_OFFSET + SSZType.maxByteLength t
      head + SSZType.maxByteLengthFields ts

end

/-! ### The value-level guard

`maxByteLength s < MAX_LENGTH` is a schema-level guard: it bounds
every value of `s` at once, but it fails whole schemas (real
`BeaconState` shapes among them) whose static maximum exceeds
`2 ^ 32` even though no producible value does. `EncodedFits` is the
value-level replacement the `decode_encode` guard-widening rows in
`packages/SizzLean/docs/PROOF_LEDGER.md` record: a hypothesis on
the theorem. The encoder writes every
`uint32` offset placeholder as `Nat.toUInt32` of a running offset,
and every running offset is bounded by the total encoded size, so
one bound below `MAX_LENGTH = 2 ^ 32` keeps every placeholder's
`UInt32` round-trip exact. -/

/-- The encoded size of `x` stays below `MAX_LENGTH`, so every
`uint32` offset the encoder writes is exact. The value-level
replacement for the schema-level `maxByteLength s < MAX_LENGTH`
guard. -/
def EncodedFits (s : SSZType) (x : s.interp) : Prop :=
  (SSZType.serialize s x).size < MAX_LENGTH

/-- The encoded size of a two-field container of `uintN 8` values
is `2`: the kernel reduces the serialized bytes through the
encoder equations, which `simp` lines up. -/
example : (SSZType.serialize (.container [.uintN 8, .uintN 8])
        (1, 2, PUnit.unit)).size = 2 := by
  simp [SSZType.serialize, SSZType.serializeFieldsAux,
    SSZType.fixedSectionSizeFields, SSZType.isFixedSize]

/-- And the `EncodedFits` statement for that value holds: the
encoded size is the `2` the example above computes, and `2 < 2 ^ 32`
is arithmetic. -/
example : EncodedFits (.container [.uintN 8, .uintN 8])
    (1, 2, PUnit.unit) := by
  have h2 : (SSZType.serialize (.container [.uintN 8, .uintN 8])
      (1, 2, PUnit.unit)).size = 2 := by
    simp [SSZType.serialize, SSZType.serializeFieldsAux,
      SSZType.fixedSectionSizeFields, SSZType.isFixedSize]
  have hML : MAX_LENGTH = 2 ^ 32 := rfl
  rw [EncodedFits, hML]
  omega

/-! ### Worked bounds

Both branches of the `.vector` / `.list` arms, pinned by `rfl` so the
build rejects a drift in the arithmetic. `rfl` suffices because
`maxByteLength` is structural recursion over a closed `SSZType`: the
kernel reduces each arm, decides the `isFixedSize` condition, and
evaluates the `Nat` multiplication. `SSZType.maxByteLength (.bitlist 8)`
is `(8 + 1 + 7) / 8 = 2`, the figure the variable-element lines below
multiply against.

Both branches are inside the theorem set: `encode_size_le_max`
covers the fixed-element branches (`Proofs/VectorFixed.lean`,
`Proofs/ListFixed.lean`) and the variable-element ones
(`Proofs/CollectionVar.lean`), the latter under the value-level
`EncodedFits` guard. These examples stay as the drift check on the
arithmetic itself. -/

-- Fixed-size elements: no offset table, `n` bodies of 1 byte each.
example : SSZType.maxByteLength (.vector (.uintN 8) 4) = 4  := rfl
example : SSZType.maxByteLength (.list (.uintN 8) 4)   = 4  := rfl

-- Variable-size elements: `BYTES_PER_LENGTH_OFFSET` per element on top
-- of each body, so `2 * (4 + 2)` and `4 * (4 + 2)`.
example : SSZType.maxByteLength (.vector (.bitlist 8) 2) = 12 := rfl
example : SSZType.maxByteLength (.list (.bitlist 8) 4)   = 24 := rfl

-- A nested variable collection: the inner `.list (.uintN 8) 4` is
-- variable-size and bounded by 4, so the outer vector pays
-- `2 * (4 + 4)`.
example : SSZType.maxByteLength (.vector (.list (.uintN 8) 4) 2) = 16 := rfl

-- A container field pays the same offset-table term, `4 + 2` for the
-- `bitlist` on top of the 1-byte `uintN 8`.
example : SSZType.maxByteLength (.container [.uintN 8, .bitlist 8]) = 7 := rfl

end SizzLean.Spec
