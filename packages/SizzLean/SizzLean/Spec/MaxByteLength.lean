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
* **`list t cap`**: `cap` elements (the *cap*, not the actual length,
  this is a static upper bound), each at most `maxByteLength t`.
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
  | .vector t n   => SSZType.maxByteLength t * n
  | .list t cap   => cap * SSZType.maxByteLength t
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

end SizzLean.Spec
