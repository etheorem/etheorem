import SizzLean.Spec.Type
import SizzLean.Spec.Serialize  -- for isFixedSize / allFixedSize

/-!
# `SizzLean.Spec.BasicSupported`: the predicate the proof set grows over

A *strict subset* of `SSZType.Supported` (in `Spec/Supported.lean`)
that the three central theorems (`decode_encode`,
`serialize_injective`, `encode_size_le_max`) are proved for. Each
constructor here names an `SSZType` shape on which the proofs
close exhaustively; adding a constructor obliges the proofs to
extend.

The predicate lives in `Spec/` (not `Proofs/`) because the
user-facing `SSZ.roundtrip` corollary in `Repr/Class.lean`
mentions it, a layering concern that follows ARCHITECTURE.md §2's
library-then-surface flow (Spec layer below, Repr layer above;
Proofs/ reaches over to discharge the theorems).

## Coverage

* **Basic integers**: `.uintN 8 / 16 / 32 / 64` (closed in
  `Proofs/UInt.lean` via `unfold` + `bv_decide`) and
  `.uintN 128 / 256` (closed in `Proofs/UIntWide.lean` by
  `Nat`-digit induction on the `natToLEBytes` / `readNatLE` codec,
  with no `bv_decide` axiom).
* **Bool**: `.bool` (closed by `cases`, in `Proofs/Bool.lean`).
* **Composites**: `.vector t n` / `.list t cap` /
  `.container fs` over fixed-size element / field types
  (closed in `Proofs/{VectorFixed,ListFixed,ContainerFixed}.lean`
  via mutual induction with the shared prereq
  `Proofs/SerializeSize.lean`).
* **Bit shapes**: `.bitvector n` (with `0 < n`) and
  `.bitlist cap` (closed in `Proofs/BitPack.lean` via the
  bit-packing inverse `packBitsLE_unpackBitsLEAux_inverse` plus
  `msbPos` delimiter recovery for the bitlist).

## Outside `BasicSupported`

* **Mixed-field containers** (some variable-size fields): the
  offset-table decode path sits outside `Supported` itself;
  admitting it here is separate spec-layer work.

## Why two mutually inductive predicates

The general `.container fs` arm needs to *recurse* into its field
list, each field must itself be `BasicSupported` and fixed-size.
`BasicSupportedFieldsFixed` captures this pointwise; it is mutual
with `BasicSupported` because the field-list predicate's `cons`
constructor takes a `BasicSupported t` witness for the head.

## Why `0 < n` on `vectorFixed` / `bitvector`

The spec rejects `n = 0` at *decode* time for both shapes
(`ssz_generic/basic_vector/invalid/vec_*_0` and
`ssz_generic/bitvector/invalid/bitvec_0` test cases), so the
universal roundtrip would fail in those constructors. The
precondition is carried at the `BasicSupported` layer rather than
tightening `Supported` itself, which would be a more invasive
spec adjustment.

-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual
/-- Narrow correctness-coverage predicate. Each constructor names
an `SSZType` shape for which all three central theorems
(`decode_encode`, `serialize_injective`, `encode_size_le_max`) are
proved in `Proofs/`. Adding a constructor obliges the proofs to
extend. -/
inductive SSZType.BasicSupported : SSZType → Prop
  /-- Single-byte unsigned integer. `serialize` is `empty.push x`;
  the roundtrip closes by `rfl` after one `unfold`. -/
  | uintN8 : SSZType.BasicSupported (.uintN 8)
  /-- 16-bit little-endian unsigned integer. Closes via the
  per-byte indexing chain reduced by `rfl` + `bv_decide` on the
  residual LE identity. -/
  | uintN16 : SSZType.BasicSupported (.uintN 16)
  /-- 32-bit little-endian unsigned integer. -/
  | uintN32 : SSZType.BasicSupported (.uintN 32)
  /-- 64-bit little-endian unsigned integer. -/
  | uintN64 : SSZType.BasicSupported (.uintN 64)
  /-- 128-bit little-endian unsigned integer. Unlike the narrow
  widths, the roundtrip closes by `Nat`-digit induction on the
  `natToLEBytes` / `readNatLE` codec (`Proofs/UIntWide.lean`), with
  no `bv_decide` axiom. -/
  | uintN128 : SSZType.BasicSupported (.uintN 128)
  /-- 256-bit little-endian unsigned integer (e.g.
  `ExecutionPayload.base_fee_per_gas`). Same codec proof as
  `uintN128`. -/
  | uintN256 : SSZType.BasicSupported (.uintN 256)
  /-- `Bool`, single-byte 0/1. -/
  | bool : SSZType.BasicSupported .bool
  /-- Fixed-length vector with fixed-size element type and
  non-empty length. The `n > 0` precondition mirrors the spec's
  zero-length rejection. -/
  | vectorFixed : ∀ {t : SSZType} {n : Nat},
                  0 < n → SSZType.BasicSupported t → t.isFixedSize = true →
                  SSZType.BasicSupported (.vector t n)
  /-- Variable-length list (up to `cap`) with fixed-size element
  type and positive element size. The `0 < t.fixedByteSize`
  precondition rules out the `.container []`-element pathology
  where the spec's `if sz = 0 then .error .tooShort` decoder
  guard would fail. -/
  | listFixed : ∀ {t : SSZType} {cap : Nat},
                SSZType.BasicSupported t → t.isFixedSize = true →
                0 < t.fixedByteSize →
                SSZType.BasicSupported (.list t cap)
  /-- Bit-packed fixed-width vector. The `n > 0` precondition
  mirrors the spec's zero-length rejection, same as `vectorFixed`.
  Roundtrip closes in `Proofs/BitPack.lean`. -/
  | bitvector : ∀ {n : Nat}, 0 < n → SSZType.BasicSupported (.bitvector n)
  /-- Bit-packed variable-length list (up to `cap` data bits) with
  its trailing delimiter bit. Roundtrip closes in
  `Proofs/BitPack.lean` via `msbPos` delimiter recovery. -/
  | bitlist : ∀ {cap : Nat}, SSZType.BasicSupported (.bitlist cap)
  /-- Container with an all-fixed-size, all-`BasicSupported`
  field list. -/
  | containerFixed : ∀ {fs : List SSZType},
                     SSZType.BasicSupportedFieldsFixed fs →
                     SSZType.BasicSupported (.container fs)

/-- Pointwise `BasicSupported ∧ isFixedSize` over a field list.
Used by the `containerFixed` arm. The `isFixedSize` half makes
the container decoder's `allFixedSize fs` guard pass; the
`BasicSupported` half lets the per-field roundtrip recurse. -/
inductive SSZType.BasicSupportedFieldsFixed : List SSZType → Prop
  | nil : SSZType.BasicSupportedFieldsFixed []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.BasicSupported t → t.isFixedSize = true →
           SSZType.BasicSupportedFieldsFixed ts →
           SSZType.BasicSupportedFieldsFixed (t :: ts)
end

end SizzLean.Spec
