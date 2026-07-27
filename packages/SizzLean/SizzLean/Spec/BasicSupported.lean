import SizzLean.Spec.Type
import SizzLean.Spec.Serialize  -- for isFixedSize / allFixedSize
import SizzLean.Spec.Supported  -- for the subset theorem below

/-!
# `SizzLean.Spec.BasicSupported`: the predicate the proof set grows over

A *strict subset* of `SSZType.Supported` (in `Spec/Supported.lean`)
that the three central theorems (`decode_encode`,
`serialize_injective`, `encode_size_le_max`) are proved for. Each
constructor here names an `SSZType` shape on which the proofs
close exhaustively; adding a constructor obliges the proofs to
extend. The subset relation is machine-checked by
`supported_of_basicSupported` at the bottom of this file, so the
two predicates cannot drift apart silently (adding a
`BasicSupported` constructor without its `Supported` counterpart
breaks the build).

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

/-! ### The subset relation, machine-checked

The module docstring's claim that `BasicSupported` is a subset of
`Supported` used to be prose only, and it silently broke when the
`uintN 128 / 256` constructors landed on `BasicSupported` before
`Supported` knew about the wide widths. The mutual theorem below
turns the claim into a build-enforced invariant: each
`BasicSupported` constructor maps to its `Supported` counterpart,
dropping the proof-only preconditions (`0 < n` on `vectorFixed` /
`bitvector`, `0 < t.fixedByteSize` on `listFixed`) that
`BasicSupported` carries and `Supported` does not. -/

mutual

/-- Every `BasicSupported` shape is `Supported`: the proof-coverage
predicate never claims a shape the codec does not implement.
Structural recursion over the `(BasicSupported,
BasicSupportedFieldsFixed)` inductive pair, mirroring the mutual
blocks in `Proofs/Roundtrip.lean`. -/
theorem SSZType.supported_of_basicSupported : ∀ {s : SSZType},
    SSZType.BasicSupported s → SSZType.Supported s
  | _, .uintN8 => .uintN8
  | _, .uintN16 => .uintN16
  | _, .uintN32 => .uintN32
  | _, .uintN64 => .uintN64
  | _, .uintN128 => .uintN128
  | _, .uintN256 => .uintN256
  | _, .bool => .bool
  | _, .vectorFixed _h_pos h_t h_t_fixed =>
      .vectorFixed (SSZType.supported_of_basicSupported h_t) h_t_fixed
  | _, .listFixed h_t h_t_fixed _h_sz_pos =>
      .listFixed (SSZType.supported_of_basicSupported h_t) h_t_fixed
  | _, .bitvector _h_pos => .bitvector
  | _, .bitlist => .bitlist
  | _, .containerFixed h_fs =>
      .containerFixed (SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed h_fs)

/-- Field-list companion: pointwise lift of
`supported_of_basicSupported` over a container's field list. -/
theorem SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed :
    ∀ {fs : List SSZType},
    SSZType.BasicSupportedFieldsFixed fs → SSZType.SupportedFieldsFixed fs
  | _, .nil => .nil
  | _, .cons h_t h_t_fixed h_ts =>
      .cons (SSZType.supported_of_basicSupported h_t) h_t_fixed
        (SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed h_ts)

end

/-- The subset is *strict*: `Supported` admits shapes the proof set
does not cover. `.bitvector 0` is the smallest witness, `Supported`
has no positivity precondition, while `BasicSupported.bitvector`
requires `0 < n` because the spec's decoder rejects zero-width
bitvectors and the universal roundtrip would be false. -/
example : SSZType.Supported (.bitvector 0) := .bitvector

/-- And `.bitvector 0` is indeed outside `BasicSupported`: `cases`
exposes the constructor's `0 < 0` precondition, absurd by `omega`. -/
example : ¬ SSZType.BasicSupported (.bitvector 0) := fun h => by
  cases h; omega

end SizzLean.Spec
