import SizzLean.Spec.Type
import SizzLean.Spec.Serialize  -- for isFixedSize / allFixedSize
import SizzLean.Spec.Supported  -- for the subset theorem below
import SizzLean.Spec.Constants  -- for MAX_LENGTH

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

* **Basic integers**: `.uintN 8 / 16 / 32 / 64` and
  `.uintN 128 / 256`, all closed through the `Nat`-digit
  `natToLEBytes` / `readNatLE` codec (`Proofs/UInt.lean` routes the
  narrow widths through the same lemmas `Proofs/UIntWide.lean`
  proves for the wide ones). No SAT certificate anywhere.
* **Bool**: `.bool` (closed by `cases`, in `Proofs/Bool.lean`).
* **Composites**: `.vector t n` / `.list t cap` over
  fixed-size element types (closed in
  `Proofs/{VectorFixed,ListFixed}.lean`) and over variable-size
  element types (closed in `Proofs/CollectionVar.lean` via the
  offset-table codec); `.container fs` over fixed-size field
  types (closed in `Proofs/ContainerFixed.lean` via mutual
  induction with the shared prereq `Proofs/SerializeSize.lean`).
* **Bit shapes**: `.bitvector n` (with `0 < n`) and
  `.bitlist cap` (closed in `Proofs/BitPack.lean` via the
  bit-packing inverse `packBitsLE_unpackBitsLEAux_inverse` plus
  `msbPos` delimiter recovery for the bitlist).

* **Mixed-field containers**: `.container fs` with at least one
  variable-size field (closed in `Proofs/ContainerVar.lean`'s
  groundwork plus the roundtrip walker
  `Proofs/Roundtrip.lean`'s `decode_encode_containerVar_aux`, via
  the offset-table codec).

## Why three mutually inductive predicates

The general `.container fs` arms need to *recurse* into their field
lists. `containerFixed` needs every field `BasicSupported` and
fixed-size; `BasicSupportedFieldsFixed` captures this pointwise.
`containerVar` only needs every field `BasicSupported` (fixed or
not, since the offset table handles both uniformly);
`BasicSupportedFields` captures *that* pointwise. Both field-list
predicates are mutual with `BasicSupported` because their `cons`
constructors take a `BasicSupported t` witness for the head.

## Why the constructors carry no `MAX_LENGTH` guard

Every offset the encoder writes is a `uint32`
(`Nat.toUInt32 varOff`, see `Spec/Serialize.lean`'s
`serializeFieldsAux` / `serializeVarElemsAux`), and it round-trips
through `UInt32` exactly only while the running offset stays below
`2 ^ 32`. A schema-level guard would exclude whole schemas whose
*static* maximum exceeds `MAX_LENGTH`, real `BeaconState` /
`BeaconBlockBody` shapes among them, even when no producible value
does.

The guard lives on the theorems: the
value-level `EncodedFits s x` (`Spec/MaxByteLength.lean`) says the
encoding of *this* value stays below `MAX_LENGTH`, and every
running offset is bounded by the total encoded size, so one
value-level bound keeps every offset's `UInt32` round-trip exact.
`decode_encode` and `serialize_injective` carry `EncodedFits` as a
hypothesis (`Proofs/Roundtrip.lean`, `Proofs/Injective.lean`);
`SSZ.roundtrip` lifts it to the user surface. The gate-widening
rows in `packages/SizzLean/docs/PROOF_LEDGER.md` record the change.

## Why `0 < n` on `vectorFixed` / `vectorVar` / `bitvector`

The spec rejects `n = 0` at *decode* time for these shapes
(`ssz_generic/basic_vector/invalid/vec_*_0` and
`ssz_generic/bitvector/invalid/bitvec_0` test cases), so the
universal roundtrip would fail in those constructors. The
`BasicSupported` layer carries the precondition. `Supported`
remains the structural codec predicate. `listVar` has no
positivity precondition: the empty list is the empty buffer.

-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual
/-- The proof-coverage predicate: `Supported` plus the two
zero-width side conditions, `0 < n` on the vector and bitvector
arms and `0 < t.fixedByteSize` on `listFixed`. Each constructor
names an `SSZType` shape for which all three central theorems
(`decode_encode`, `serialize_injective`, `encode_size_le_max`) are
proved in `Proofs/`. Adding a constructor obliges the proofs to
extend. That is this predicate's whole definition; no doc should
describe a further widening toward `Supported` (see the section at
the foot of this file). -/
inductive SSZType.BasicSupported : SSZType → Prop
  /-- Single-byte unsigned integer. `serialize` is `empty.push x`;
  the roundtrip closes by `rfl` after one `unfold`. -/
  | uintN8 : SSZType.BasicSupported (.uintN 8)
  /-- 16-bit little-endian unsigned integer. Closes through the
  `Nat`-digit codec bridge in `Proofs/UInt.lean`. -/
  | uintN16 : SSZType.BasicSupported (.uintN 16)
  /-- 32-bit little-endian unsigned integer. -/
  | uintN32 : SSZType.BasicSupported (.uintN 32)
  /-- 64-bit little-endian unsigned integer. -/
  | uintN64 : SSZType.BasicSupported (.uintN 64)
  /-- 128-bit little-endian unsigned integer. The roundtrip
  closes by `Nat`-digit induction on the `natToLEBytes` /
  `readNatLE` codec (`Proofs/UIntWide.lean`). -/
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
  /-- Fixed-length vector with variable-size element type and
  non-empty length. Decoded via the offset-table path
  (`Proofs/CollectionVar.lean`). The `n > 0` precondition mirrors
  the spec's zero-length rejection. The uint32-overflow guard is
  the theorem-level `EncodedFits`; no constructor hypothesis
  carries it. -/
  | vectorVar : ∀ {t : SSZType} {n : Nat},
                0 < n → SSZType.BasicSupported t → t.isFixedSize = false →
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
  /-- Variable-length list (up to `cap`) with variable-size element
  type. Decoded via the offset-table path; the empty list is the
  empty buffer. No `0 < t.fixedByteSize` (that pathology is
  specific to the fixed-element list decoder). The uint32-overflow
  guard is the theorem-level `EncodedFits`; no constructor
  hypothesis carries it. -/
  | listVar : ∀ {t : SSZType} {cap : Nat},
              SSZType.BasicSupported t → t.isFixedSize = false →
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
  /-- Container with at least one variable-size field
  (`allFixedSize fs = false`), decoded via the offset-table path
  (`Proofs/ContainerVar.lean`, `Proofs/Roundtrip.lean`'s
  `decode_encode_containerVar_aux`). The uint32-overflow guard is
  the theorem-level `EncodedFits`; no constructor hypothesis
  carries it; see the module docstring. -/
  | containerVar : ∀ {fs : List SSZType},
                   SSZType.BasicSupportedFields fs →
                   SSZType.allFixedSize fs = false →
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

/-- Pointwise `BasicSupported` over a field list, with **no**
`isFixedSize` constraint (unlike `BasicSupportedFieldsFixed`).
Used by the `containerVar` arm: the offset-table decode path
(`SSZType.deserializeVarFields`) handles fixed and variable fields
alike, so every field just needs to be individually
`BasicSupported`, whichever shape it is. -/
inductive SSZType.BasicSupportedFields : List SSZType → Prop
  | nil : SSZType.BasicSupportedFields []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.BasicSupported t →
           SSZType.BasicSupportedFields ts →
           SSZType.BasicSupportedFields (t :: ts)
end

/-! ### The subset relation, machine-checked

The mutual theorem below is the build-enforced form of the subset
claim: each `BasicSupported` constructor maps to its `Supported`
counterpart,
dropping the proof-only preconditions (`0 < n` on `vectorFixed` /
`vectorVar` / `bitvector`, `0 < t.fixedByteSize` on `listFixed`)
that `BasicSupported` carries and `Supported` does not. -/

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
  | _, .vectorVar _h_pos h_t h_var =>
      .vectorVar (SSZType.supported_of_basicSupported h_t) h_var
  | _, .listFixed h_t h_t_fixed _h_sz_pos =>
      .listFixed (SSZType.supported_of_basicSupported h_t) h_t_fixed
  | _, .listVar h_t h_var =>
      .listVar (SSZType.supported_of_basicSupported h_t) h_var
  | _, .bitvector _h_pos => .bitvector
  | _, .bitlist => .bitlist
  | _, .containerFixed h_fs =>
      .containerFixed (SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed h_fs)
  | _, .containerVar h_fs h_not_fixed =>
      .containerVar (SSZType.supportedFields_of_basicSupportedFields h_fs) h_not_fixed

/-- Field-list companion: pointwise lift of
`supported_of_basicSupported` over a container's field list. -/
theorem SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed :
    ∀ {fs : List SSZType},
    SSZType.BasicSupportedFieldsFixed fs → SSZType.SupportedFieldsFixed fs
  | _, .nil => .nil
  | _, .cons h_t h_t_fixed h_ts =>
      .cons (SSZType.supported_of_basicSupported h_t) h_t_fixed
        (SSZType.supportedFieldsFixed_of_basicSupportedFieldsFixed h_ts)

/-- Field-list companion for `containerVar`: pointwise lift of
`supported_of_basicSupported` over a container's field list, with
no `isFixedSize` witness to carry. -/
theorem SSZType.supportedFields_of_basicSupportedFields :
    ∀ {fs : List SSZType},
    SSZType.BasicSupportedFields fs → SSZType.SupportedFields fs
  | _, .nil => .nil
  | _, .cons h_t h_ts =>
      .cons (SSZType.supported_of_basicSupported h_t)
        (SSZType.supportedFields_of_basicSupportedFields h_ts)

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

/-! ### The bounded composition

`BasicSupported` composes into the third predicate without an
induction of its own: `supported_of_basicSupported` lifts the
witness to `Supported`, and `supportedBounded_of_supported`
(`Spec/Supported.lean`) lifts it the rest of the way. With this
composition in place every gating predicate in the library
translates into every other, and `encode_size_le_max`'s
`SupportedBounded` hypothesis is reachable from the proof set's own
`BasicSupported` witnesses. -/

/-! ## What `BasicSupported` is, by definition

The whole difference between `BasicSupported` and `Supported` is
the two zero-width side conditions: `0 < n` on the vector and bitvector
arms, and `0 < t.fixedByteSize` on `listFixed`. That is this
predicate's definition. `BasicSupported` is `Supported` plus
non-degeneracy, recorded here so no doc describes a further
widening toward `Supported` that cannot happen: the roundtrip
claim is *false* for the zero-width shapes (`Spec/Deserialize.lean`
rejects them, per the `ssz_generic` invalid vectors), so no proof
can cover them.
-/

/-- Every `BasicSupported` shape is `SupportedBounded`, by
composing the two subset theorems. No induction of its own. -/
theorem SSZType.supportedBounded_of_basicSupported {s : SSZType}
    (h : SSZType.BasicSupported s) : SSZType.SupportedBounded s :=
  SSZType.supportedBounded_of_supported (SSZType.supported_of_basicSupported h)

/-- The shape etheorem#61 quotes: a `uintN 64` field next to
a `list` of `uintN 64` at cap `2 ^ 40`, whose static
`maxByteLengthFields` exceeds `2 ^ 32` while every actual value
stays far below it. Closes by constructors: `containerVar` carries
no schema-level guard. -/
example : SSZType.BasicSupported (.container [.uintN 64, .list (.uintN 64) (2 ^ 40)]) :=
  .containerVar (.cons .uintN64 (.cons (.listFixed .uintN64 rfl (by decide)) .nil)) rfl

end SizzLean.Spec
