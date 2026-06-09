import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SerializeSize

/-!
# `SizzLean.Proofs.ContainerFixed`: general `.container fs` arm

Closes `decode_encode` and `encode_size_le_max` for `.container fs`
when each field is `BasicSupported` and fixed-size
(`BasicSupportedFieldsFixed fs`).

## Recipe

The encoder produces `(serializeFieldsAux fs vs varOff).1` (with
empty `.2` for all-fixed fields, see `size_serializeFieldsAux_fix`).
The decoder dispatches through `deserializeFixedFields fs b 0`,
which walks the fields left-to-right, reading each at a running
`off` advanced by `t.fixedByteSize` each step.

The proof uses **induction on the field list `fs`** (rather than
on the mutually inductive `BasicSupportedFieldsFixed` predicate,
which Lean's `induction` tactic rejects on mutual inductives).
Inside each list case, we `cases` the predicate to expose the
sub-witness, then recurse via the list's induction hypothesis.

Two helpers:

* `deserializeFixedFields_append_shift`: `deserializeFixedFields
  fs (a ++ b) (a.size + off) = deserializeFixedFields fs b off`.
  Lets us peel a fixed prefix off the buffer after consuming a
  field.
* `fixedByteSize_le_maxByteLength_of_BasicSupported`:
  `BasicSupported t → t.isFixedSize = true → fixedByteSize t ≤
  maxByteLength t`. Needs an `Inhabited` witness on the element
  type, supplied by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- `BasicSupportedFieldsFixed fs → allFixedSize fs = true`. -/
theorem allFixedSize_of_BasicSupportedFieldsFixed :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFieldsFixed fs →
      SSZType.allFixedSize fs = true := by
  intro fs h_fs
  induction fs with
  | nil => rfl
  | cons _ _ ih =>
    cases h_fs with
    | cons _ h_t_fixed h_ts =>
      unfold SSZType.allFixedSize
      simp [h_t_fixed, ih h_ts]

/-- `deserializeFixedFields fs (a ++ b) (a.size + off) =
deserializeFixedFields fs b off`. Public because the mutual
`decode_encode_containerFixed_aux` in `Proofs/Roundtrip.lean`
calls it. -/
theorem deserializeFixedFields_append_shift
    (fs : List SSZType) : ∀ (a b : ByteArray) (off : Nat),
      SSZType.deserializeFixedFields fs (a ++ b) (a.size + off) =
        SSZType.deserializeFixedFields fs b off := by
  induction fs with
  | nil =>
    intro a b off
    unfold SSZType.deserializeFixedFields
    rfl
  | cons t ts ih =>
    intro a b off
    have h_assoc : a.size + off + t.fixedByteSize =
                   a.size + (off + t.fixedByteSize) := Nat.add_assoc _ _ _
    -- Both sides reduce to a chunk-decode + a recursive call. The chunks match
    -- via extract_append_size_add (after assoc); the recursive calls match via
    -- the IH applied at the shifted offset. `congr 1` doesn't help here because
    -- of the let-bindings, so we use `simp only` to push through definitionally.
    have h_eq :
        SSZType.deserializeFixedFields (t :: ts) (a ++ b) (a.size + off) =
        SSZType.deserializeFixedFields (t :: ts) b off := by
      simp only [SSZType.deserializeFixedFields]
      rw [show a.size + off + t.fixedByteSize =
              a.size + (off + t.fixedByteSize) from Nat.add_assoc _ _ _,
          ByteArray.extract_append_size_add]
      -- Recursive deserializeFixedFields ts (a ++ b) (a.size + (off + t.fixedByteSize))
      -- = deserializeFixedFields ts b (off + t.fixedByteSize) via IH.
      rw [ih a b (off + t.fixedByteSize)]
    exact h_eq

-- The per-field decode_encode walker (`decode_encode_containerFixed_aux`)
-- and the top-level wrapper live in `Proofs/Roundtrip.lean`, where they
-- form a mutual block with `decode_encode` itself. The helpers in this
-- file (`deserializeFixedFields_append_shift`,
-- `allFixedSize_of_BasicSupportedFieldsFixed`,
-- `fixedByteSizeFields_le_maxByteLengthFields`) support both arms but
-- are not themselves mutually recursive.

/-- Field-list version of the size bound, taking the concrete
value `vs` as a source of per-field inhabitants. -/
theorem fixedByteSizeFields_le_maxByteLengthFields :
    ∀ {fs : List SSZType} (_h_fs : SSZType.BasicSupportedFieldsFixed fs)
      (_vs : SSZType.interpFields fs)
      (_h_max_field : ∀ t (_ : SSZType.BasicSupported t)
        (_ : t.isFixedSize = true) (x : t.interp),
        (SSZType.serialize t x).size ≤ SSZType.maxByteLength t),
      SSZType.fixedByteSizeFields fs ≤ SSZType.maxByteLengthFields fs := by
  intro fs
  induction fs with
  | nil =>
    intro _ _ _
    unfold SSZType.fixedByteSizeFields SSZType.maxByteLengthFields
    decide
  | cons t ts ih =>
    intro h_fs vs h_max_field
    cases h_fs with
    | cons h_t h_t_fixed h_ts =>
      have h_head_le_max : t.fixedByteSize ≤ SSZType.maxByteLength t := by
        have h := h_max_field t h_t h_t_fixed vs.1
        have h_sz := size_serialize_eq_fixedByteSize h_t h_t_fixed vs.1
        rw [h_sz] at h; exact h
      have h_tail := ih h_ts vs.2 h_max_field
      unfold SSZType.fixedByteSizeFields SSZType.maxByteLengthFields
      simp only [h_t_fixed, if_true]
      omega

/-- Size bound for `.container fs`. -/
theorem encode_size_le_max_containerFixed
    (fs : List SSZType) (h_fs : SSZType.BasicSupportedFieldsFixed fs)
    (h_max_field :
      ∀ t (_ : SSZType.BasicSupported t) (_ : t.isFixedSize = true) (x : t.interp),
        (SSZType.serialize t x).size ≤ SSZType.maxByteLength t)
    (vs : SSZType.interpFields fs) :
    (SSZType.serialize (.container fs) vs).size ≤
      SSZType.maxByteLength (.container fs) := by
  have h_var_empty := (size_serializeFieldsAux_fix h_fs vs
                        (SSZType.fixedSectionSizeFields fs)).2
  have h_fix_size := (size_serializeFieldsAux_fix h_fs vs
                        (SSZType.fixedSectionSizeFields fs)).1
  have h_serialize_size :
      (SSZType.serialize (.container fs) vs).size = SSZType.fixedByteSizeFields fs := by
    unfold SSZType.serialize
    simp [h_var_empty, h_fix_size]
  rw [h_serialize_size]
  show SSZType.fixedByteSizeFields fs ≤ SSZType.maxByteLength (.container fs)
  show SSZType.fixedByteSizeFields fs ≤ SSZType.maxByteLengthFields fs
  exact fixedByteSizeFields_le_maxByteLengthFields h_fs vs h_max_field

end SizzLean.Proofs
