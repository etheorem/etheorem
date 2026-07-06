import SizzLean.Spec.Supported
import SizzLean.Spec.MaxByteLength
import SizzLean.Spec.BasicSupported
import SizzLean.Proofs.SimpAttrs
import SizzLean.Proofs.SerializeSize
import SizzLean.Proofs.UInt
import SizzLean.Proofs.Bool
import SizzLean.Proofs.VectorFixed
import SizzLean.Proofs.ListFixed
import SizzLean.Proofs.ContainerFixed
import SizzLean.Proofs.BitPack

/-!
# `SizzLean.Proofs.SizeBound`: encoded-size upper bound

The third central theorem; *dispatcher* for the per-arm bounds.

## Mutual block

Same shape as `Proofs/Roundtrip.lean`: the `containerFixed` case
needs per-field size bound `∀ t ∈ fs, …`, which would force the
helper to take a closure abstracting `t`; the structural-recursion
checker doesn't see through the closure. Fix: pair
`encode_size_le_max` with `encode_size_le_max_containerFields_aux`
in a mutual block.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

mutual

/-- *Encoded-size upper bound* (ARCHITECTURE.md §4): every
`BasicSupported`-shape value's serialized form fits within the
schema-derived `maxByteLength` upper bound. Composite arms call
the mutual partner `encode_size_le_max_containerFields_aux`. -/
theorem encode_size_le_max : ∀ {s : SSZType}, SSZType.BasicSupported s →
    ∀ (x : s.interp),
      (SSZType.serialize s x).size ≤ SSZType.maxByteLength s
  | _, .uintN8, x => encode_size_le_max_uintN8 x
  | _, .uintN16, x => encode_size_le_max_uintN16 x
  | _, .uintN32, x => encode_size_le_max_uintN32 x
  | _, .uintN64, x => encode_size_le_max_uintN64 x
  | _, .bool, b => encode_size_le_max_bool b
  | _, .vectorFixed (t := t) (n := n) h_pos h_t h_t_fixed, v =>
      encode_size_le_max_vectorFixed t n h_pos h_t h_t_fixed
        (fun y => encode_size_le_max h_t y) v
  | _, .listFixed (t := t) (cap := cap) h_t h_t_fixed _h_sz_pos, xs =>
      encode_size_le_max_listFixed t cap h_t h_t_fixed
        (fun y => encode_size_le_max h_t y) xs
  | _, .bitvector (n := n) _h_pos, bv => encode_size_le_max_bitvector n bv
  | _, .bitlist (cap := cap), xs => encode_size_le_max_bitlist cap xs
  | _, .containerFixed (fs := fs) h_fs, vs => by
      -- Same dispatch as `decode_encode`'s container arm, reduce the
      -- encoder's `(fix ++ var)` shape to size = `fixedByteSizeFields fs`,
      -- then bound via the field-walker.
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
      exact encode_size_le_max_containerFields_aux h_fs vs

/-- Field-walker companion: descend `h_fs` structurally; at each
cons head, call `encode_size_le_max` on the field's
`BasicSupported` witness to derive `fixedByteSize t ≤
maxByteLength t`. -/
theorem encode_size_le_max_containerFields_aux : ∀ {fs : List SSZType}
    (_h_fs : SSZType.BasicSupportedFieldsFixed fs)
    (_vs : SSZType.interpFields fs),
    SSZType.fixedByteSizeFields fs ≤ SSZType.maxByteLengthFields fs
  | _, .nil, _ => by
      unfold SSZType.fixedByteSizeFields SSZType.maxByteLengthFields
      decide
  | _, .cons (t := t) (ts := ts) h_t h_t_fixed h_ts, vs => by
      have h_head_le_max : t.fixedByteSize ≤ SSZType.maxByteLength t := by
        have h := encode_size_le_max h_t vs.1
        have h_sz := size_serialize_eq_fixedByteSize h_t h_t_fixed vs.1
        rw [h_sz] at h; exact h
      have h_tail := encode_size_le_max_containerFields_aux h_ts vs.2
      unfold SSZType.fixedByteSizeFields SSZType.maxByteLengthFields
      simp only [h_t_fixed, if_true]
      omega

end

end SizzLean.Proofs
