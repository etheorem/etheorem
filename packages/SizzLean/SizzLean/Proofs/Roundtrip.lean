import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Proofs.SimpAttrs
import SizzLean.Proofs.SerializeSize
import SizzLean.Proofs.UInt
import SizzLean.Proofs.UIntWide
import SizzLean.Proofs.Bool
import SizzLean.Proofs.VectorFixed
import SizzLean.Proofs.ListFixed
import SizzLean.Proofs.ContainerFixed
import SizzLean.Proofs.FixedElems
import SizzLean.Proofs.BitPack

/-!
# `SizzLean.Proofs.Roundtrip`: `decode_encode` dispatch over `BasicSupported`

This file is the *dispatcher* for the central `decode_encode`
theorem. Per-arm proofs live in sibling modules:

| Arm | File |
|---|---|
| `.uintN 8/16/32/64` | `Proofs/UInt.lean` |
| `.uintN 128/256` | `Proofs/UIntWide.lean` |
| `.bool` | `Proofs/Bool.lean` |
| `.vectorFixed t n` | `Proofs/VectorFixed.lean` |
| `.listFixed t cap` | `Proofs/ListFixed.lean` |
| `.bitvector n` / `.bitlist cap` | `Proofs/BitPack.lean` |

## A short note on Lean's recursion checker

Recursive definitions in Lean must be proved to terminate. The
*structural-recursion checker* is the cheap path: it accepts a
recursive call `f arg` if `arg` is a **strict subterm** of the
caller's input, i.e. extracted by pattern matching, so the
inductive's definition makes it syntactically smaller. The other
path is well-founded recursion, where the programmer supplies a
measure and a proof that it decreases; it's strictly more
powerful but needs an explicit `termination_by`/`decreasing_by`.

The proofs here use the structural path, which constrains *how*
recursive calls are written.

## The mutual `decode_encode` / `decode_encode_containerFixed_aux`

For composite arms (`vectorFixed`, `listFixed`), `decode_encode`
hands the per-arm helper a closure
`fun y => decode_encode h_t y`. The checker accepts this because
`h_t` is the case-split's sub-witness, a *strict subterm* of the
outer `h_sup`, extracted by the `BasicSupported.vectorFixed`
pattern, so each recursive call descends.

For the `containerFixed` arm, the helper would need
`∀ t ∈ fs, decode_encode_t`. A closure abstracting `t`
loses the connection to `fs`, and the checker can't see the
descent. The fix is a **mutual block** with a partner function
`decode_encode_containerFixed_aux` that recurses on
`h_fs : BasicSupportedFieldsFixed` structurally and dispatches
to `decode_encode` per-cons-head. Within a mutual block, members
can call each other freely so long as every call descends on a
strict subterm of *some* mutually-defined input; here the descent
zig-zags between the inductive pair `(BasicSupported,
BasicSupportedFieldsFixed)`.

`Proofs/ContainerFixed.lean` still ships the substantive
helpers (`deserializeFixedFields_append_shift`,
`allFixedSize_of_BasicSupportedFieldsFixed`,
`fixedByteSizeFields_le_maxByteLengthFields`) and the top-level
wrapper `decode_encode_containerFixed` (which unfolds the
encoder's `(fix ++ .empty)` shape into `fix`). This file's mutual
block holds only the field-walker `decode_encode_containerFixed_aux`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000000

namespace SizzLean.Proofs

open SizzLean.Spec

mutual

/-- Roundtrip over `BasicSupported`. Dispatches to per-arm
proofs; composite arms call into the mutual partner
`decode_encode_containerFixed_aux` for field-list induction. -/
theorem decode_encode : ∀ {s : SSZType}, SSZType.BasicSupported s →
    ∀ (x : s.interp),
      SSZType.deserialize s (SSZType.serialize s x) =
        .ok (x, (SSZType.serialize s x).size)
  | _, .uintN8, x => decode_encode_uintN8 x
  | _, .uintN16, x => decode_encode_uintN16 x
  | _, .uintN32, x => decode_encode_uintN32 x
  | _, .uintN64, x => decode_encode_uintN64 x
  | _, .uintN128, x => decode_encode_uintN128 x
  | _, .uintN256, x => decode_encode_uintN256 x
  | _, .bool, b => decode_encode_bool b
  | _, .vectorFixed (t := t) (n := n) h_pos h_t h_t_fixed, v =>
      decode_encode_vectorFixed t n h_pos h_t h_t_fixed
        (fun y => decode_encode h_t y) v
  | _, .listFixed (t := t) (cap := cap) h_t h_t_fixed h_sz_pos, xs =>
      decode_encode_listFixed t cap h_t h_t_fixed h_sz_pos
        (fun y => decode_encode h_t y) xs
  | _, .bitvector (n := n) h_pos, bv => decode_encode_bitvector n h_pos bv
  | _, .bitlist (cap := cap), xs => decode_encode_bitlist cap xs
  | _, .containerFixed (fs := fs) h_fs, vs => by
      -- Reduce the encoder's `(fix, var)` shape to just `fix` (var = .empty for
      -- all-fixed fields), then dispatch into the mutual aux for field-list induction.
      have h_var_empty := (size_serializeFieldsAux_fix h_fs vs
                            (SSZType.fixedSectionSizeFields fs)).2
      have h_fix_size := (size_serializeFieldsAux_fix h_fs vs
                            (SSZType.fixedSectionSizeFields fs)).1
      have h_all_fixed := allFixedSize_of_BasicSupportedFieldsFixed h_fs
      have h_serialize_size :
          (SSZType.serialize (.container fs) vs).size =
            SSZType.fixedByteSizeFields fs := by
        unfold SSZType.serialize
        simp [h_var_empty, h_fix_size]
      rw [h_serialize_size]
      unfold SSZType.serialize
      simp only [h_var_empty, ByteArray.append_empty]
      unfold SSZType.deserialize
      simp only [h_all_fixed, if_true]
      exact decode_encode_containerFixed_aux h_fs vs _

/-- Field-walker companion: induct on `h_fs` and dispatch
per-cons-head to `decode_encode`. -/
theorem decode_encode_containerFixed_aux : ∀ {fs : List SSZType}
    (_h_fs : SSZType.BasicSupportedFieldsFixed fs)
    (vs : SSZType.interpFields fs) (varOff : Nat),
    SSZType.deserializeFixedFields fs
        (SSZType.serializeFieldsAux fs vs varOff).1 0 =
      .ok (vs, SSZType.fixedByteSizeFields fs)
  | _, .nil, vs, _ => by
      unfold SSZType.serializeFieldsAux SSZType.deserializeFixedFields
        SSZType.fixedByteSizeFields
      rcases vs with ⟨⟩
      simp
  | _, .cons (t := t) (ts := ts) h_t h_t_fixed h_ts, vs, varOff => by
      have h_head_size :
          (SSZType.serialize t vs.1).size = t.fixedByteSize :=
        size_serialize_eq_fixedByteSize h_t h_t_fixed vs.1
      have h_head_de := decode_encode h_t vs.1
      have h_enc :
          (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 =
            SSZType.serialize t vs.1 ++
              (SSZType.serializeFieldsAux ts vs.2 varOff).1 := by
        show (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 = _
        simp only [SSZType.serializeFieldsAux, h_t_fixed, if_true]
      rw [h_enc]
      unfold SSZType.deserializeFixedFields
      have h_head_chunk :
          (SSZType.serialize t vs.1 ++
            (SSZType.serializeFieldsAux ts vs.2 varOff).1).extract 0
            (0 + t.fixedByteSize) = SSZType.serialize t vs.1 := by
        rw [Nat.zero_add,
            show t.fixedByteSize = (SSZType.serialize t vs.1).size from h_head_size.symm]
        exact ByteArray.extract_append_eq_left rfl
      simp only [h_head_chunk, h_head_de, h_head_size, ne_eq,
                 not_true_eq_false, ite_false]
      have h_shift :
          SSZType.deserializeFixedFields ts
              (SSZType.serialize t vs.1 ++
                (SSZType.serializeFieldsAux ts vs.2 varOff).1)
              (0 + t.fixedByteSize) =
            SSZType.deserializeFixedFields ts
              (SSZType.serializeFieldsAux ts vs.2 varOff).1 0 := by
        have h_eq : 0 + t.fixedByteSize = (SSZType.serialize t vs.1).size + 0 := by
          rw [h_head_size, Nat.add_zero, Nat.zero_add]
        rw [h_eq, deserializeFixedFields_append_shift]
      rw [h_shift, decode_encode_containerFixed_aux h_ts vs.2 varOff]
      show Except.ok ((vs.1, vs.2), t.fixedByteSize + SSZType.fixedByteSizeFields ts) =
           Except.ok (vs, SSZType.fixedByteSizeFields (t :: ts))
      rw [Prod.eta]
      rfl

end

end SizzLean.Proofs
