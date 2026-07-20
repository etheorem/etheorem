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
import SizzLean.Proofs.ContainerVar
import SizzLean.Proofs.SizeBound
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

/-- `BasicSupportedFields` gives everything `FieldsFixedSizeOk`
(`Proofs/ContainerVar.lean`) needs: for fields that happen to be
fixed-size anyway, `size_serialize_eq_fixedByteSize` supplies the
exact byte count from the field's own `BasicSupported` witness.
Not part of the mutual block below, it doesn't call `decode_encode`. -/
theorem fieldsFixedSizeOk_of_basicSupportedFields :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFields fs →
    ∀ (vs : SSZType.interpFields fs), FieldsFixedSizeOk fs vs
  | _, .nil, _ => by unfold FieldsFixedSizeOk; trivial
  | _, .cons (t := t) (ts := ts) h_t h_ts, vs => by
      unfold FieldsFixedSizeOk
      exact ⟨fun h_fixed => size_serialize_eq_fixedByteSize h_t h_fixed vs.1,
             fieldsFixedSizeOk_of_basicSupportedFields h_ts vs.2⟩

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
  | _, .containerVar (fs := fs) h_fields h_not_fixed h_max_lt, vs => by
      -- Instantiate the offset-table walker at the top: `pre = .empty`,
      -- `prefixOff = 0`, `bufEnd = b.size`. `size_serializeFieldsAux_fixedSection`
      -- (`ContainerVar.lean`) pins the fixed prefix's width to the schema value,
      -- which both extract-invariants below and the pre-extraction inverse
      -- (`extractFieldOffsets_serializeFieldsAux`, PR 1) need.
      have h_ok := fieldsFixedSizeOk_of_basicSupportedFields h_fields vs
      have h_maxOk := encode_size_le_max_containerVarFields_aux h_fields vs
      have h_fix_size :
          (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1.size =
            SSZType.fixedSectionSizeFields fs :=
        size_serializeFieldsAux_fixedSection fs vs (SSZType.fixedSectionSizeFields fs) h_ok
      have h_bound :
          (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1.size +
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2.size ≤
            SSZType.maxByteLengthFields fs :=
        size_serializeFieldsAux_le_maxByteLengthFields fs vs
          (SSZType.fixedSectionSizeFields fs) h_maxOk
      have h_serialize_eq :
          SSZType.serialize (.container fs) vs =
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1 ++
              (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2 := by
        show SSZType.serialize (.container fs) vs = _
        unfold SSZType.serialize
        rfl
      have hML : SizzLean.Spec.MAX_LENGTH = 2 ^ 32 := rfl
      have h_uint32_bound :
          SSZType.fixedSectionSizeFields fs +
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2.size <
            2 ^ 32 := by
        omega
      have h_bsize :
          (SSZType.serialize (.container fs) vs).size =
            SSZType.fixedSectionSizeFields fs +
              (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2.size := by
        rw [h_serialize_eq, ByteArray.size_append, h_fix_size]
      have h_F :
          (SSZType.serialize (.container fs) vs).extract 0
              (0 + SSZType.fixedSectionSizeFields fs) =
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1 := by
        rw [Nat.zero_add, h_serialize_eq]
        exact ByteArray.extract_append_eq_left h_fix_size.symm
      have h_V :
          (SSZType.serialize (.container fs) vs).extract (SSZType.fixedSectionSizeFields fs)
              (SSZType.serialize (.container fs) vs).size =
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2 := by
        rw [h_bsize, h_serialize_eq]
        exact ByteArray.extract_append_eq_right h_fix_size.symm (by rw [h_fix_size])
      have h_offs :
          SizzLean.Spec.extractFieldOffsets (SSZType.serialize (.container fs) vs) fs 0 =
            .ok (varOffsetsOf fs vs (SSZType.fixedSectionSizeFields fs)) := by
        have h_pre :=
          extractFieldOffsets_serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)
            .empty h_ok h_uint32_bound
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2
        rw [h_serialize_eq]
        simpa using h_pre
      have h_walk :
          SSZType.deserializeVarFields fs (SSZType.serialize (.container fs) vs) 0
              (varOffsetsOf fs vs (SSZType.fixedSectionSizeFields fs))
              (SSZType.serialize (.container fs) vs).size = .ok vs :=
        decode_encode_containerVar_aux h_fields vs (SSZType.fixedSectionSizeFields fs)
          (SSZType.serialize (.container fs) vs) 0 (SSZType.serialize (.container fs) vs).size
          (by rw [Nat.zero_add, h_bsize]; omega)
          (by rw [h_bsize]; omega)
          (Nat.le_refl _) h_F h_V
      rw [h_serialize_eq]
      show SSZType.deserialize (.container fs)
          ((SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1 ++
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2) =
        .ok (vs,
          ((SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).1 ++
            (SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)).2).size)
      rw [← h_serialize_eq]
      unfold SSZType.deserialize
      simp only [h_not_fixed, Bool.false_eq_true, if_false]
      have h_prefixSize_le :
          ¬ (SSZType.serialize (.container fs) vs).size < SSZType.fixedSectionSizeFields fs := by
        omega
      simp only [h_prefixSize_le, if_false]
      rw [h_offs]
      have h_head_getD :
          (varOffsetsOf fs vs (SSZType.fixedSectionSizeFields fs)).head?.getD
              (SSZType.serialize (.container fs) vs).size =
            SSZType.fixedSectionSizeFields fs :=
        varOffsetsOf_head_getD fs vs (SSZType.fixedSectionSizeFields fs)
          (SSZType.serialize (.container fs) vs).size (by omega)
      cases h_head : varOffsetsOf fs vs (SSZType.fixedSectionSizeFields fs) with
      | nil =>
          -- No variable fields at all: `allFixedSize fs = true`, contradicting `h_not_fixed`.
          exact absurd (allFixedSize_of_varOffsetsOf_eq_nil fs vs
            (SSZType.fixedSectionSizeFields fs) h_head) (by rw [h_not_fixed]; decide)
      | cons o rest =>
          rw [h_head] at h_head_getD
          simp only [List.head?, Option.getD] at h_head_getD
          simp only [List.head?]
          rw [if_neg (fun h => h h_head_getD)]
          rw [h_head] at h_walk
          rw [h_walk]

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

/-- Field-walker companion for `containerVar`: the offset-table
decoder (`SSZType.deserializeVarFields`) recovers exactly the value
the encoder wrote, given the two `extract`-level invariants that
pin `b`'s fixed-prefix slice at `prefixOff` to `serializeFieldsAux`'s
`.1` and its variable-region slice at `[varOff, bufEnd)` to `.2`.

Both invariants decompose along `extract_split`
(`Proofs/ContainerVar.lean`) at each cons step: `.1`'s head
contributes either the field's own bytes (fixed) or a 4-byte offset
placeholder (variable); `.2`'s head contributes either nothing
(fixed) or the field's own body (variable). Unlike
`decode_encode_containerFixed_aux`, `b` itself never changes across
the recursive calls, only `prefixOff` / `varOff` (folded into the
`varOffsetsOf` argument) do, matching how
`SSZType.deserializeVarFields` is actually written. -/
theorem decode_encode_containerVar_aux : ∀ {fs : List SSZType},
    SSZType.BasicSupportedFields fs → ∀ (vs : SSZType.interpFields fs)
    (varOff : Nat) (b : ByteArray) (prefixOff bufEnd : Nat),
    prefixOff + SSZType.fixedSectionSizeFields fs ≤ b.size →
    varOff ≤ bufEnd → bufEnd ≤ b.size →
    b.extract prefixOff (prefixOff + SSZType.fixedSectionSizeFields fs) =
      (SSZType.serializeFieldsAux fs vs varOff).1 →
    b.extract varOff bufEnd = (SSZType.serializeFieldsAux fs vs varOff).2 →
    SSZType.deserializeVarFields fs b prefixOff (varOffsetsOf fs vs varOff) bufEnd = .ok vs
  | _, .nil, vs, _varOff, _b, _prefixOff, _bufEnd, _h_pf, _h_ve, _h_vb, _h_F, _h_V => by
      rcases vs with ⟨⟩
      unfold SSZType.deserializeVarFields
      rfl
  | _, .cons (t := t) (ts := ts) h_t h_ts, vs, varOff, b, prefixOff, bufEnd,
      h_pf, h_ve, h_vb, h_F, h_V => by
      by_cases h_fixed : t.isFixedSize = true
      · -- Fixed field: `.1`'s head is the field's own bytes; `.2` is untouched.
        have h_head_size : (SSZType.serialize t vs.1).size = t.fixedByteSize :=
          size_serialize_eq_fixedByteSize h_t h_fixed vs.1
        have h_fsz' :
            prefixOff + SSZType.fixedSectionSizeFields (t :: ts) =
              prefixOff + t.fixedByteSize + SSZType.fixedSectionSizeFields ts := by
          show prefixOff + (t.fixedSectionSize + SSZType.fixedSectionSizeFields ts) = _
          have h_sect_eq : t.fixedSectionSize = t.fixedByteSize := by
            unfold SSZType.fixedSectionSize; simp [h_fixed]
          rw [h_sect_eq]; omega
        have h_enc :
            (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 =
              SSZType.serialize t vs.1 ++ (SSZType.serializeFieldsAux ts vs.2 varOff).1 := by
          show (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 = _
          simp only [SSZType.serializeFieldsAux, h_fixed, if_true]
        have h_enc2 :
            (SSZType.serializeFieldsAux (t :: ts) vs varOff).2 =
              (SSZType.serializeFieldsAux ts vs.2 varOff).2 := by
          show (SSZType.serializeFieldsAux (t :: ts) vs varOff).2 = _
          simp only [SSZType.serializeFieldsAux, h_fixed, if_true]
        rw [h_enc, h_fsz'] at h_F
        rw [h_enc2] at h_V
        have h_pf' : prefixOff + t.fixedByteSize + SSZType.fixedSectionSizeFields ts ≤ b.size := by
          rw [← h_fsz']; exact h_pf
        have h_split :=
          extract_split (b := b) (p := prefixOff)
            (q := prefixOff + t.fixedByteSize + SSZType.fixedSectionSizeFields ts)
            (u := SSZType.serialize t vs.1) (v := (SSZType.serializeFieldsAux ts vs.2 varOff).1)
            h_F (by omega) h_pf'
        rw [h_head_size] at h_split
        have h_chunk : b.extract prefixOff (prefixOff + t.fixedByteSize) =
            SSZType.serialize t vs.1 := h_split.1
        have h_F' :
            b.extract (prefixOff + t.fixedByteSize)
                (prefixOff + t.fixedByteSize + SSZType.fixedSectionSizeFields ts) =
              (SSZType.serializeFieldsAux ts vs.2 varOff).1 := h_split.2
        have h_de := decode_encode h_t vs.1
        rw [h_head_size] at h_de
        have h_voff : varOffsetsOf (t :: ts) vs varOff = varOffsetsOf ts vs.2 varOff := by
          show (if t.isFixedSize then varOffsetsOf ts vs.2 varOff else _) = _
          simp [h_fixed]
        show SSZType.deserializeVarFields (t :: ts) b prefixOff
            (varOffsetsOf (t :: ts) vs varOff) bufEnd = .ok vs
        rw [h_voff]
        unfold SSZType.deserializeVarFields
        simp only [h_fixed, if_true]
        rw [h_chunk, h_de]
        simp only [ne_eq, not_true_eq_false, ite_false]
        rw [decode_encode_containerVar_aux h_ts vs.2 varOff b (prefixOff + t.fixedByteSize)
              bufEnd h_pf' h_ve h_vb h_F' h_V]
      · -- Variable field: `.1`'s head is a 4-byte offset placeholder;
        -- `.2`'s head is the field's own body.
        have h_fixed' : t.isFixedSize = false := by
          cases hc : t.isFixedSize <;> simp_all
        have hBPLO : SizzLean.Spec.BYTES_PER_LENGTH_OFFSET = 4 := rfl
        have h_fsz' :
            prefixOff + SSZType.fixedSectionSizeFields (t :: ts) =
              prefixOff + 4 + SSZType.fixedSectionSizeFields ts := by
          show prefixOff + (t.fixedSectionSize + SSZType.fixedSectionSizeFields ts) = _
          have h_sect_eq : t.fixedSectionSize = BYTES_PER_LENGTH_OFFSET := by
            unfold SSZType.fixedSectionSize; simp [h_fixed']
          rw [h_sect_eq, hBPLO]; omega
        have h_enc :
            (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 =
              uint32LE (Nat.toUInt32 varOff) ++
                (SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).1 := by
          show (SSZType.serializeFieldsAux (t :: ts) vs varOff).1 = _
          simp only [SSZType.serializeFieldsAux, h_fixed', if_false, Bool.false_eq_true]
        have h_enc2 :
            (SSZType.serializeFieldsAux (t :: ts) vs varOff).2 =
              SSZType.serialize t vs.1 ++
                (SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).2 := by
          show (SSZType.serializeFieldsAux (t :: ts) vs varOff).2 = _
          simp only [SSZType.serializeFieldsAux, h_fixed', if_false, Bool.false_eq_true]
        rw [h_enc, h_fsz'] at h_F
        rw [h_enc2] at h_V
        have h_offBytes_size : (uint32LE (Nat.toUInt32 varOff)).size = 4 := size_uint32LE _
        have h_pf' : prefixOff + 4 + SSZType.fixedSectionSizeFields ts ≤ b.size := by
          rw [← h_fsz']; exact h_pf
        have h_splitF :=
          extract_split (b := b) (p := prefixOff)
            (q := prefixOff + 4 + SSZType.fixedSectionSizeFields ts)
            (u := uint32LE (Nat.toUInt32 varOff))
            (v := (SSZType.serializeFieldsAux ts vs.2
              (varOff + (SSZType.serialize t vs.1).size)).1)
            h_F (by omega) h_pf'
        rw [h_offBytes_size] at h_splitF
        have h_F' :
            b.extract (prefixOff + 4)
                (prefixOff + 4 + SSZType.fixedSectionSizeFields ts) =
              (SSZType.serializeFieldsAux ts vs.2
                (varOff + (SSZType.serialize t vs.1).size)).1 := h_splitF.2
        have hqV : varOff + (SSZType.serialize t vs.1).size ≤ bufEnd := by
          have hVsize : (b.extract varOff bufEnd).size =
              (SSZType.serialize t vs.1).size +
                (SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).2.size := by
            rw [h_V, ByteArray.size_append]
          rw [ByteArray.size_extract, Nat.min_eq_left h_vb] at hVsize
          omega
        have h_splitV :=
          extract_split (b := b) (p := varOff) (q := bufEnd)
            (u := SSZType.serialize t vs.1)
            (v := (SSZType.serializeFieldsAux ts vs.2
              (varOff + (SSZType.serialize t vs.1).size)).2)
            h_V (by omega) h_vb
        have h_body : b.extract varOff (varOff + (SSZType.serialize t vs.1).size) =
            SSZType.serialize t vs.1 := h_splitV.1
        have h_V' :
            b.extract (varOff + (SSZType.serialize t vs.1).size) bufEnd =
              (SSZType.serializeFieldsAux ts vs.2
                (varOff + (SSZType.serialize t vs.1).size)).2 := h_splitV.2
        have h_bufEnd_eq :
            bufEnd = (varOff + (SSZType.serialize t vs.1).size) +
              (SSZType.serializeFieldsAux ts vs.2
                (varOff + (SSZType.serialize t vs.1).size)).2.size := by
          have h_sz := congrArg ByteArray.size h_V'
          rw [ByteArray.size_extract, Nat.min_eq_left h_vb] at h_sz
          omega
        have h_nextOff :
            (varOffsetsOf ts vs.2 (varOff + (SSZType.serialize t vs.1).size)).head?.getD bufEnd =
              varOff + (SSZType.serialize t vs.1).size :=
          varOffsetsOf_head_getD ts vs.2 (varOff + (SSZType.serialize t vs.1).size) bufEnd
            h_bufEnd_eq
        have h_voff :
            varOffsetsOf (t :: ts) vs varOff =
              varOff :: varOffsetsOf ts vs.2 (varOff + (SSZType.serialize t vs.1).size) := by
          show (if t.isFixedSize then _ else
            varOff :: varOffsetsOf ts vs.2 (varOff + (SSZType.serialize t vs.1).size)) = _
          simp [h_fixed']
        have h_de := decode_encode h_t vs.1
        show SSZType.deserializeVarFields (t :: ts) b prefixOff
            (varOffsetsOf (t :: ts) vs varOff) bufEnd = .ok vs
        rw [h_voff]
        unfold SSZType.deserializeVarFields
        simp only [h_fixed', if_false, Bool.false_eq_true, hBPLO]
        rw [h_nextOff]
        have h_guard : ¬ (varOff > varOff + (SSZType.serialize t vs.1).size ||
            varOff + (SSZType.serialize t vs.1).size > bufEnd) := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
          omega
        simp only [h_guard]
        rw [h_body, h_de]
        rw [decode_encode_containerVar_aux h_ts vs.2 (varOff + (SSZType.serialize t vs.1).size) b
              (prefixOff + 4) bufEnd h_pf' hqV h_vb h_F' h_V']
        show Except.ok (vs.1, vs.2) = Except.ok vs
        rw [Prod.eta]

end

end SizzLean.Proofs
