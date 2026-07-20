import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.MaxByteLength
import Std.Tactic.BVDecide

/-!
# `SizzLean.Proofs.ContainerVar`: groundwork for mixed-field `.container fs`

Mixed-field containers (at least one variable-size field, `list` /
`bitlist`) are the flagship remaining gap in `SSZType.Supported`:
the codec ([`Spec/Serialize.lean`](../Spec/Serialize.lean)'s
`serializeFieldsAux`, [`Spec/Deserialize.lean`](../Spec/Deserialize.lean)'s
non-`allFixedSize` `.container` branch) fully implements the
offset-table wire format, but no `BasicSupported` constructor
claims it yet, and no theorem closes it. This module lays the
groundwork; the predicates (`containerVar` on `BasicSupported` /
`Supported` / `SupportedBounded`) and the roundtrip walker land in
a follow-up, once this file's lemmas are available to build on.

## Wire format (what the lemmas below characterize)

```
fixed section                         variable section
┌────────┬──────────┬────────┬──────┐ ┌────────┬────────┐
│ A bytes│ offset(B)│ C bytes│offset│ │ B body │ D body │
│(fixed) │ (uint32) │(fixed) │ (D)  │ │        │        │
└────────┴──────────┴────────┴──────┘ └────────┴────────┘
```

`serializeFieldsAux` builds this by walking `fs` once, threading a
running `varOff` (seeded at `fixedSectionSizeFields fs`, the total
width of the fixed section): fixed fields append their bytes to the
`.1` accumulator; variable fields append a `uint32LE varOff`
placeholder to `.1` and their own body to the `.2` accumulator,
then advance `varOff` by the body's size. The decoder's
`extractFieldOffsets` walks `fs` against the *same* running `off`
to read the placeholders back out, before `deserializeVarFields`
uses them to slice each variable field's body out of the variable
region.

## Lemma path

The five groundwork facts, in the order they compose:

1. **uint32 codec bridge** (`readUInt32LE_uint32LE_append`,
   `readUInt32LE_append_shift`, `toNat_toUInt32_of_lt`): the
   `uint32LE` / `readUInt32LE` round-trip, and the shift needed to
   read an offset placeholder embedded partway through a buffer.
   Same trust class as the narrow `uintN` arms: one `bv_decide`.
2. **Extract-middle** (`extract_middle`): slicing the middle piece
   out of a three-way `ByteArray` append, the lemma the (later)
   roundtrip walker needs to identify `b.extract curOff nextOff`
   with a variable field's serialized body.
3. **Field-list plumbing devices** (`FieldsFixedSizeOk`,
   `FieldsMaxSizeOk`, `varOffsetsOf`): the per-field correctness
   facts the accounting lemmas below need, threaded alongside `vs`
   the way `serializeFixedElems_size_aux` threads a per-element size
   fact, but for a *heterogeneous* field list, so the natural shape
   is a structural `def` (not an `inductive`) recursing on `fs` and
   `vs` in lockstep. Kept local to this file rather than exported to
   `Spec/`: once `BasicSupportedFields` lands (the real,
   proof-carrying pointwise predicate), each is a one-line corollary
   of it, and the dedicated file that adds it will make that link.
4. **Encoder accounting** (`size_serializeFieldsAux_fixedSection`):
   `(serializeFieldsAux fs vs varOff).1.size = fixedSectionSizeFields fs`.
5. **Size walker** (`size_serializeFieldsAux_le_maxByteLengthFields`):
   `(serializeFieldsAux fs vs varOff).1.size + .2.size ≤
   maxByteLengthFields fs`. Needed for the `encode_size_le_max`
   arm, and for the uint32-overflow guard every offset placeholder
   depends on.
6. **Offset-extraction inverse**
   (`extractFieldOffsets_serializeFieldsAux`): reading
   `extractFieldOffsets` back off the encoder's own output recovers
   exactly the running offsets `serializeFieldsAux` wrote
   (`varOffsetsOf`). The hard direction; see its docstring for why
   the invariant is *simpler* than it first looks (it never has to
   track where the variable region physically sits).

## Trust

Every lemma here closes with the three standard kernel axioms plus
one `bv_decide` call (`readUInt32LE_uint32LE_append`), the same
trust class as the narrow `uintN 8/16/32/64` arms in `Proofs/UInt.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SizzLean.Proofs

open SizzLean.Spec
-- `extractFieldOffsets` is `protected` in `Spec/Deserialize.lean`
-- (proof-internal, kept off the general `SizzLean.Spec` surface, same
-- convention as `natToLEBytes` / `readNatLE`), so the wildcard `open`
-- above does not bring it into scope; request it explicitly.
open SizzLean.Spec (extractFieldOffsets)

/-! ### uint32 offset codec bridge -/

/-- `uint32LE` always emits exactly 4 bytes. -/
theorem size_uint32LE (x : UInt32) : (uint32LE x).size = 4 := by
  unfold uint32LE
  simp [ByteArray.size_push, ByteArray.size_empty]

/-- Reading a `uint32LE`-encoded offset placeholder back off the
front of a buffer recovers the original value. One `bv_decide` call
bit-blasts the byte-reassembly identity, same trust class as
`decode_encode_uintN32` in `Proofs/UInt.lean`. -/
theorem readUInt32LE_uint32LE_append (x : UInt32) (b : ByteArray) :
    readUInt32LE (uint32LE x ++ b) 0 = some x := by
  have hsize : (uint32LE x).size = 4 := size_uint32LE x
  have hbound : (0 : Nat) + 4 ≤ (uint32LE x ++ b).size := by
    rw [ByteArray.size_append, hsize]; omega
  unfold readUInt32LE
  rw [dif_pos hbound]
  have h0 : (uint32LE x ++ b)[(0 : Nat)]'(by omega) = x.toUInt8 := by
    rw [ByteArray.getElem_append_left (by rw [hsize]; omega)]
    unfold uint32LE; rfl
  have h1 : (uint32LE x ++ b)[(0 : Nat) + 1]'(by omega) = (x >>> 8).toUInt8 := by
    rw [ByteArray.getElem_append_left (by rw [hsize]; omega)]
    unfold uint32LE; rfl
  have h2 : (uint32LE x ++ b)[(0 : Nat) + 2]'(by omega) = (x >>> 16).toUInt8 := by
    rw [ByteArray.getElem_append_left (by rw [hsize]; omega)]
    unfold uint32LE; rfl
  have h3 : (uint32LE x ++ b)[(0 : Nat) + 3]'(by omega) = (x >>> 24).toUInt8 := by
    rw [ByteArray.getElem_append_left (by rw [hsize]; omega)]
    unfold uint32LE; rfl
  simp only [h0, h1, h2, h3]
  congr 1
  bv_decide

/-- Reading a fixed-width `uint32` at an offset shifted past some
already-consumed prefix `a` agrees with reading at the unshifted
offset into the remainder `b`. Lets the offset-extraction inverse
peel prefix bytes off the buffer one field at a time. -/
theorem readUInt32LE_append_shift (a b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) :
    readUInt32LE (a ++ b) (a.size + off) = readUInt32LE b off := by
  have hbound_ab : a.size + off + 4 ≤ (a ++ b).size := by
    rw [ByteArray.size_append]; omega
  unfold readUInt32LE
  rw [dif_pos hbound_ab, dif_pos h]
  have e0 : (a ++ b)[a.size + off]'(by omega) = b[off]'(by omega) := by
    rw [ByteArray.getElem_append_right (by omega)]; congr 1; omega
  have e1 : (a ++ b)[a.size + off + 1]'(by omega) = b[off + 1]'(by omega) := by
    simp only [show a.size + off + 1 = a.size + (off + 1) from by omega]
    rw [ByteArray.getElem_append_right (by omega)]; congr 1; omega
  have e2 : (a ++ b)[a.size + off + 2]'(by omega) = b[off + 2]'(by omega) := by
    simp only [show a.size + off + 2 = a.size + (off + 2) from by omega]
    rw [ByteArray.getElem_append_right (by omega)]; congr 1; omega
  have e3 : (a ++ b)[a.size + off + 3]'(by omega) = b[off + 3]'(by omega) := by
    simp only [show a.size + off + 3 = a.size + (off + 3) from by omega]
    rw [ByteArray.getElem_append_right (by omega)]; congr 1; omega
  simp only [e0, e1, e2, e3]

/-- `UInt32.ofNat` inverts `.toNat` under the width bound. Named for
the offset placeholders: `Nat.toUInt32 varOff` round-trips exactly
as long as `varOff < 2 ^ 32`, the uint32-overflow guard every
running offset needs. -/
theorem toNat_toUInt32_of_lt (o : Nat) (h : o < 2 ^ 32) : (Nat.toUInt32 o).toNat = o :=
  UInt32.toNat_ofNat_of_lt' h

/-! ### Extract-middle -/

/-- Slicing the middle piece out of a three-way append. The
(later) roundtrip walker uses this to identify `b.extract curOff
nextOff` with a variable field's own serialized body, given `b =
a ++ body ++ c` for the appropriate `a` / `c`. -/
theorem extract_middle (a b c : ByteArray) :
    (a ++ b ++ c).extract a.size (a.size + b.size) = b := by
  rw [ByteArray.append_assoc]
  have h := @ByteArray.extract_append_size_add a (b ++ c) 0 b.size
  simp only [Nat.add_zero] at h
  rw [h, ByteArray.extract_append_eq_left rfl]

/-! ### Field-list plumbing devices

Per-field correctness facts threaded alongside `vs`, the
heterogeneous-list analogue of the single-hypothesis style
`serializeFixedElems_size_aux` uses for homogeneous lists. Plain
structural `def`s (not `inductive`s): they carry no proof
obligations of their own, and once `BasicSupportedFields` (the
proof-carrying pointwise predicate) lands, each is recovered from it
in one line, which is what lets the predicate-independent lemmas
below land ahead of the predicate itself. -/

/-- Per-fixed-field exact size fact: for every field of `fs` that is
itself fixed-size, its serialized bytes have exactly the schema's
`fixedByteSize`. Says nothing about variable fields (their exact
serialized size isn't schema-determined). -/
def FieldsFixedSizeOk : (fs : List SSZType) → SSZType.interpFields fs → Prop
  | [],      _  => True
  | t :: ts, vs =>
      (t.isFixedSize = true → (SSZType.serialize t vs.1).size = t.fixedByteSize) ∧
        FieldsFixedSizeOk ts vs.2

/-- Per-field `maxByteLength` bound, for *every* field (fixed or
variable alike, unlike `FieldsFixedSizeOk`): the schema-level bound
the size walker below composes across the whole list. -/
def FieldsMaxSizeOk : (fs : List SSZType) → SSZType.interpFields fs → Prop
  | [],      _  => True
  | t :: ts, vs =>
      (SSZType.serialize t vs.1).size ≤ SSZType.maxByteLength t ∧ FieldsMaxSizeOk ts vs.2

/-- Expected running variable-field offsets: the list the encoder's
placeholders *should* decode back to, mirroring
`serializeFieldsAux`'s own branching exactly (one entry per
variable-size field, in declaration order). -/
def varOffsetsOf : (fs : List SSZType) → SSZType.interpFields fs → Nat → List Nat
  | [],      _,  _      => []
  | t :: ts, vs, varOff =>
      if t.isFixedSize then varOffsetsOf ts vs.2 varOff
      else varOff :: varOffsetsOf ts vs.2 (varOff + (SSZType.serialize t vs.1).size)

/-! ### Encoder accounting and the size walker -/

/-- **Encoder accounting**: the fixed-section output of
`serializeFieldsAux` has exactly the schema-predicted width. Every
fixed field contributes `fixedByteSize t` (from `FieldsFixedSizeOk`);
every variable field contributes exactly 4 bytes (the offset
placeholder, `size_uint32LE`). Structural induction on `fs`, in
lockstep with `FieldsFixedSizeOk`. -/
theorem size_serializeFieldsAux_fixedSection :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs) (varOff : Nat),
    FieldsFixedSizeOk fs vs →
    (SSZType.serializeFieldsAux fs vs varOff).1.size = SSZType.fixedSectionSizeFields fs := by
  intro fs
  induction fs with
  | nil =>
    intro vs varOff _
    unfold SSZType.serializeFieldsAux SSZType.fixedSectionSizeFields
    simp [ByteArray.size_empty]
  | cons t ts ih =>
    intro vs varOff h_ok
    unfold FieldsFixedSizeOk at h_ok
    obtain ⟨h_head, h_tail⟩ := h_ok
    unfold SSZType.serializeFieldsAux SSZType.fixedSectionSizeFields SSZType.fixedSectionSize
    by_cases h_fixed : t.isFixedSize = true
    · simp only [h_fixed, if_true]
      rw [ByteArray.size_append, h_head h_fixed, ih vs.2 varOff h_tail]
    · have h_fixed' : t.isFixedSize = false := by
        cases h : t.isFixedSize <;> simp_all
      have hBPLO : SizzLean.Spec.BYTES_PER_LENGTH_OFFSET = 4 := rfl
      simp only [h_fixed', if_false, Bool.false_eq_true, hBPLO]
      rw [ByteArray.size_append, size_uint32LE,
          ih vs.2 (varOff + (SSZType.serialize t vs.1).size) h_tail]

/-- **Size walker**: the total serialized output of
`serializeFieldsAux` (fixed section plus variable section combined)
fits within the schema-derived `maxByteLengthFields` bound. Every
field contributes `≤ maxByteLength t` to the appropriate side; the
variable-field branch additionally accounts for its 4-byte offset
placeholder against `BYTES_PER_LENGTH_OFFSET`. Feeds both the
`encode_size_le_max` `containerVar` arm and the uint32-overflow
guard the offset-extraction inverse below depends on. -/
theorem size_serializeFieldsAux_le_maxByteLengthFields :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs) (varOff : Nat),
    FieldsMaxSizeOk fs vs →
    (SSZType.serializeFieldsAux fs vs varOff).1.size +
      (SSZType.serializeFieldsAux fs vs varOff).2.size ≤ SSZType.maxByteLengthFields fs := by
  intro fs
  induction fs with
  | nil =>
    intro vs varOff _
    unfold SSZType.serializeFieldsAux SSZType.maxByteLengthFields
    simp [ByteArray.size_empty]
  | cons t ts ih =>
    intro vs varOff h_ok
    unfold FieldsMaxSizeOk at h_ok
    obtain ⟨h_head, h_tail⟩ := h_ok
    have h_tail_bound := ih vs.2 varOff h_tail
    have h_tail_bound' := ih vs.2 (varOff + (SSZType.serialize t vs.1).size) h_tail
    unfold SSZType.serializeFieldsAux SSZType.maxByteLengthFields
    by_cases h_fixed : t.isFixedSize = true
    · simp only [h_fixed, if_true]
      rw [ByteArray.size_append]
      omega
    · have h_fixed' : t.isFixedSize = false := by
        cases h : t.isFixedSize <;> simp_all
      simp only [h_fixed', if_false, Bool.false_eq_true]
      rw [ByteArray.size_append, ByteArray.size_append, size_uint32LE]
      have hBPLO : SizzLean.Spec.BYTES_PER_LENGTH_OFFSET = 4 := rfl
      rw [hBPLO]
      omega

/-! ### Offset-extraction inverse -/

/-- **Offset-extraction inverse**: reading `extractFieldOffsets`
back off the encoder's own fixed-section output recovers exactly
the running offsets `serializeFieldsAux` wrote (`varOffsetsOf`).

Generalized over an arbitrary already-consumed prefix `pre` (so
induction can peel one field's contribution off the front via the
append-shift bridges above) and an arbitrary suffix `suf` following
the fixed section. The `suf` generality is what keeps this proof
tractable: `extractFieldOffsets` never reads past the fixed prefix
(every `uint32` placeholder it decodes lies entirely within `.1`,
by construction of `fixedSectionSizeFields`), so the buffer's tail
can be *anything*, in particular `.2 ++ (whatever came after the
whole container)`, without the invariant ever having to track where
the variable region physically sits. An earlier attempt at this
proof threaded `.2` through the induction to try to match the
walker's eventual needs one step ahead of time; that tangled the
induction for no benefit, since `.2`'s position is exactly what this
lemma doesn't need to know.

The `h_bound` hypothesis is the uint32-overflow guard: every offset
the encoder writes is `varOff ≤ o ≤ varOff + (total variable bytes
written so far)`, so bounding that sum by `2 ^ 32` keeps every
offset's `UInt32` round-trip exact (`toNat_toUInt32_of_lt`).
Specializes to `pre = .empty` for the top-level statement the (later)
roundtrip walker needs. -/
theorem extractFieldOffsets_serializeFieldsAux :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs) (varOff : Nat) (pre : ByteArray),
    FieldsFixedSizeOk fs vs →
    varOff + (SSZType.serializeFieldsAux fs vs varOff).2.size < 2 ^ 32 →
    ∀ (suf : ByteArray),
    extractFieldOffsets (pre ++ ((SSZType.serializeFieldsAux fs vs varOff).1 ++ suf)) fs pre.size
      = .ok (varOffsetsOf fs vs varOff) := by
  intro fs
  induction fs with
  | nil =>
    intro vs varOff pre _ _ suf
    unfold SSZType.serializeFieldsAux varOffsetsOf extractFieldOffsets
    rfl
  | cons t ts ih =>
    intro vs varOff pre h_ok h_bound suf
    unfold FieldsFixedSizeOk at h_ok
    obtain ⟨h_head, h_tail⟩ := h_ok
    by_cases h_fixed : t.isFixedSize = true
    · -- Fixed field: `.1` gets `serialize t vs.1 ++ fixTail`, `.2`
      -- unchanged. `extractFieldOffsets` advances `off` by
      -- `t.fixedByteSize` without reading.
      have h_size_head : (SSZType.serialize t vs.1).size = t.fixedByteSize := h_head h_fixed
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
      rw [h_enc2] at h_bound
      rw [h_enc]
      have h_reassoc :
          pre ++ (SSZType.serialize t vs.1 ++ (SSZType.serializeFieldsAux ts vs.2 varOff).1 ++ suf)
            = (pre ++ SSZType.serialize t vs.1) ++
                ((SSZType.serializeFieldsAux ts vs.2 varOff).1 ++ suf) := by
        simp only [ByteArray.append_assoc]
      rw [h_reassoc]
      have h_ih := ih vs.2 varOff (pre ++ SSZType.serialize t vs.1) h_tail h_bound suf
      have h_presize : (pre ++ SSZType.serialize t vs.1).size = pre.size + t.fixedByteSize := by
        rw [ByteArray.size_append, h_size_head]
      unfold extractFieldOffsets
      simp only [h_fixed, if_true]
      rw [show pre.size + t.fixedByteSize = (pre ++ SSZType.serialize t vs.1).size from
            h_presize.symm, h_ih]
      simp only [varOffsetsOf, h_fixed, if_true]
    · -- Variable field: `.1` gets `offBytes ++ fixTail`.
      -- `extractFieldOffsets` reads the offset placeholder (via the
      -- uint32 bridge), then advances by 4; the field's own body
      -- `xBytes` lives entirely in `.2`, which this theorem never
      -- inspects.
      have h_fixed' : t.isFixedSize = false := by
        cases h : t.isFixedSize <;> simp_all
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
      rw [h_enc2] at h_bound
      have h_bound' : varOff + (SSZType.serialize t vs.1).size < 2 ^ 32 := by
        rw [ByteArray.size_append] at h_bound; omega
      have h_bound_tail :
          (varOff + (SSZType.serialize t vs.1).size) +
            (SSZType.serializeFieldsAux ts vs.2
              (varOff + (SSZType.serialize t vs.1).size)).2.size < 2 ^ 32 := by
        rw [ByteArray.size_append] at h_bound; omega
      have h_ih :=
        ih vs.2 (varOff + (SSZType.serialize t vs.1).size)
          (pre ++ uint32LE (Nat.toUInt32 varOff)) h_tail h_bound_tail suf
      have h_presize : (pre ++ uint32LE (Nat.toUInt32 varOff)).size = pre.size + 4 := by
        rw [ByteArray.size_append, size_uint32LE]
      rw [h_enc]
      have h_reassoc :
          pre ++
              (uint32LE (Nat.toUInt32 varOff) ++
                (SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).1 ++ suf)
            = (pre ++ uint32LE (Nat.toUInt32 varOff)) ++
                ((SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).1 ++ suf) := by
        simp only [ByteArray.append_assoc]
      rw [h_reassoc]
      unfold extractFieldOffsets
      simp only [h_fixed', if_false, Bool.false_eq_true]
      have h_read :
          readUInt32LE
              ((pre ++ uint32LE (Nat.toUInt32 varOff)) ++
                ((SSZType.serializeFieldsAux ts vs.2
                  (varOff + (SSZType.serialize t vs.1).size)).1 ++ suf))
              pre.size
            = some (Nat.toUInt32 varOff) := by
        rw [ByteArray.append_assoc]
        have hshift := readUInt32LE_append_shift pre
          (uint32LE (Nat.toUInt32 varOff) ++
            ((SSZType.serializeFieldsAux ts vs.2
              (varOff + (SSZType.serialize t vs.1).size)).1 ++ suf))
          0 (by rw [ByteArray.size_append, size_uint32LE]; omega)
        simp only [Nat.add_zero] at hshift
        rw [hshift, readUInt32LE_uint32LE_append]
      rw [h_read]
      dsimp only
      have hBPLO : SizzLean.Spec.BYTES_PER_LENGTH_OFFSET = 4 := rfl
      rw [hBPLO, show pre.size + 4 = (pre ++ uint32LE (Nat.toUInt32 varOff)).size from
            h_presize.symm, h_ih]
      dsimp only
      have h_toNat : (Nat.toUInt32 varOff).toNat = varOff :=
        toNat_toUInt32_of_lt varOff (by omega)
      rw [h_toNat]
      simp only [varOffsetsOf, h_fixed', if_false, Bool.false_eq_true]

end SizzLean.Proofs
