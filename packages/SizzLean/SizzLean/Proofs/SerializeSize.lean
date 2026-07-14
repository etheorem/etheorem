import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SimpAttrs
import SizzLean.Proofs.BitPack
import SizzLean.Proofs.UIntWide

/-!
# `SizzLean.Proofs.SerializeSize`: the shared size-prereq lemma

For any `s` that is *both* `BasicSupported` and `isFixedSize`, the
serialized output has size exactly `s.fixedByteSize`, independent
of the value. This is *the* prerequisite for the composite arms
(`VectorFixed`, `ListFixed`, `ContainerFixed`): each decoder needs
to know exactly how many bytes the encoder produced to slice the
buffer correctly.

The proof is structurally recursive on `BasicSupported`. Two
mutually structural-recursive theorems:

* `size_serialize_eq_fixedByteSize`: main lemma, descends on
  `BasicSupported s`; for `vectorFixed` recurses on the element
  type's witness, for `containerFixed` calls the field-list
  helper below.
* `size_serializeFieldsAux_fix`: helper for the
  `serializeFieldsAux` field walker; descends on
  `BasicSupportedFieldsFixed fs`. Returns *both* the size of the
  fixed-prefix output **and** the witness that the variable-body
  output is `.empty`, they travel together because the
  recursive case needs to thread both through the cons.

A small non-mutual aux lemma `serializeFixedElems_size_aux`
factors out the
`(serializeFixedElems t xs).size = xs.length * sz` calculation,
parameterised by the element-size hypothesis. This lets the
`vectorFixed` arm of the main lemma cite the aux lemma directly
without needing a third partner in the mutual block.

## Why `cases ... with | … => rename_i` instead of named-arg `cases`

Lean 4.29's `cases h with | ctor name₁ … nameₖ` only names the
*explicit* constructor arguments; the *implicit* ones (e.g. the
`{t : SSZType}` in `vectorFixed`) get anonymous hypothesis names
(`t✝` etc.). Reaching them requires either `@`-binding (which
also forces naming every implicit) or a follow-up `rename_i`.
We use `rename_i` consistently, less syntactic noise and avoids
the need to enumerate all implicits at every cases line.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- For any `t` whose serialization has constant size `sz` per
element, `serializeFixedElems t xs` has size `xs.length * sz`.
Not mutually recursive, induct on `xs` directly; the
element-size hypothesis is provided by the caller. Used both by
the main mutual block here (for the `vectorFixed` arm) and by
the `VectorFixed` / `ListFixed` proof files. -/
theorem serializeFixedElems_size_aux
    (t : SSZType) (sz : Nat)
    (h_elem : ∀ y : t.interp, (SSZType.serialize t y).size = sz)
    (xs : List t.interp) :
    (SSZType.serializeFixedElems t xs).size = xs.length * sz := by
  induction xs with
  | nil =>
    unfold SSZType.serializeFixedElems
    simp [ByteArray.size_empty]
  | cons x xs' ih =>
    show (SSZType.serializeFixedElems t (x :: xs')).size = (x :: xs').length * sz
    unfold SSZType.serializeFixedElems
    rw [ByteArray.size_append, h_elem, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

mutual

/-- Main size lemma: for any `BasicSupported`, `isFixedSize` shape
the serialized output has size exactly `fixedByteSize`. -/
theorem size_serialize_eq_fixedByteSize :
    ∀ {s : SSZType}, SSZType.BasicSupported s → s.isFixedSize = true →
    ∀ (x : s.interp), (SSZType.serialize s x).size = SSZType.fixedByteSize s := by
  intro s h_s h_fixed x
  cases h_s with
  | uintN8 =>
    let x' : UInt8 := x
    show (SSZType.serialize (.uintN 8) x').size = SSZType.fixedByteSize (.uintN 8)
    simp [SSZType.serialize, SSZType.fixedByteSize,
          ByteArray.size_push, ByteArray.size_empty]
  | uintN16 =>
    let x' : UInt16 := x
    show (SSZType.serialize (.uintN 16) x').size = SSZType.fixedByteSize (.uintN 16)
    simp [SSZType.serialize, SSZType.fixedByteSize, uint16LE,
          ByteArray.size_push, ByteArray.size_empty]
  | uintN32 =>
    let x' : UInt32 := x
    show (SSZType.serialize (.uintN 32) x').size = SSZType.fixedByteSize (.uintN 32)
    simp [SSZType.serialize, SSZType.fixedByteSize, uint32LE,
          ByteArray.size_push, ByteArray.size_empty]
  | uintN64 =>
    let x' : UInt64 := x
    show (SSZType.serialize (.uintN 64) x').size = SSZType.fixedByteSize (.uintN 64)
    simp [SSZType.serialize, SSZType.fixedByteSize, uint64LE,
          ByteArray.size_push, ByteArray.size_empty]
  | uintN128 =>
    let x' : BitVec 128 := x
    show (SSZType.serialize (.uintN 128) x').size = SSZType.fixedByteSize (.uintN 128)
    rw [size_serialize_uintN128]
    simp [SSZType.fixedByteSize]
  | uintN256 =>
    let x' : BitVec 256 := x
    show (SSZType.serialize (.uintN 256) x').size = SSZType.fixedByteSize (.uintN 256)
    rw [size_serialize_uintN256]
    simp [SSZType.fixedByteSize]
  | bool =>
    let b : Bool := x
    show (SSZType.serialize .bool b).size = SSZType.fixedByteSize .bool
    cases b <;> simp [SSZType.serialize, SSZType.fixedByteSize,
                      ByteArray.size_push, ByteArray.size_empty]
  | vectorFixed _h_pos h_t h_t_fixed =>
    rename_i t n
    let v : Vector t.interp n := x
    have h_elem : ∀ y : t.interp, (SSZType.serialize t y).size = SSZType.fixedByteSize t :=
      fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y
    have h_helper :
        (SSZType.serializeFixedElems t v.toList).size = v.toList.length * SSZType.fixedByteSize t :=
      serializeFixedElems_size_aux t (SSZType.fixedByteSize t) h_elem v.toList
    show (SSZType.serialize (.vector t n) v).size = SSZType.fixedByteSize (.vector t n)
    unfold SSZType.serialize
    -- `if t.isFixedSize then ... else ...`: rewrite using `h_t_fixed : t.isFixedSize = true`.
    simp only [h_t_fixed, ↓reduceIte]
    rw [h_helper, Vector.length_toList]
    -- Reduce `(.vector t n).fixedByteSize` to `t.fixedByteSize * n`, then mul_comm.
    simp only [SSZType.fixedByteSize]
    rw [Nat.mul_comm]
  | listFixed _ _ =>
    -- `(.list t cap).isFixedSize = false`; `h_fixed : false = true` is absurd.
    simp [SSZType.isFixedSize] at h_fixed
  | bitvector _h_pos =>
    rename_i n
    let bv : BitVec n := x
    show (SSZType.serialize (.bitvector n) bv).size = SSZType.fixedByteSize (.bitvector n)
    rw [size_serialize_bitvector]
    simp [SSZType.fixedByteSize]
  | bitlist =>
    -- `(.bitlist cap).isFixedSize = false`; absurd like `listFixed`.
    simp [SSZType.isFixedSize] at h_fixed
  | containerFixed h_fs =>
    rename_i fs
    let vs : SSZType.interpFields fs := x
    have h_fields :=
      size_serializeFieldsAux_fix h_fs vs (SSZType.fixedSectionSizeFields fs)
    show (SSZType.serialize (.container fs) vs).size = SSZType.fixedByteSize (.container fs)
    unfold SSZType.serialize
    simp [h_fields.1, h_fields.2, SSZType.fixedByteSize]

/-- For `BasicSupportedFieldsFixed fs`, `serializeFieldsAux` produces
a fixed-prefix output of size `fixedByteSizeFields fs` *and* an
empty variable-body output. The two facts travel together because
the `cons` step needs the IH at both slots simultaneously. -/
theorem size_serializeFieldsAux_fix :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFieldsFixed fs →
    ∀ (vs : SSZType.interpFields fs) (varOff : Nat),
      (SSZType.serializeFieldsAux fs vs varOff).1.size =
        SSZType.fixedByteSizeFields fs ∧
      (SSZType.serializeFieldsAux fs vs varOff).2 = .empty := by
  intro fs h_fs vs varOff
  cases h_fs with
  | nil =>
    unfold SSZType.serializeFieldsAux SSZType.fixedByteSizeFields
    simp [ByteArray.size_empty]
  | cons h_t h_t_fixed h_ts =>
    rename_i t ts
    -- `vs : interpFields (t :: ts) = t.interp × interpFields ts`.
    have h_head : (SSZType.serialize t vs.1).size = SSZType.fixedByteSize t :=
      size_serialize_eq_fixedByteSize h_t h_t_fixed vs.1
    have h_tail := size_serializeFieldsAux_fix h_ts vs.2 varOff
    refine ⟨?_, ?_⟩
    · unfold SSZType.serializeFieldsAux SSZType.fixedByteSizeFields
      simp [h_t_fixed, ByteArray.size_append, h_head, h_tail.1]
    · unfold SSZType.serializeFieldsAux
      simp [h_t_fixed, h_tail.2]

end

end SizzLean.Proofs
