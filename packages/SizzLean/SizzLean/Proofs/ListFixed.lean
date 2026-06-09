import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SerializeSize
import SizzLean.Proofs.FixedElems

/-!
# `SizzLean.Proofs.ListFixed`: `.list t cap` arm with fixed-size `t`

Closes `decode_encode` and `encode_size_le_max` for `.list t cap`
when `t` is `BasicSupported` + fixed-size **and** has a strictly
positive `fixedByteSize` (the spec's decoder errors on
zero-element-size lists, see `if sz = 0 then .error .tooShort` in
`Spec/Deserialize.lean`'s `.list` arm).

## Recipe

Mirrors `VectorFixed`:

1. `serialize (.list t cap) xs = serializeFixedElems t xs.val.toList`
   (encoder's `t.isFixedSize` branch).
2. Decoder computes `count = b.size / sz`; with the encoded buffer
   having `size = xs.val.size * sz`, this is `xs.val.size`.
3. `count ≤ cap` because `xs.val.size ≤ cap` (subtype proof).
4. `count * sz = b.size` (closed form).
5. `deserializeFixedElems` yields `.ok (xs.val.toList, count * sz)`
   via our shared helper.
6. The subtype `⟨xs.val.toList.toArray, _⟩` propositionally equals
   `xs` (toArray on toList is identity).

The `0 < t.fixedByteSize` precondition rules out the
`.container []`-element pathology where the decoder's `sz = 0`
guard would fail.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- Roundtrip for `.list t cap` with `t` BasicSupported + fixed
+ positive element size. Parameterised by the element-type
decode/encode roundtrip. -/
theorem decode_encode_listFixed
    (t : SSZType) (cap : Nat)
    (h_t : SSZType.BasicSupported t)
    (h_t_fixed : t.isFixedSize = true)
    (h_sz_pos : 0 < t.fixedByteSize)
    (h_decode_encode_t : ∀ y : t.interp,
      SSZType.deserialize t (SSZType.serialize t y) =
        .ok (y, (SSZType.serialize t y).size))
    (xs : { ys : Array t.interp // ys.size ≤ cap }) :
    SSZType.deserialize (.list t cap) (SSZType.serialize (.list t cap) xs) =
      .ok (xs, (SSZType.serialize (.list t cap) xs).size) := by
  have h_size_t : ∀ y : t.interp, (SSZType.serialize t y).size = t.fixedByteSize :=
    fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y
  -- Step 1: serialize = serializeFixedElems t xs.val.toList.
  have h_serialize_eq :
      SSZType.serialize (.list t cap) xs =
        SSZType.serializeFixedElems t xs.val.toList := by
    unfold SSZType.serialize
    simp [h_t_fixed]
  -- Step 2: total size = xs.val.size * fixedByteSize t.
  have h_list_len : xs.val.toList.length = xs.val.size := by
    simp
  have h_serialize_size :
      (SSZType.serialize (.list t cap) xs).size =
        xs.val.size * t.fixedByteSize := by
    rw [h_serialize_eq]
    have := serializeFixedElems_size_aux t t.fixedByteSize h_size_t xs.val.toList
    rw [this, h_list_len]
  -- Step 3: helper yields .ok (xs.val.toList, xs.val.size * sz).
  have h_inv := deserializeFixedElems_serializeFixedElems t
                  h_decode_encode_t h_size_t xs.val.toList
  rw [h_list_len] at h_inv
  -- Step 4: assemble the full deserialize.
  rw [h_serialize_size, h_serialize_eq]
  unfold SSZType.deserialize
  simp only [h_t_fixed, if_true]
  -- Decoder guards:
  --  (a) sz ≠ 0 (h_sz_pos)
  --  (b) count := b.size / sz = xs.val.size (computed below)
  --  (c) count ≤ cap (from xs.property)
  --  (d) count * sz = b.size (from h_serialize_size)
  have h_sz_ne : ¬ t.fixedByteSize = 0 := Nat.ne_of_gt h_sz_pos
  simp only [h_sz_ne, if_false]
  -- Now: b.size = xs.val.size * sz (after rw); count = (xs.val.size * sz) / sz = xs.val.size.
  have h_count :
      (SSZType.serializeFixedElems t xs.val.toList).size / t.fixedByteSize = xs.val.size := by
    have h_size_eq :
        (SSZType.serializeFixedElems t xs.val.toList).size = xs.val.size * t.fixedByteSize := by
      rw [serializeFixedElems_size_aux t t.fixedByteSize h_size_t xs.val.toList, h_list_len]
    rw [h_size_eq, Nat.mul_div_cancel _ h_sz_pos]
  rw [h_count]
  -- count > cap branch: xs.val.size > cap is false because xs.property is xs.val.size ≤ cap.
  have h_le_cap : ¬ xs.val.size > cap := Nat.not_lt.mpr xs.property
  simp only [h_le_cap, if_false]
  -- count * sz = b.size branch: xs.val.size * sz = (serializeFixedElems …).size (true).
  have h_size_match :
      ¬ xs.val.size * t.fixedByteSize ≠
        (SSZType.serializeFixedElems t xs.val.toList).size := by
    intro h
    apply h
    rw [serializeFixedElems_size_aux t t.fixedByteSize h_size_t xs.val.toList, h_list_len]
  simp only [h_size_match, if_false]
  -- Now: match deserializeFixedElems … with .ok …
  rw [h_inv]
  -- Final: dependent-if on arr.size ≤ cap, then Vector-style subtype equality.
  have h_arr_sz : xs.val.toList.toArray.size ≤ cap := by
    rw [List.size_toArray, h_list_len]; exact xs.property
  simp only [h_arr_sz, dite_true]

/-- Size bound for `.list t cap`. `(serialize …).size = xs.val.size * sz`;
`maxByteLength = cap * maxByteLength t`.

For the empty list (`xs.val.size = 0`) the bound is trivial: LHS
is 0. For a non-empty list, we use `xs.val[0]` to derive
`fixedByteSize t ≤ maxByteLength t` via the per-element bound +
`size_serialize_eq_fixedByteSize`. -/
theorem encode_size_le_max_listFixed
    (t : SSZType) (cap : Nat)
    (h_t : SSZType.BasicSupported t)
    (h_t_fixed : t.isFixedSize = true)
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (xs : { ys : Array t.interp // ys.size ≤ cap }) :
    (SSZType.serialize (.list t cap) xs).size ≤
      SSZType.maxByteLength (.list t cap) := by
  have h_size_t : ∀ y : t.interp, (SSZType.serialize t y).size = t.fixedByteSize :=
    fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y
  -- Concrete size of the encoded list:
  have h_size : (SSZType.serialize (.list t cap) xs).size =
      xs.val.size * t.fixedByteSize := by
    unfold SSZType.serialize
    simp only [h_t_fixed, if_true]
    have h_list_len : xs.val.toList.length = xs.val.size := by simp
    rw [serializeFixedElems_size_aux t t.fixedByteSize h_size_t xs.val.toList, h_list_len]
  rw [h_size]
  show xs.val.size * t.fixedByteSize ≤ SSZType.maxByteLength (.list t cap)
  simp only [SSZType.maxByteLength]
  -- Case-split on `xs.val.size = 0` to avoid needing an `Inhabited` instance.
  by_cases h_empty : xs.val.size = 0
  · rw [h_empty]; simp
  · -- xs.val is non-empty; use xs.val[0] as the witness for fixedByteSize ≤ maxByteLength.
    have h_pos : 0 < xs.val.size := Nat.pos_of_ne_zero h_empty
    have h_fixed_le_max : t.fixedByteSize ≤ SSZType.maxByteLength t := by
      have h := h_max_t (xs.val[0]'h_pos)
      rw [h_size_t (xs.val[0]'h_pos)] at h
      exact h
    calc xs.val.size * t.fixedByteSize
        ≤ cap * t.fixedByteSize := Nat.mul_le_mul_right _ xs.property
      _ ≤ cap * SSZType.maxByteLength t := Nat.mul_le_mul_left _ h_fixed_le_max

end SizzLean.Proofs
