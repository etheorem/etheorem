import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SerializeSize
import SizzLean.Proofs.FixedElems

/-!
# `SizzLean.Proofs.VectorFixed`: `.vector t n` arm with fixed-size `t`, `n > 0`

Closes `decode_encode` and `encode_size_le_max` for `.vector t n`
when `t` is `BasicSupported` + fixed-size and `n > 0`.

## Roundtrip recipe

1. `serialize (.vector t n) v = serializeFixedElems t v.toList`
   (by the encoder's `t.isFixedSize` branch).
2. `decode (.vector t n) (serializeFixedElems t v.toList)`
   dispatches through `deserializeFixedElems t n …`.
3. Our shared helper `deserializeFixedElems_serializeFixedElems`
   (in `Proofs/FixedElems.lean`) turns that call into
   `.ok (v.toList, n * sz)`.
4. The decoder then builds `⟨v.toList.toArray, _⟩` which
   propositionally equals `v` (a `Vector` is determined by its
   underlying `Array`).
5. The bytes-consumed count `n * sz` equals
   `(serialize (.vector t n) v).size` via `size_serialize_eq_fixedByteSize`.

## Element-IH parameter

`decode_encode_vectorFixed` is parameterised by the
**decode/encode roundtrip on the element type `t`**
(`h_decode_encode_t`). This lets the main mutual block in
`Proofs/Roundtrip.lean` recurse into `decode_encode (h_t : …)`
without needing this file to be part of the mutual block, the
recursion happens at the dispatch level.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- Roundtrip for `.vector t n` with `t` BasicSupported + fixed
and `n > 0`. Parameterised by the element-type decode/encode
roundtrip, the dispatch in `Proofs/Roundtrip.lean` provides it
via mutual recursion on `BasicSupported`. -/
theorem decode_encode_vectorFixed
    (t : SSZType) (n : Nat) (h_pos : 0 < n)
    (h_t : SSZType.BasicSupported t)
    (h_t_fixed : t.isFixedSize = true)
    (h_decode_encode_t : ∀ y : t.interp,
      SSZType.deserialize t (SSZType.serialize t y) =
        .ok (y, (SSZType.serialize t y).size))
    (v : Vector t.interp n) :
    SSZType.deserialize (.vector t n) (SSZType.serialize (.vector t n) v) =
      .ok (v, (SSZType.serialize (.vector t n) v).size) := by
  -- Step 1: serialize = serializeFixedElems t v.toList (encoder dispatches on h_t_fixed).
  have h_size_t : ∀ y : t.interp, (SSZType.serialize t y).size = t.fixedByteSize :=
    fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y
  have h_serialize_eq :
      SSZType.serialize (.vector t n) v =
        SSZType.serializeFixedElems t v.toList := by
    unfold SSZType.serialize
    simp [h_t_fixed]
  -- Step 2: total serialized size = n * t.fixedByteSize.
  have h_total_size :
      (SSZType.serialize (.vector t n) v).size = n * t.fixedByteSize := by
    rw [size_serialize_eq_fixedByteSize (.vectorFixed h_pos h_t h_t_fixed)
        (show SSZType.isFixedSize (.vector t n) = true by
          unfold SSZType.isFixedSize; exact h_t_fixed) v]
    show SSZType.fixedByteSize (.vector t n) = n * t.fixedByteSize
    simp only [SSZType.fixedByteSize]
    rw [Nat.mul_comm]
  -- Step 3: helper turns deserializeFixedElems into .ok (v.toList, n * sz).
  have h_inv := deserializeFixedElems_serializeFixedElems t
                  h_decode_encode_t h_size_t v.toList
  -- Now compute the full deserialize. Carefully: use h_total_size to keep
  -- the RHS as `(serialize (.vector t n) v).size`, not `(serializeFixedElems ...).size`.
  rw [show (SSZType.serialize (.vector t n) v).size = n * t.fixedByteSize from h_total_size]
  rw [h_serialize_eq]
  unfold SSZType.deserialize
  have hn : ¬ n = 0 := Nat.ne_of_gt h_pos
  simp only [hn, if_false]
  simp only [h_t_fixed, if_true]
  rw [Vector.length_toList] at h_inv
  rw [h_inv]
  have h_sz_arr : v.toList.toArray.size = n := by
    rw [List.size_toArray, Vector.length_toList]
  simp only [h_sz_arr, dite_true]
  -- Goal: .ok (Vector.mk v.toList.toArray …, n*sz) = .ok (v, n*sz)
  -- Destructure `v` as a `Vector.mk arr h` (Vector is single-constructor) and
  -- close via `v.toList.toArray = v.toArray` (`Array.toArray_toList`).
  cases v with
  | mk arr h =>
    show Except.ok (Vector.mk arr.toList.toArray _, n * t.fixedByteSize) = _
    simp [Array.toArray_toList]

/-- Size bound for `.vector t n` with `t` fixed-size, `n > 0`.
The serialized buffer has size `n * t.fixedByteSize`, which
is ≤ `maxByteLength (.vector t n) = maxByteLength t * n`. The
`n > 0` precondition lets us pick `v[0]` as a witness for
deriving `fixedByteSize t ≤ maxByteLength t`. -/
theorem encode_size_le_max_vectorFixed
    (t : SSZType) (n : Nat) (h_pos : 0 < n)
    (h_t : SSZType.BasicSupported t)
    (h_t_fixed : t.isFixedSize = true)
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (v : Vector t.interp n) :
    (SSZType.serialize (.vector t n) v).size ≤
      SSZType.maxByteLength (.vector t n) := by
  have h_size_t : ∀ y : t.interp, (SSZType.serialize t y).size = t.fixedByteSize :=
    fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y
  -- Pick the first element of `v` (well-defined since `n > 0`) as a witness for
  -- deriving `fixedByteSize t ≤ maxByteLength t`: `(serialize t v[0]).size = fixedByteSize t`
  -- (h_size_t) and `≤ maxByteLength t` (h_max_t).
  have h_fixed_le_max : t.fixedByteSize ≤ SSZType.maxByteLength t := by
    have h := h_max_t (v[0]'h_pos)
    rw [h_size_t (v[0]'h_pos)] at h
    exact h
  -- Concrete size of the encoded vector:
  have h_size : (SSZType.serialize (.vector t n) v).size = n * t.fixedByteSize := by
    rw [size_serialize_eq_fixedByteSize (.vectorFixed h_pos h_t h_t_fixed)
        (show SSZType.isFixedSize (.vector t n) = true by
          unfold SSZType.isFixedSize; exact h_t_fixed) v]
    show SSZType.fixedByteSize (.vector t n) = n * t.fixedByteSize
    simp only [SSZType.fixedByteSize]
    rw [Nat.mul_comm]
  rw [h_size]
  show n * t.fixedByteSize ≤ SSZType.maxByteLength (.vector t n)
  simp only [SSZType.maxByteLength]
  rw [Nat.mul_comm (SSZType.maxByteLength t) n]
  exact Nat.mul_le_mul_left n h_fixed_le_max

end SizzLean.Proofs
