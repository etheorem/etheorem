import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Proofs.SerializeSize

/-!
# `SizzLean.Proofs.FixedElems`: the `deserializeFixedElems` inverse

Shared helper for the `VectorFixed` and `ListFixed` arms:
proves that `deserializeFixedElems` is the left inverse of
`serializeFixedElems` when the element type is `BasicSupported`
and fixed-size.

The spec functions have asymmetric shapes: `serializeFixedElems`
just concatenates `serialize t xᵢ` for each element, but
`deserializeFixedElems` uses a *tail-recursive accumulator with a
final reverse*, threading `(off, acc, accSz)` through the
recursion. The proof generalises over the accumulator and a
per-slice matching hypothesis.

## Lemma path

1. **`extract_serializeFixedElems`**: the `i`-th `sz`-byte
   slice of `serializeFixedElems t xs` is exactly `serialize t
   (xs[i])`. Induction on `xs` (handles `i = 0` via
   `extract_append_eq_left`, `i = i'+1` via the shift lemma
   `extract_append_size_add`).
2. **`deserializeFixedElems_eq_of_slice`**: given the buffer's
   per-slice matching, the accumulator-based decoder returns
   `acc.reverse ++ xs`. Induction on `xs` with `off`, `acc`,
   `accSz` generalised.
3. **`deserializeFixedElems_serializeFixedElems`**: combines
   the two: callers (Vector / List) cite this directly.

The helper is parameterised by `decode_encode` on the element
type so that it can be invoked from the main mutual block
without re-introducing mutual recursion at this level.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- The `i`-th `sz`-byte slice of `serializeFixedElems t xs` is
exactly the encoded i-th element, provided every encode has size
exactly `sz`. -/
theorem extract_serializeFixedElems
    (t : SSZType) (sz : Nat)
    (h_elem_size : ∀ x : t.interp, (SSZType.serialize t x).size = sz)
    (xs : List t.interp) (i : Nat) (h_i : i < xs.length) :
    (SSZType.serializeFixedElems t xs).extract (i * sz) ((i + 1) * sz) =
      SSZType.serialize t (xs[i]'h_i) := by
  induction xs generalizing i with
  | nil => simp at h_i
  | cons y ys ih =>
    -- `serializeFixedElems t (y :: ys) = serialize t y ++ serializeFixedElems t ys`.
    unfold SSZType.serializeFixedElems
    cases i with
    | zero =>
      -- Goal: `(serialize t y ++ _).extract (0 * sz) ((0 + 1) * sz) = serialize t (y :: ys)[0]`.
      simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul,
                 List.getElem_cons_zero]
      have h_y : (SSZType.serialize t y).size = sz := h_elem_size y
      rw [show sz = (SSZType.serialize t y).size from h_y.symm]
      exact ByteArray.extract_append_eq_left rfl
    | succ i' =>
      -- Goal: extract ((i'+1)*sz) ((i'+2)*sz) on the append.
      -- Use the shift lemma `extract_append_size_add` after rewriting
      -- both offsets to `(serialize t y).size + …`.
      have h_y : (SSZType.serialize t y).size = sz := h_elem_size y
      have h_i' : i' < ys.length := by
        rw [List.length_cons] at h_i; omega
      have h_lhs : (i' + 1) * sz = (SSZType.serialize t y).size + i' * sz := by
        rw [h_y, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      have h_rhs : (i' + 1 + 1) * sz = (SSZType.serialize t y).size + (i' + 1) * sz := by
        rw [h_y, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [h_lhs, h_rhs, ByteArray.extract_append_size_add]
      -- LHS now: `(serializeFixedElems t ys).extract (i' * sz) ((i' + 1) * sz)`.
      -- RHS: serialize t ((y :: ys)[i' + 1]).
      -- By List.getElem_cons_succ: (y :: ys)[i' + 1] = ys[i'].
      simp only [List.getElem_cons_succ]
      exact ih i' h_i'

/-- The accumulator-based decoder inverts the concatenated
serializer, returning the elements in their original order
(despite the internal reverse). The `h_slice` hypothesis
discharges the per-step buffer match. -/
theorem deserializeFixedElems_eq_of_slice
    (t : SSZType)
    (h_decode_encode_t : ∀ x : t.interp,
      SSZType.deserialize t (SSZType.serialize t x) =
        .ok (x, (SSZType.serialize t x).size))
    (h_serialize_size : ∀ x : t.interp,
      (SSZType.serialize t x).size = t.fixedByteSize) :
    ∀ (xs : List t.interp) (b : ByteArray) (off : Nat)
      (acc : List t.interp) (accSz : Nat),
      (∀ i, ∀ h : i < xs.length,
        b.extract (off + i * t.fixedByteSize) (off + (i + 1) * t.fixedByteSize) =
          SSZType.serialize t (xs[i]'h)) →
      SSZType.deserializeFixedElems t xs.length b off t.fixedByteSize acc accSz =
        .ok (acc.reverse ++ xs, accSz + xs.length * t.fixedByteSize) := by
  intro xs
  induction xs with
  | nil =>
    intro b off acc accSz _h_slice
    unfold SSZType.deserializeFixedElems
    simp
  | cons x xs' ih =>
    intro b off acc accSz h_slice
    -- count = xs'.length + 1; the recursive step processes `x`, then recurses on xs'.
    show SSZType.deserializeFixedElems t (xs'.length + 1) b off t.fixedByteSize acc accSz = _
    unfold SSZType.deserializeFixedElems
    -- The chunk for i = 0 of (x :: xs') is `serialize t x` by `h_slice 0`.
    have h_chunk : b.extract off (off + t.fixedByteSize) = SSZType.serialize t x := by
      have := h_slice 0 (by simp)
      simp at this; exact this
    simp only [h_chunk, h_decode_encode_t x, h_serialize_size x, ne_eq,
               not_true_eq_false, ite_false]
    -- Recursive call: deserializeFixedElems t xs'.length b (off + sz) sz (x :: acc) (accSz + sz).
    -- Apply IH on xs' with shifted slice hypothesis.
    have h_slice' :
        ∀ i, ∀ h : i < xs'.length,
          b.extract ((off + t.fixedByteSize) + i * t.fixedByteSize)
              ((off + t.fixedByteSize) + (i + 1) * t.fixedByteSize) =
            SSZType.serialize t (xs'[i]'h) := by
      intro i h
      have h_idx : i + 1 < (x :: xs').length := by
        rw [List.length_cons]; omega
      have h_at := h_slice (i + 1) h_idx
      -- Goal LHS: b.extract (off + sz + i*sz) (off + sz + (i+1)*sz)
      -- h_at: b.extract (off + (i+1)*sz) (off + (i+1+1)*sz) = t.serialize (x :: xs')[i+1]
      -- Rewrite arithmetically: (i+1)*sz = sz + i*sz; (i+1+1)*sz = sz + (i+1)*sz.
      have e1 : off + (i + 1) * t.fixedByteSize =
                off + t.fixedByteSize + i * t.fixedByteSize := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc,
            Nat.add_comm (i * t.fixedByteSize) t.fixedByteSize]
      have e2 : off + (i + 1 + 1) * t.fixedByteSize =
                off + t.fixedByteSize + (i + 1) * t.fixedByteSize := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc,
            Nat.add_comm ((i + 1) * t.fixedByteSize) t.fixedByteSize]
      rw [← e1, ← e2, h_at]
      -- (x :: xs')[i + 1] = xs'[i] by List.getElem_cons_succ
      simp [List.getElem_cons_succ]
    have h_ih := ih b (off + t.fixedByteSize) (x :: acc) (accSz + t.fixedByteSize) h_slice'
    rw [h_ih]
    -- LHS: .ok ((x :: acc).reverse ++ xs', (accSz + sz) + xs'.length * sz)
    -- RHS: .ok (acc.reverse ++ (x :: xs'), accSz + (xs'.length + 1) * sz)
    -- Reconcile the list (cons + reverse) and the arithmetic.
    rw [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons]
    -- Now LHS: .ok (acc.reverse ++ x :: xs', accSz + sz + xs'.length * sz)
    -- RHS: .ok (acc.reverse ++ x :: xs', accSz + (xs'.length + 1) * sz)
    -- Only the snd of the pair differs by arithmetic.
    congr 1
    -- goal: (acc.reverse ++ x :: xs', accSz + sz + xs'.length * sz) = (acc.reverse ++ x :: xs', accSz + (xs'.length + 1) * sz)
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    -- accSz + sz + xs'.length * sz = accSz + (xs'.length + 1) * sz
    rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc,
        Nat.add_comm (xs'.length * t.fixedByteSize) t.fixedByteSize]

/-- Main inverse lemma: combines `extract_serializeFixedElems`
with `deserializeFixedElems_eq_of_slice` at `b :=
serializeFixedElems t xs`, `off := 0`, `acc := []`, `accSz := 0`. -/
theorem deserializeFixedElems_serializeFixedElems
    (t : SSZType)
    (h_decode_encode_t : ∀ x : t.interp,
      SSZType.deserialize t (SSZType.serialize t x) =
        .ok (x, (SSZType.serialize t x).size))
    (h_serialize_size : ∀ x : t.interp,
      (SSZType.serialize t x).size = t.fixedByteSize)
    (xs : List t.interp) :
    SSZType.deserializeFixedElems t xs.length
        (SSZType.serializeFixedElems t xs) 0 t.fixedByteSize [] 0 =
      .ok (xs, xs.length * t.fixedByteSize) := by
  have h_extract :
      ∀ i, ∀ h : i < xs.length,
        (SSZType.serializeFixedElems t xs).extract (0 + i * t.fixedByteSize)
            (0 + (i + 1) * t.fixedByteSize) =
          SSZType.serialize t (xs[i]'h) := by
    intro i h
    simp [Nat.zero_add]
    exact extract_serializeFixedElems t t.fixedByteSize h_serialize_size xs i h
  have := deserializeFixedElems_eq_of_slice t h_decode_encode_t h_serialize_size
            xs (SSZType.serializeFixedElems t xs) 0 [] 0 h_extract
  simpa using this

end SizzLean.Proofs
