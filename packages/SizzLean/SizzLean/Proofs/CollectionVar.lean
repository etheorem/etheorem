import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.ContainerVar

/-!
# `SizzLean.Proofs.CollectionVar`: groundwork for variable-element `.vector` / `.list`

Variable-element collections (`.vector t n` / `.list t cap` with
`t.isFixedSize = false`) are the remaining composite gap in
`SSZType.Supported` once mixed-field containers land: the codec
([`Spec/Serialize.lean`](../Spec/Serialize.lean)'s
`serializeVarElemsAux`, [`Spec/Deserialize.lean`](../Spec/Deserialize.lean)'s
non-`isFixedSize` `.vector` / `.list` branches) fully implements the
offset-table wire format, but no `BasicSupported` constructor claims
it yet, and no theorem closes it. This module lays the groundwork;
the predicates (`vectorVar` / `listVar` on `BasicSupported` /
`Supported` / `SupportedBounded`) and the roundtrip walkers land in
a follow-up, once this file's lemmas are available to build on and
once `containerVar` is on `main` (the `BasicSupported` matchers grow
two constructors; that arm must already be exhaustive).

Homogeneous collections have one element type `t`, so the proof
inducts on the element list as `Proofs/FixedElems.lean` does. The
existing uint32 codec bridge from `ContainerVar`
(`readUInt32LE_uint32LE_append`, `readUInt32LE_append_shift`,
`toNat_toUInt32_of_lt`) supplies the byte-level inverse.

## Wire format (what the lemmas below characterize)

```
offset table                         body region
┌────────┬────────┬────────┐         ┌────────┬────────┐
│ off₀   │ off₁   │ off₂   │   …     │ body₀  │ body₁  │ …
│(uint32)│(uint32)│(uint32)│         │        │        │
└────────┴────────┴────────┘         └────────┴────────┘
```

`serializeVarElemsAux` builds this by walking the element list once,
threading a running `varOff` (seeded at `xs.length * BYTES_PER_LENGTH_OFFSET`,
the total width of the offset table): each element appends a
`uint32LE varOff` placeholder to the `.1` accumulator and its own
body to the `.2` accumulator, then advances `varOff` by the body's
size. The decoder's `extractCollOffsets` reads `count` placeholders
back out, before `deserializeVarElems` uses them to slice each
body. Vectors take `count = n` and reject `n = 0`; lists recover
`count` from `off₀ / 4`, with the empty buffer the empty list.

## Lemma path

The groundwork, in the order it composes (proven facts, plus the
plumbing `def` of item 1 that threads the running offsets through
them):

1. **Offset-list plumbing** (`collOffsetsOf`): the list the
   encoder's placeholders *should* decode back to, mirroring
   `serializeVarElemsAux`'s own walk (one entry per element, in
   order). Homogeneous analogue of `varOffsetsOf`.
2. **Encoder accounting** (`size_serializeVarElemsAux_offs`):
   `(serializeVarElemsAux t xs varOff).1.size = xs.length * 4`.
   Independent of `varOff` and of the bodies. At the encoder's seed
   `varOff = n * 4`, the first encoded offset is `n * 4`. The vector
   decoder takes `count = n` from the schema. The later roundtrip
   proof uses the encoder's canonical offset.
3. **Size walker** (`size_serializeVarElemsAux_le_max`):
   `(serializeVarElemsAux t xs varOff).1.size + .2.size ≤
   xs.length * (BYTES_PER_LENGTH_OFFSET + maxByteLength t)`.
   Specializes to `maxByteLength (.vector t n)` / `(.list t cap)`
   once `t.isFixedSize = false` (and `xs.length = n` /
   `xs.length ≤ cap`). Needed for the `encode_size_le_max` arms,
   and for the uint32-overflow guard every offset placeholder
   depends on.
4. **Offset-extraction inverse**
   (`extractCollOffsets_serializeVarElemsAux`): reading
   `extractCollOffsets` back off the encoder's own output recovers
   exactly the running offsets `serializeVarElemsAux` wrote
   (`collOffsetsOf`). Same `pre` / `suf` invariant as
   `extractFieldOffsets_serializeFieldsAux`: the extractor never
   reads past the offset table, so the buffer's tail can be
   anything.

## Trust

The lemmas use at most the standard kernel axioms. The uint32 bridge
from `ContainerVar` carries one `bv_decide` certificate, the same
trust class as the narrow `uintN` arms in `Proofs/UInt.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SizzLean.Proofs

open SizzLean.Spec
-- `extractCollOffsets` is `protected` in `Spec/Deserialize.lean`
-- (proof-internal, kept off the general `SizzLean.Spec` surface, same
-- convention as `extractFieldOffsets` / `natToLEBytes` / `readNatLE`),
-- so the wildcard `open` above does not bring it into scope; request
-- it explicitly.
open SizzLean.Spec (extractCollOffsets)

/-! ### Offset-list plumbing -/

/-- Expected running element offsets: the list the encoder's
placeholders *should* decode back to, mirroring
`serializeVarElemsAux`'s own walk exactly (one entry per element,
in order). Homogeneous analogue of `varOffsetsOf`. -/
def collOffsetsOf (t : SSZType) : List t.interp → Nat → List Nat
  | [],      _      => []
  | x :: xs, varOff =>
      varOff :: collOffsetsOf t xs (varOff + (SSZType.serialize t x).size)

/-- `collOffsetsOf` produces one offset per element. -/
theorem collOffsetsOf_length
    (t : SSZType) (xs : List t.interp) (varOff : Nat) :
    (collOffsetsOf t xs varOff).length = xs.length := by
  induction xs generalizing varOff with
  | nil => rfl
  | cons _ xs ih =>
    unfold collOffsetsOf
    simp [ih]

/-- The first placeholder a non-empty collection writes is the
seeded `varOff`. At the encoder's call site that seed is
`xs.length * BYTES_PER_LENGTH_OFFSET`. The vector roundtrip uses
this canonical encoder value. The list decoder uses it to recover
`count = firstOff / 4`. -/
theorem collOffsetsOf_head_cons
    (t : SSZType) (x : t.interp) (xs : List t.interp) (varOff : Nat) :
    (collOffsetsOf t (x :: xs) varOff).head? = some varOff := rfl

/-! ### Encoder accounting and the size walker -/

/-- **Encoder accounting**: the offset-table output of
`serializeVarElemsAux` has size exactly `xs.length * 4`, one
`uint32` placeholder per element (`size_uint32LE`). Independent of
`varOff` and of the bodies. Structural induction on `xs`. -/
theorem size_serializeVarElemsAux_offs
    (t : SSZType) (xs : List t.interp) (varOff : Nat) :
    (SSZType.serializeVarElemsAux t xs varOff).1.size =
      xs.length * BYTES_PER_LENGTH_OFFSET := by
  induction xs generalizing varOff with
  | nil =>
    unfold SSZType.serializeVarElemsAux
    simp [ByteArray.size_empty]
  | cons x xs ih =>
    have h_enc :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).1 =
          uint32LE (Nat.toUInt32 varOff) ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).1 := by
      simp only [SSZType.serializeVarElemsAux]
    rw [h_enc, ByteArray.size_append, size_uint32LE, ih, List.length_cons]
    simp only [BYTES_PER_LENGTH_OFFSET, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Reading the first offset placeholder back off the front of a
non-empty collection's own encoded output recovers the seeded
`varOff`. The list decoder's `readUInt32LE b 0` is this lemma at
`pre = .empty`; combined with `toNat_toUInt32_of_lt` it yields
`count = firstOff / 4`. -/
theorem readUInt32LE_serializeVarElemsAux_cons
    (t : SSZType) (x : t.interp) (xs : List t.interp) (varOff : Nat) :
    readUInt32LE
      ((SSZType.serializeVarElemsAux t (x :: xs) varOff).1 ++
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).2) 0
      = some (Nat.toUInt32 varOff) := by
  have h_enc :
      (SSZType.serializeVarElemsAux t (x :: xs) varOff).1 =
        uint32LE (Nat.toUInt32 varOff) ++
          (SSZType.serializeVarElemsAux t xs
            (varOff + (SSZType.serialize t x).size)).1 := by
    simp only [SSZType.serializeVarElemsAux]
  rw [h_enc, ByteArray.append_assoc]
  exact readUInt32LE_uint32LE_append _ _

/-- **Size walker**: the total serialized output of
`serializeVarElemsAux` (offset table plus bodies combined) fits
within `xs.length * (BYTES_PER_LENGTH_OFFSET + maxByteLength t)`.
Every element contributes `≤ maxByteLength t` to the body side and
exactly 4 bytes to the offset table. Feeds both the
`encode_size_le_max` `vectorVar` / `listVar` arms and the
uint32-overflow guard the offset-extraction inverse below depends
on. The per-element bound is taken on all of `t.interp` (the shape
`encode_size_le_max` will supply), not merely the elements of `xs`. -/
theorem size_serializeVarElemsAux_le_max
    (t : SSZType) (xs : List t.interp) (varOff : Nat)
    (h_max : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t) :
    (SSZType.serializeVarElemsAux t xs varOff).1.size +
      (SSZType.serializeVarElemsAux t xs varOff).2.size ≤
      xs.length * (BYTES_PER_LENGTH_OFFSET +
        SSZType.maxByteLength t) := by
  induction xs generalizing varOff with
  | nil =>
    unfold SSZType.serializeVarElemsAux
    simp [ByteArray.size_empty]
  | cons x xs ih =>
    have h_enc :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).1 =
          uint32LE (Nat.toUInt32 varOff) ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).1 := by
      simp only [SSZType.serializeVarElemsAux]
    have h_enc2 :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).2 =
          SSZType.serialize t x ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).2 := by
      simp only [SSZType.serializeVarElemsAux]
    rw [h_enc, h_enc2, ByteArray.size_append, ByteArray.size_append,
        size_uint32LE]
    have h_tail := ih (varOff + (SSZType.serialize t x).size)
    have h_head := h_max x
    simp only [BYTES_PER_LENGTH_OFFSET] at h_tail ⊢
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Size walker specialized to `.vector t n`: once `t` is
variable-size and the element list has length `n`, the aux bound
is definitionally `maxByteLength (.vector t n)`. -/
theorem size_serializeVarElemsAux_le_maxByteLength_vector
    (t : SSZType) (n : Nat) (xs : List t.interp) (varOff : Nat)
    (h_var : t.isFixedSize = false)
    (h_len : xs.length = n)
    (h_max : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t) :
    (SSZType.serializeVarElemsAux t xs varOff).1.size +
      (SSZType.serializeVarElemsAux t xs varOff).2.size ≤
      SSZType.maxByteLength (.vector t n) := by
  have h := size_serializeVarElemsAux_le_max t xs varOff h_max
  simp only [SSZType.maxByteLength, h_var, if_false, Bool.false_eq_true]
  rwa [h_len] at h

/-- Size walker specialized to `.list t cap`: once `t` is
variable-size and the element list is within cap, the aux bound
scales up to `maxByteLength (.list t cap)` by
`Nat.mul_le_mul_right`. Empty lists (size 0) are in-bounds. -/
theorem size_serializeVarElemsAux_le_maxByteLength_list
    (t : SSZType) (cap : Nat) (xs : List t.interp) (varOff : Nat)
    (h_var : t.isFixedSize = false)
    (h_len : xs.length ≤ cap)
    (h_max : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t) :
    (SSZType.serializeVarElemsAux t xs varOff).1.size +
      (SSZType.serializeVarElemsAux t xs varOff).2.size ≤
      SSZType.maxByteLength (.list t cap) := by
  have h := size_serializeVarElemsAux_le_max t xs varOff h_max
  simp only [SSZType.maxByteLength, h_var, if_false, Bool.false_eq_true]
  exact Nat.le_trans h (Nat.mul_le_mul_right _ h_len)

/-! ### Offset-extraction inverse -/

/-- **Offset-extraction inverse**: reading `extractCollOffsets`
back off the encoder's own offset-table output recovers exactly
the running offsets `serializeVarElemsAux` wrote (`collOffsetsOf`).

Generalized over an arbitrary already-consumed prefix `pre` (so
induction can peel one placeholder off the front via the
append-shift bridges in `ContainerVar`) and an arbitrary suffix
`suf` following the offset table. The `suf` generality is what
keeps this proof tractable: `extractCollOffsets` never reads past
the offset table (every `uint32` placeholder it decodes lies
entirely within `.1`, by `size_serializeVarElemsAux_offs`), so
the buffer's tail can be *anything*, in particular `.2 ++ (whatever
came after the whole collection)`, without the invariant ever
having to track where the body region physically sits.

The `h_bound` hypothesis is the uint32-overflow guard: every offset
the encoder writes is `varOff ≤ o ≤ varOff + (total body bytes
written so far)`, so bounding that sum by `2 ^ 32` keeps every
offset's `UInt32` round-trip exact (`toNat_toUInt32_of_lt`).
Specializes to `pre = .empty` for the top-level statement the
(later) roundtrip walker needs. -/
theorem extractCollOffsets_serializeVarElemsAux
    (t : SSZType) :
    ∀ (xs : List t.interp) (varOff : Nat) (pre : ByteArray),
    varOff + (SSZType.serializeVarElemsAux t xs varOff).2.size < 2 ^ 32 →
    ∀ (suf : ByteArray),
    extractCollOffsets
      (pre ++ ((SSZType.serializeVarElemsAux t xs varOff).1 ++ suf))
      xs.length pre.size
      = .ok (collOffsetsOf t xs varOff) := by
  intro xs
  induction xs with
  | nil =>
    intro varOff pre _ suf
    unfold SSZType.serializeVarElemsAux collOffsetsOf extractCollOffsets
    rfl
  | cons x xs ih =>
    intro varOff pre h_bound suf
    have h_enc :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).1 =
          uint32LE (Nat.toUInt32 varOff) ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).1 := by
      simp only [SSZType.serializeVarElemsAux]
    have h_enc2 :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).2 =
          SSZType.serialize t x ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).2 := by
      simp only [SSZType.serializeVarElemsAux]
    rw [h_enc2] at h_bound
    have h_bound_tail :
        (varOff + (SSZType.serialize t x).size) +
          (SSZType.serializeVarElemsAux t xs
            (varOff + (SSZType.serialize t x).size)).2.size < 2 ^ 32 := by
      rw [ByteArray.size_append] at h_bound; omega
    have h_ih :=
      ih (varOff + (SSZType.serialize t x).size)
        (pre ++ uint32LE (Nat.toUInt32 varOff)) h_bound_tail suf
    have h_presize :
        (pre ++ uint32LE (Nat.toUInt32 varOff)).size = pre.size + 4 := by
      rw [ByteArray.size_append, size_uint32LE]
    rw [h_enc]
    have h_reassoc :
        pre ++
            (uint32LE (Nat.toUInt32 varOff) ++
              (SSZType.serializeVarElemsAux t xs
                (varOff + (SSZType.serialize t x).size)).1 ++ suf)
          = (pre ++ uint32LE (Nat.toUInt32 varOff)) ++
              ((SSZType.serializeVarElemsAux t xs
                (varOff + (SSZType.serialize t x).size)).1 ++ suf) := by
      simp only [ByteArray.append_assoc]
    rw [h_reassoc]
    simp only [List.length_cons]
    unfold extractCollOffsets
    have h_read :
        readUInt32LE
            ((pre ++ uint32LE (Nat.toUInt32 varOff)) ++
              ((SSZType.serializeVarElemsAux t xs
                (varOff + (SSZType.serialize t x).size)).1 ++ suf))
            pre.size
          = some (Nat.toUInt32 varOff) := by
      rw [ByteArray.append_assoc]
      have hshift := readUInt32LE_append_shift pre
        (uint32LE (Nat.toUInt32 varOff) ++
          ((SSZType.serializeVarElemsAux t xs
            (varOff + (SSZType.serialize t x).size)).1 ++ suf))
        0 (by rw [ByteArray.size_append, size_uint32LE]; omega)
      simp only [Nat.add_zero] at hshift
      rw [hshift, readUInt32LE_uint32LE_append]
    rw [h_read]
    dsimp only
    rw [show BYTES_PER_LENGTH_OFFSET = 4 from rfl,
        show pre.size + 4 = (pre ++ uint32LE (Nat.toUInt32 varOff)).size
          from h_presize.symm, h_ih]
    dsimp only
    have h_toNat : (Nat.toUInt32 varOff).toNat = varOff :=
      toNat_toUInt32_of_lt varOff (by omega)
    rw [h_toNat]
    rfl

end SizzLean.Proofs
