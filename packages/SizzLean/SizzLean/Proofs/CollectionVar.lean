import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.MaxByteLength
import SizzLean.Spec.Constants
import SizzLean.Proofs.ContainerVar

/-!
# `SizzLean.Proofs.CollectionVar`: variable-element `.vector` / `.list`

Closes `decode_encode` and `encode_size_le_max` for `.vector t n` /
`.list t cap` when `t` is `BasicSupported` and variable-size, via
the offset-table codec (`serializeVarElemsAux` /
`deserializeVarElems`). The predicates (`vectorVar` / `listVar` on
`BasicSupported` / `Supported` / `SupportedBounded`) live in
`Spec/`; this file ships the codec-level lemmas and the
parameterised walkers the Roundtrip / SizeBound dispatchers call.

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
   `varOff = n * 4`, that first offset is where the first body
   starts, immediately after the `n`-entry table. The list decoder
   recovers `count` from `off₀ / 4` (so `count = xs.length` on
   encoder output). The vector decoder takes `count = n` from the
   schema. Its roundtrip uses the encoder's canonical first offset.
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
5. **Element-list walker** (`deserializeVarElems_collOffsetsOf`):
   `deserializeVarElems` recovers the encoded list, given the
   body-region extract invariant. Parameterised by the element
   roundtrip.
6. **Top-level arms** (`decode_encode_vectorVar` /
   `decode_encode_listVar`, `encode_size_le_max_vectorVar` /
   `encode_size_le_max_listVar`): the dispatcher-facing wrappers.
   Vectors reject `n = 0`; lists split on the empty-buffer
   identity, then recover `count` from `off₀ / 4`.

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

/-! ### Roundtrip-walker helpers -/

/-- **Running-offset lookahead**: the "next offset, or `bufEnd` if
none remain" that `deserializeVarElems` computes
(`rest.head?.getD bufEnd`) always lands on the running `varOff`
itself. If `xs` is non-empty, `collOffsetsOf`'s list starts with
`varOff` directly. If `xs` is empty, the list is empty and `.getD`
falls back to `bufEnd`, which the hypothesis pins to `varOff`
exactly (no body bytes remain). Homogeneous analogue of
`varOffsetsOf_head_getD`. -/
theorem collOffsetsOf_head_getD
    (t : SSZType) (xs : List t.interp) (varOff bufEnd : Nat)
    (h : bufEnd = varOff + (SSZType.serializeVarElemsAux t xs varOff).2.size) :
    (collOffsetsOf t xs varOff).head?.getD bufEnd = varOff := by
  cases xs with
  | nil =>
    unfold SSZType.serializeVarElemsAux at h
    simp only [ByteArray.size_empty, Nat.add_zero] at h
    unfold collOffsetsOf
    simpa using h
  | cons _ _ =>
    unfold collOffsetsOf
    rfl

/-- **Element-list walker**: `deserializeVarElems` recovers exactly
the element list the encoder wrote, given that `b`'s body-region
slice `[varOff, bufEnd)` matches `serializeVarElemsAux`'s `.2` and
the offset list is `collOffsetsOf`. Parameterised by the
element-type roundtrip so `Proofs/Roundtrip.lean` can supply
`fun y => decode_encode h_t y` without this file joining the
mutual block. Uses `extract_split` at each cons, same as the
variable-field branch of `decode_encode_containerVar_aux`. -/
theorem deserializeVarElems_collOffsetsOf
    (t : SSZType)
    (h_decode_encode_t : ∀ y : t.interp,
      SSZType.deserialize t (SSZType.serialize t y) =
        .ok (y, (SSZType.serialize t y).size)) :
    ∀ (xs : List t.interp) (varOff : Nat) (b : ByteArray) (bufEnd : Nat),
    varOff ≤ bufEnd → bufEnd ≤ b.size →
    b.extract varOff bufEnd = (SSZType.serializeVarElemsAux t xs varOff).2 →
    SSZType.deserializeVarElems t (collOffsetsOf t xs varOff) bufEnd b = .ok xs := by
  intro xs
  induction xs with
  | nil =>
    intro varOff b bufEnd _ _ _
    unfold collOffsetsOf SSZType.deserializeVarElems
    rfl
  | cons x xs ih =>
    intro varOff b bufEnd h_ve h_vb h_V
    have h_enc2 :
        (SSZType.serializeVarElemsAux t (x :: xs) varOff).2 =
          SSZType.serialize t x ++
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).2 := by
      simp only [SSZType.serializeVarElemsAux]
    rw [h_enc2] at h_V
    have hq : varOff + (SSZType.serialize t x).size ≤ bufEnd := by
      have hVsize : (b.extract varOff bufEnd).size =
          (SSZType.serialize t x).size +
            (SSZType.serializeVarElemsAux t xs
              (varOff + (SSZType.serialize t x).size)).2.size := by
        rw [h_V, ByteArray.size_append]
      rw [ByteArray.size_extract, Nat.min_eq_left h_vb] at hVsize
      omega
    have h_split :=
      extract_split (b := b) (p := varOff) (q := bufEnd)
        (u := SSZType.serialize t x)
        (v := (SSZType.serializeVarElemsAux t xs
          (varOff + (SSZType.serialize t x).size)).2)
        h_V (by omega) h_vb
    have h_body : b.extract varOff (varOff + (SSZType.serialize t x).size) =
        SSZType.serialize t x := h_split.1
    have h_V' :
        b.extract (varOff + (SSZType.serialize t x).size) bufEnd =
          (SSZType.serializeVarElemsAux t xs
            (varOff + (SSZType.serialize t x).size)).2 := h_split.2
    have h_bufEnd_eq :
        bufEnd = (varOff + (SSZType.serialize t x).size) +
          (SSZType.serializeVarElemsAux t xs
            (varOff + (SSZType.serialize t x).size)).2.size := by
      have h_sz := congrArg ByteArray.size h_V'
      rw [ByteArray.size_extract, Nat.min_eq_left h_vb] at h_sz
      omega
    have h_nextOff :
        (collOffsetsOf t xs (varOff + (SSZType.serialize t x).size)).head?.getD bufEnd =
          varOff + (SSZType.serialize t x).size :=
      collOffsetsOf_head_getD t xs (varOff + (SSZType.serialize t x).size) bufEnd
        h_bufEnd_eq
    have h_de := h_decode_encode_t x
    unfold collOffsetsOf
    unfold SSZType.deserializeVarElems
    rw [h_nextOff]
    have h_guard : ¬ (varOff > varOff + (SSZType.serialize t x).size ||
        varOff + (SSZType.serialize t x).size > bufEnd) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    simp only [h_guard]
    rw [h_body, h_de]
    rw [ih (varOff + (SSZType.serialize t x).size) b bufEnd (by omega) h_vb h_V']
    rfl

/-- Size bound for `.vector t n` with `t` variable-size. Unfolds
the encoder's `offs ++ bodies` and cites
`size_serializeVarElemsAux_le_maxByteLength_vector`. -/
theorem encode_size_le_max_vectorVar
    (t : SSZType) (n : Nat)
    (h_var : t.isFixedSize = false)
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (v : Vector t.interp n) :
    (SSZType.serialize (.vector t n) v).size ≤
      SSZType.maxByteLength (.vector t n) := by
  have h_len : v.toList.length = n := by rw [Vector.length_toList]
  have h_serialize_eq :
      SSZType.serialize (.vector t n) v =
        (SSZType.serializeVarElemsAux t v.toList
          (v.toList.length * BYTES_PER_LENGTH_OFFSET)).1 ++
        (SSZType.serializeVarElemsAux t v.toList
          (v.toList.length * BYTES_PER_LENGTH_OFFSET)).2 := by
    unfold SSZType.serialize
    simp only [h_var, if_false, Bool.false_eq_true]
  rw [h_serialize_eq, ByteArray.size_append]
  have h := size_serializeVarElemsAux_le_maxByteLength_vector t n v.toList
      (v.toList.length * BYTES_PER_LENGTH_OFFSET) h_var h_len h_max_t
  exact h

/-- Size bound for `.list t cap` with `t` variable-size. Empty
lists (size 0) are in-bounds; non-empty lists scale the aux bound
up to the cap via `size_serializeVarElemsAux_le_maxByteLength_list`. -/
theorem encode_size_le_max_listVar
    (t : SSZType) (cap : Nat)
    (h_var : t.isFixedSize = false)
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (xs : { ys : Array t.interp // ys.size ≤ cap }) :
    (SSZType.serialize (.list t cap) xs).size ≤
      SSZType.maxByteLength (.list t cap) := by
  have h_len : xs.val.toList.length ≤ cap := by
    simpa using xs.property
  have h_serialize_eq :
      SSZType.serialize (.list t cap) xs =
        (SSZType.serializeVarElemsAux t xs.val.toList
          (xs.val.toList.length * BYTES_PER_LENGTH_OFFSET)).1 ++
        (SSZType.serializeVarElemsAux t xs.val.toList
          (xs.val.toList.length * BYTES_PER_LENGTH_OFFSET)).2 := by
    unfold SSZType.serialize
    simp only [h_var, if_false, Bool.false_eq_true]
  rw [h_serialize_eq, ByteArray.size_append]
  exact size_serializeVarElemsAux_le_maxByteLength_list t cap xs.val.toList
    (xs.val.toList.length * BYTES_PER_LENGTH_OFFSET) h_var h_len h_max_t

/-- Roundtrip for `.vector t n` with `t` variable-size and `n > 0`.
Parameterised by the element-type roundtrip and the element-type
size bound (the latter feeds the uint32-overflow guard, same
dependence `decode_encode` already has on `encode_size_le_max`
for `containerVar`). -/
theorem decode_encode_vectorVar
    (t : SSZType) (n : Nat) (h_pos : 0 < n)
    (h_var : t.isFixedSize = false)
    (h_max_lt : SSZType.maxByteLength (.vector t n) < MAX_LENGTH)
    (h_decode_encode_t : ∀ y : t.interp,
      SSZType.deserialize t (SSZType.serialize t y) =
        .ok (y, (SSZType.serialize t y).size))
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (v : Vector t.interp n) :
    SSZType.deserialize (.vector t n) (SSZType.serialize (.vector t n) v) =
      .ok (v, (SSZType.serialize (.vector t n) v).size) := by
  have h_len : v.toList.length = n := by rw [Vector.length_toList]
  have hBPLO : BYTES_PER_LENGTH_OFFSET = 4 := rfl
  let varOff : Nat := n * BYTES_PER_LENGTH_OFFSET
  have h_varOff : v.toList.length * BYTES_PER_LENGTH_OFFSET = varOff := by
    rw [h_len]
  have h_serialize_eq :
      SSZType.serialize (.vector t n) v =
        (SSZType.serializeVarElemsAux t v.toList varOff).1 ++
          (SSZType.serializeVarElemsAux t v.toList varOff).2 := by
    unfold SSZType.serialize
    simp only [h_var, if_false, Bool.false_eq_true]
    rw [h_varOff]
  have h_offs_size :
      (SSZType.serializeVarElemsAux t v.toList varOff).1.size = varOff := by
    rw [size_serializeVarElemsAux_offs, h_len]
  have h_bsize :
      (SSZType.serialize (.vector t n) v).size =
        varOff + (SSZType.serializeVarElemsAux t v.toList varOff).2.size := by
    rw [h_serialize_eq, ByteArray.size_append, h_offs_size]
  have h_bound :=
    size_serializeVarElemsAux_le_maxByteLength_vector t n v.toList varOff
      h_var h_len h_max_t
  have hML : MAX_LENGTH = 2 ^ 32 := rfl
  have h_uint32_bound :
      varOff + (SSZType.serializeVarElemsAux t v.toList varOff).2.size < 2 ^ 32 := by
    have h_le :
        (SSZType.serializeVarElemsAux t v.toList varOff).1.size +
          (SSZType.serializeVarElemsAux t v.toList varOff).2.size ≤
          SSZType.maxByteLength (.vector t n) := h_bound
    rw [h_offs_size] at h_le
    omega
  have h_offs :
      extractCollOffsets (SSZType.serialize (.vector t n) v) n 0 =
        .ok (collOffsetsOf t v.toList varOff) := by
    have h_pre :=
      extractCollOffsets_serializeVarElemsAux t v.toList varOff ByteArray.empty
        h_uint32_bound (SSZType.serializeVarElemsAux t v.toList varOff).2
    simpa [ByteArray.empty_append, h_serialize_eq, h_len] using h_pre
  have h_V :
      (SSZType.serialize (.vector t n) v).extract varOff
          (SSZType.serialize (.vector t n) v).size =
        (SSZType.serializeVarElemsAux t v.toList varOff).2 := by
    rw [h_bsize, h_serialize_eq]
    exact ByteArray.extract_append_eq_right h_offs_size.symm (by rw [h_offs_size])
  have h_elems :=
    deserializeVarElems_collOffsetsOf t h_decode_encode_t v.toList varOff
      (SSZType.serialize (.vector t n) v)
      (SSZType.serialize (.vector t n) v).size
      (by omega) (by omega) h_V
  have hn : ¬ n = 0 := Nat.ne_of_gt h_pos
  have h_ge : ¬ (SSZType.serialize (.vector t n) v).size < n * BYTES_PER_LENGTH_OFFSET := by
    rw [h_bsize]; omega
  unfold SSZType.deserialize
  simp only [hn, if_false]
  simp only [h_var, if_false, Bool.false_eq_true]
  simp only [h_ge, if_false]
  rw [h_offs]
  dsimp only
  rw [h_elems]
  have h_sz_arr : v.toList.toArray.size = n := by
    rw [List.size_toArray, h_len]
  simp only [h_sz_arr, dite_true]
  cases v with
  | mk arr h =>
    simp [Array.toArray_toList]

/-- Roundtrip for `.list t cap` with `t` variable-size.
Empty lists take the decoder's `b.size = 0` branch; non-empty
lists recover `count` from `off₀ / 4` then reuse the same walker
as `decode_encode_vectorVar`. -/
theorem decode_encode_listVar
    (t : SSZType) (cap : Nat)
    (h_var : t.isFixedSize = false)
    (h_max_lt : SSZType.maxByteLength (.list t cap) < MAX_LENGTH)
    (h_decode_encode_t : ∀ y : t.interp,
      SSZType.deserialize t (SSZType.serialize t y) =
        .ok (y, (SSZType.serialize t y).size))
    (h_max_t : ∀ y : t.interp,
      (SSZType.serialize t y).size ≤ SSZType.maxByteLength t)
    (xs : { ys : Array t.interp // ys.size ≤ cap }) :
    SSZType.deserialize (.list t cap) (SSZType.serialize (.list t cap) xs) =
      .ok (xs, (SSZType.serialize (.list t cap) xs).size) := by
  have h_list_len : xs.val.toList.length = xs.val.size := by simp
  have h_len_le : xs.val.toList.length ≤ cap := by
    simpa using xs.property
  have h_serialize_eq :
      SSZType.serialize (.list t cap) xs =
        (SSZType.serializeVarElemsAux t xs.val.toList
          (xs.val.toList.length * BYTES_PER_LENGTH_OFFSET)).1 ++
        (SSZType.serializeVarElemsAux t xs.val.toList
          (xs.val.toList.length * BYTES_PER_LENGTH_OFFSET)).2 := by
    unfold SSZType.serialize
    simp only [h_var, if_false, Bool.false_eq_true]
  by_cases h_empty : xs.val.size = 0
  · -- Empty list: encoder writes the empty buffer; decoder's
    -- `b.size = 0` branch recovers `⟨#[], _⟩`.
    have h_nil : xs.val.toList = [] :=
      List.eq_nil_of_length_eq_zero (by rw [h_list_len, h_empty])
    have h_ser_empty : SSZType.serialize (.list t cap) xs = ByteArray.empty := by
      rw [h_serialize_eq, h_nil]
      unfold SSZType.serializeVarElemsAux
      rfl
    rw [h_ser_empty]
    unfold SSZType.deserialize
    simp only [h_var, if_false, Bool.false_eq_true]
    have h_sz0 : (ByteArray.empty).size = 0 := ByteArray.size_empty
    simp only [h_sz0, if_true]
    have h_arr : xs.val = #[] := Array.eq_empty_of_size_eq_zero h_empty
    have hx : xs = ⟨#[], by simp⟩ := Subtype.ext h_arr
    rw [hx]
  · -- Non-empty: first offset is n * 4, count = n, then the walker.
    have h_pos : 0 < xs.val.size := Nat.pos_of_ne_zero h_empty
    have h_cons : ∃ x ys, xs.val.toList = x :: ys := by
      cases hxs : xs.val.toList with
      | nil =>
        have : xs.val.toList.length = 0 := by rw [hxs]; rfl
        rw [h_list_len] at this
        exact absurd this (Nat.ne_of_gt h_pos)
      | cons x ys => exact ⟨x, ys, rfl⟩
    obtain ⟨x, ys, h_cons_eq⟩ := h_cons
    let varOff : Nat := xs.val.toList.length * BYTES_PER_LENGTH_OFFSET
    have h_offs_size :
        (SSZType.serializeVarElemsAux t xs.val.toList varOff).1.size = varOff :=
      size_serializeVarElemsAux_offs t xs.val.toList varOff
    have h_bsize :
        (SSZType.serialize (.list t cap) xs).size =
          varOff + (SSZType.serializeVarElemsAux t xs.val.toList varOff).2.size := by
      rw [h_serialize_eq, ByteArray.size_append, h_offs_size]
    have h_bound :=
      size_serializeVarElemsAux_le_maxByteLength_list t cap xs.val.toList varOff
        h_var h_len_le h_max_t
    have hML : MAX_LENGTH = 2 ^ 32 := rfl
    have h_uint32_bound :
        varOff + (SSZType.serializeVarElemsAux t xs.val.toList varOff).2.size < 2 ^ 32 := by
      have h_le :
          (SSZType.serializeVarElemsAux t xs.val.toList varOff).1.size +
            (SSZType.serializeVarElemsAux t xs.val.toList varOff).2.size ≤
            SSZType.maxByteLength (.list t cap) := h_bound
      rw [h_offs_size] at h_le
      omega
    have h_first :=
      readUInt32LE_serializeVarElemsAux_cons t x ys varOff
    have h_cons_enc :
        SSZType.serializeVarElemsAux t xs.val.toList varOff =
          SSZType.serializeVarElemsAux t (x :: ys) varOff := by
      rw [h_cons_eq]
    have h_read :
        readUInt32LE (SSZType.serialize (.list t cap) xs) 0 =
          some (Nat.toUInt32 varOff) := by
      rw [h_serialize_eq, h_cons_enc]
      exact h_first
    have h_toNat : (Nat.toUInt32 varOff).toNat = varOff :=
      toNat_toUInt32_of_lt varOff (by omega)
    have h_mod : varOff % BYTES_PER_LENGTH_OFFSET = 0 := by
      unfold varOff
      have hBPLO : BYTES_PER_LENGTH_OFFSET = 4 := rfl
      rw [hBPLO]
      exact Nat.mul_mod_left _ _
    have h_div : varOff / BYTES_PER_LENGTH_OFFSET = xs.val.toList.length := by
      unfold varOff
      have hBPLO : BYTES_PER_LENGTH_OFFSET = 4 := rfl
      have hpos : 0 < BYTES_PER_LENGTH_OFFSET := by rw [hBPLO]; decide
      exact Nat.mul_div_cancel _ hpos
    have h_count_le : ¬ xs.val.toList.length > cap := Nat.not_lt.mpr h_len_le
    have h_offs :
        extractCollOffsets (SSZType.serialize (.list t cap) xs)
            (varOff / BYTES_PER_LENGTH_OFFSET) 0 =
          .ok (collOffsetsOf t xs.val.toList varOff) := by
      rw [h_div]
      have h_pre :=
        extractCollOffsets_serializeVarElemsAux t xs.val.toList varOff ByteArray.empty
          h_uint32_bound (SSZType.serializeVarElemsAux t xs.val.toList varOff).2
      simpa [ByteArray.empty_append, h_serialize_eq] using h_pre
    have h_V :
        (SSZType.serialize (.list t cap) xs).extract varOff
            (SSZType.serialize (.list t cap) xs).size =
          (SSZType.serializeVarElemsAux t xs.val.toList varOff).2 := by
      rw [h_bsize, h_serialize_eq]
      exact ByteArray.extract_append_eq_right h_offs_size.symm (by rw [h_offs_size])
    have h_elems :=
      deserializeVarElems_collOffsetsOf t h_decode_encode_t xs.val.toList varOff
        (SSZType.serialize (.list t cap) xs)
        (SSZType.serialize (.list t cap) xs).size
        (by omega) (by omega) h_V
    have h_sz_pos : ¬ (SSZType.serialize (.list t cap) xs).size = 0 := by
      rw [h_bsize]
      have hpos : 0 < varOff := by
        change 0 < xs.val.toList.length * BYTES_PER_LENGTH_OFFSET
        have hl : 0 < xs.val.toList.length := by rw [h_list_len]; exact h_pos
        have hb : 0 < BYTES_PER_LENGTH_OFFSET := by decide
        exact Nat.mul_pos hl hb
      omega
    unfold SSZType.deserialize
    simp only [h_var, if_false, Bool.false_eq_true]
    simp only [h_sz_pos, if_false]
    rw [h_read]
    dsimp only
    have h_mod' : ¬ (Nat.toUInt32 varOff).toNat % BYTES_PER_LENGTH_OFFSET ≠ 0 := by
      rw [h_toNat, h_mod]; intro h; exact h rfl
    simp only [h_mod', if_false]
    rw [h_toNat, h_div]
    simp only [h_count_le, if_false]
    rw [h_div] at h_offs
    rw [h_offs]
    dsimp only
    rw [h_elems]
    have h_arr_sz : xs.val.toList.toArray.size ≤ cap := by
      rw [List.size_toArray, h_list_len]; exact xs.property
    simp only [h_arr_sz, dite_true]

end SizzLean.Proofs
