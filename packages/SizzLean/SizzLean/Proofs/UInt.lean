import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SimpAttrs
import Std.Tactic.BVDecide

/-!
# `SizzLean.Proofs.UInt`: `decode_encode` and size bound for the four `uintN` arms

Per-shape lemmas for `.uintN 8 / 16 / 32 / 64`. Each closes by
`unfold`ing the LE writer/reader (`uint16LE` / `readUInt16LE`,
etc., public defs in `Spec/{Serialize,Deserialize}.lean`),
reducing the per-byte indexing of the `(empty.push a₀)…push aₙ)[i]`
chain via `rfl`-typed `have`s, and discharging the residual
`UInt N` LE identity `b₀ ||| (b₁ <<< 8) ||| … = x` with
**`bv_decide`**.

## Tactics used in this file (annotated on first appearance)

* `unfold f`: replace every occurrence of `f` in the goal by its
  definition's right-hand side. Pure beta/delta reduction; no
  computation is performed. Useful when the definition's RHS is
  already in the form the next tactic needs.
* `rfl`: close a goal of the form `a = a` after Lean has reduced
  both sides definitionally. The fastest tactic; if `rfl` works,
  the equation holds by *definitional equality* (no propositional
  reasoning needed).
* `bv_decide`: bit-blasts a goal over fixed-width `BitVec` /
  `UInt` operations into a SAT problem and runs a CaDiCaL solver.
  Closes goals like `b₀ ||| (b₁ <<< 8) = x` by trying every
  bit-assignment. Each call introduces a `Lean.ofReduceBool` axiom
  (the standard "trust the verified SAT certificate" footprint);
  `#print axioms <theorem>` shows exactly which.
* `intro x`: move the `∀ x, …` quantifier into the hypothesis
  context so the rest of the proof reasons about a fixed `x`.

The `.uintN 8` arm closes by `rfl` after one `unfold`; the
multi-byte arms each add the `bv_decide` axiom.

`Proofs/Roundtrip.lean` re-imports and dispatches to the lemmas
here through its `cases h_sup with | uintNₖ => exact
decode_encode_uintNₖ x` arms, keeping the dispatch theorem
focused on case-splitting rather than per-arm reasoning.
-/

set_option autoImplicit false
-- `bv_decide` on the 8-byte UInt64 LE identity is the heaviest
-- single proof in this file; bump heartbeats to match.
set_option maxHeartbeats 400000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- Roundtrip for `.uintN 8`.

`serialize (.uintN 8) x = ByteArray.empty.push x` (single byte);
`deserialize (.uintN 8) b = readUInt8At b 0` (reads byte 0, returns
`.ok (·, 1)`). The composition reduces to `.ok (x, 1) = .ok (x, 1)`
after one `unfold`, closed by `rfl`. -/
theorem decode_encode_uintN8 : ∀ (x : UInt8),
    SSZType.deserialize (.uintN 8) (SSZType.serialize (.uintN 8) x) =
      .ok (x, (SSZType.serialize (.uintN 8) x).size) := by
  intro x
  unfold SSZType.deserialize SSZType.serialize
  rfl

/-- Roundtrip for `.uintN 16`.

After unfolding the 2-byte LE writer / reader and reducing the
buffer-size dependent-if, the residual is the LE per-bit identity
on `UInt16`, closed by `bv_decide`. The two `have hᵢ := rfl`
steps reduce `(empty.push a₀).push a₁)[i]` to `aᵢ` for the
`bv_decide`-visible form. -/
theorem decode_encode_uintN16 : ∀ (x : UInt16),
    SSZType.deserialize (.uintN 16) (SSZType.serialize (.uintN 16) x) =
      .ok (x, (SSZType.serialize (.uintN 16) x).size) := by
  intro x
  unfold SSZType.deserialize SSZType.serialize uint16LE readUInt16LE
  simp only [ByteArray.size_push, ByteArray.size_empty]
  simp
  have h0 : ((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8)[0]'(by
              simp [ByteArray.size_push, ByteArray.size_empty]) = x.toUInt8 := rfl
  have h1 : ((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8)[1]'(by
              simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 8).toUInt8 := rfl
  rw [h0, h1]
  bv_decide

/-- Roundtrip for `.uintN 32`. Same recipe as `uintN16` with four
byte-index reductions. -/
theorem decode_encode_uintN32 : ∀ (x : UInt32),
    SSZType.deserialize (.uintN 32) (SSZType.serialize (.uintN 32) x) =
      .ok (x, (SSZType.serialize (.uintN 32) x).size) := by
  intro x
  unfold SSZType.deserialize SSZType.serialize uint32LE readUInt32LE
  simp only [ByteArray.size_push, ByteArray.size_empty]
  simp
  have h0 : ((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8)[0]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = x.toUInt8 := rfl
  have h1 : ((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8)[1]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 8).toUInt8 := rfl
  have h2 : ((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8)[2]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 16).toUInt8 := rfl
  have h3 : ((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8)[3]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 24).toUInt8 := rfl
  rw [h0, h1, h2, h3]
  bv_decide

/-- Roundtrip for `.uintN 64`. Same recipe with eight byte-index
reductions; `bv_decide` SAT problem is the largest of the four
integer arms but still well under a second. -/
theorem decode_encode_uintN64 : ∀ (x : UInt64),
    SSZType.deserialize (.uintN 64) (SSZType.serialize (.uintN 64) x) =
      .ok (x, (SSZType.serialize (.uintN 64) x).size) := by
  intro x
  unfold SSZType.deserialize SSZType.serialize uint64LE readUInt64LE
  simp only [ByteArray.size_push, ByteArray.size_empty]
  simp
  have h0 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[0]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = x.toUInt8 := rfl
  have h1 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[1]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 8).toUInt8 := rfl
  have h2 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[2]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 16).toUInt8 := rfl
  have h3 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[3]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 24).toUInt8 := rfl
  have h4 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[4]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 32).toUInt8 := rfl
  have h5 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[5]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 40).toUInt8 := rfl
  have h6 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[6]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 48).toUInt8 := rfl
  have h7 : ((((((((ByteArray.empty.push x.toUInt8).push (x >>> 8).toUInt8).push
              (x >>> 16).toUInt8).push (x >>> 24).toUInt8).push (x >>> 32).toUInt8).push
              (x >>> 40).toUInt8).push (x >>> 48).toUInt8).push (x >>> 56).toUInt8)[7]'(by
                simp [ByteArray.size_push, ByteArray.size_empty]) = (x >>> 56).toUInt8 := rfl
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  bv_decide

/-! ### Size bounds: each `(serialize …).size = (N+7)/8 = maxByteLength` -/

/-- Per-`UInt8` size bound. Both sides reduce to `1`. -/
theorem encode_size_le_max_uintN8 : ∀ (x : UInt8),
    (SSZType.serialize (.uintN 8) x).size ≤ SSZType.maxByteLength (.uintN 8) := by
  intro x
  simp [SSZType.serialize, SSZType.maxByteLength, ByteArray.size_push,
        ByteArray.size_empty]

/-- Per-`UInt16` size bound. Both sides reduce to `2`. -/
theorem encode_size_le_max_uintN16 : ∀ (x : UInt16),
    (SSZType.serialize (.uintN 16) x).size ≤ SSZType.maxByteLength (.uintN 16) := by
  intro x
  simp [SSZType.serialize, SSZType.maxByteLength, uint16LE,
        ByteArray.size_push, ByteArray.size_empty]

/-- Per-`UInt32` size bound. Both sides reduce to `4`. -/
theorem encode_size_le_max_uintN32 : ∀ (x : UInt32),
    (SSZType.serialize (.uintN 32) x).size ≤ SSZType.maxByteLength (.uintN 32) := by
  intro x
  simp [SSZType.serialize, SSZType.maxByteLength, uint32LE,
        ByteArray.size_push, ByteArray.size_empty]

/-- Per-`UInt64` size bound. Both sides reduce to `8`. -/
theorem encode_size_le_max_uintN64 : ∀ (x : UInt64),
    (SSZType.serialize (.uintN 64) x).size ≤ SSZType.maxByteLength (.uintN 64) := by
  intro x
  simp [SSZType.serialize, SSZType.maxByteLength, uint64LE,
        ByteArray.size_push, ByteArray.size_empty]

end SizzLean.Proofs
