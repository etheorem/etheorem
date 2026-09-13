import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Proofs.Merkle.Chunk`: chunk-count bookkeeping

The bookkeeping Dafny proved for its merkleizer, and the side
conditions every `naiveRoot` application above needs: `chunkify`
produces `bytesToChunkCount b.size` chunks of 32 bytes each;
`padToChunk` and `natToChunk` emit exactly one chunk; and
`chunkDepth n` is the least `d` with `n ≤ 2 ^ d` (`chunkDepth 0 =
0`), so a chunk list is never longer than its own tree depth.

The proofs generalize the `let rec` fuel (`chunkDepth.go`,
`chunkify.go`, `padToChunk.go`, `natToChunk.go`) and carry the
loop invariant (`cur = 2 ^ acc` for the depth loop, one push per
step for the byte loops).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec

/-! ### `padToChunk` and `natToChunk`: one chunk each -/

/-- Each padding step pushes one zero byte. -/
theorem size_padToChunk_go : ∀ (k : Nat) (acc : ByteArray),
    (Spec.padToChunk.go k acc).size = acc.size + k := by
  intro k
  induction k with
  | zero => intro acc; simp [Spec.padToChunk.go]
  | succ k ih =>
      intro acc
      show (Spec.padToChunk.go (k + 1) acc).size = _
      rw [Spec.padToChunk.go, ih, ByteArray.size_push]
      omega

/-- A buffer of at most one chunk pads to exactly one chunk. -/
theorem size_padToChunk (b : ByteArray) (h : b.size ≤ BYTES_PER_CHUNK) :
    (Spec.padToChunk b).size = BYTES_PER_CHUNK := by
  simp only [padToChunk]
  by_cases hge : b.size ≥ BYTES_PER_CHUNK
  · rw [if_pos hge]
    have hb : b.size = BYTES_PER_CHUNK := by omega
    rw [hb]
  · rw [if_neg hge]
    have hlt : b.size < BYTES_PER_CHUNK := by omega
    rw [size_padToChunk_go]
    omega

/-- Each digit step pushes one byte. -/
theorem size_natToChunk_go : ∀ (k m : Nat) (acc : ByteArray),
    (Spec.natToChunk.go k m acc).size = acc.size + k := by
  intro k
  induction k with
  | zero => intro m acc; simp [Spec.natToChunk.go]
  | succ k ih =>
      intro m acc
      show (Spec.natToChunk.go (k + 1) m acc).size = _
      rw [Spec.natToChunk.go, ih, ByteArray.size_push]
      omega

/-- The length chunk is exactly one chunk. -/
theorem size_natToChunk (n : Nat) : (Spec.natToChunk n).size = BYTES_PER_CHUNK := by
  show (Spec.natToChunk.go BYTES_PER_CHUNK n ByteArray.empty).size = _
  rw [size_natToChunk_go]
  simp

/-! ### `chunkify`: the chunk count and the chunk size -/

/-- Each chunkify step prepends one chunk. -/
theorem length_chunkify_go (b : ByteArray) : ∀ (k : Nat) (acc : List ByteArray),
    (Spec.chunkify.go b k acc).length = acc.length + k := by
  intro k
  induction k with
  | zero => intro acc; simp [Spec.chunkify.go]
  | succ k ih =>
      intro acc
      show (Spec.chunkify.go b (k + 1) acc).length = _
      rw [Spec.chunkify.go, ih, List.length_cons]
      omega

/-- `chunkify` produces exactly `bytesToChunkCount b.size` chunks. -/
theorem length_chunkify (b : ByteArray) :
    (Spec.chunkify b).length = bytesToChunkCount b.size := by
  simp only [chunkify]
  have hcount : bytesToChunkCount b.size
      = (b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK := rfl
  by_cases hz : (b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK = 0
  · rw [if_pos hz, hcount, hz]; rfl
  · rw [if_neg hz, hcount, length_chunkify_go]
    simp

/-- Every buffer pushed by `chunkify.go` is a full chunk. -/
theorem size_mem_chunkify_go (b : ByteArray) : ∀ (k : Nat) (acc : List ByteArray),
    (∀ c ∈ acc, c.size = BYTES_PER_CHUNK) →
    ∀ c ∈ Spec.chunkify.go b k acc, c.size = BYTES_PER_CHUNK := by
  intro k
  induction k with
  | zero =>
      intro acc hin c hc
      simp only [Spec.chunkify.go] at hc
      exact hin c hc
  | succ k ih =>
      intro acc hin c hc
      rw [Spec.chunkify.go] at hc
      refine ih (padToChunk (b.extract (k * BYTES_PER_CHUNK)
        (k * BYTES_PER_CHUNK + BYTES_PER_CHUNK)) :: acc) ?_ c hc
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hmem
      · refine size_padToChunk _ ?_
        rw [ByteArray.size_extract]
        have hsub : BYTES_PER_CHUNK - k * BYTES_PER_CHUNK ≤ BYTES_PER_CHUNK :=
          Nat.sub_le _ _
        omega
      · exact hin c' hmem

/-- Every `chunkify` chunk is a full 32-byte chunk. -/
theorem size_mem_chunkify (b : ByteArray) :
    ∀ c ∈ Spec.chunkify b, c.size = BYTES_PER_CHUNK := by
  intro c hc
  simp only [chunkify] at hc
  by_cases hz : (b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK = 0
  · rw [if_pos hz] at hc
    simp at hc
  · rw [if_neg hz] at hc
    exact size_mem_chunkify_go b _ [] (by simp) c hc

/-! ### `chunkDepth`: the least power-of-two depth -/

/-- The depth loop's invariant: `cur = 2 ^ acc`, and the loop
terminates with `n ≤ 2 ^ acc` given enough fuel (`n ≤ 2 ^ (acc +
f)`). -/
theorem chunkDepth_go_bound (n : Nat) : ∀ (f acc cur : Nat), cur = 2 ^ acc →
    n ≤ 2 ^ (acc + f) → n ≤ 2 ^ chunkDepth.go n f acc cur := by
  intro f
  induction f with
  | zero =>
      intro acc cur _ hbound
      show n ≤ 2 ^ chunkDepth.go n 0 acc cur
      rw [chunkDepth.go]
      rwa [Nat.add_zero] at hbound
  | succ f ih =>
      intro acc cur hcur hbound
      show n ≤ 2 ^ chunkDepth.go n (f + 1) acc cur
      rw [chunkDepth.go]
      by_cases hn : n ≤ cur
      · rw [if_pos hn]
        rwa [hcur] at hn
      · rw [if_neg hn]
        refine ih (acc + 1) (cur * 2) ?_ ?_
        · rw [hcur, Nat.pow_succ, Nat.mul_comm]
        · have hexp : (acc + 1) + f = acc + (f + 1) := by omega
          rw [hexp]
          exact hbound

/-- `n` never exceeds its own power-of-two tree. -/
theorem nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      rw [Nat.pow_succ, Nat.mul_two]
      omega

/-- `chunkDepth n` bounds the value: `n ≤ 2 ^ chunkDepth n`. -/
theorem le_two_pow_chunkDepth (n : Nat) : n ≤ 2 ^ chunkDepth n := by
  have h1 : (1 : Nat) = 2 ^ 0 := (Nat.pow_zero 2).symm
  have hn : n ≤ 2 ^ (0 + n) := by
    rw [Nat.zero_add]
    exact nat_le_two_pow n
  exact chunkDepth_go_bound n n 0 1 h1 hn

/-- The depth loop is the *least* such bound: `n ≤ 2 ^ d` forces
`chunkDepth n ≤ d`. -/
theorem chunkDepth_go_le (n d : Nat) : ∀ (f acc cur : Nat), cur = 2 ^ acc →
    2 ^ acc ≤ 2 ^ d → acc ≤ d → n ≤ 2 ^ d → chunkDepth.go n f acc cur ≤ d := by
  intro f
  induction f with
  | zero =>
      intro acc cur _ _ hacc _
      show chunkDepth.go n 0 acc cur ≤ d
      rw [chunkDepth.go]
      exact hacc
  | succ f ih =>
      intro acc cur hcur hpow2 hacc hbound
      show chunkDepth.go n (f + 1) acc cur ≤ d
      rw [chunkDepth.go]
      by_cases hn : n ≤ cur
      · rw [if_pos hn]
        exact hacc
      · rw [if_neg hn]
        have hcurLt : cur < n := Nat.not_le.mp hn
        have hpowLt : 2 ^ acc < 2 ^ d := by
          rw [hcur] at hcurLt
          exact Nat.lt_of_lt_of_le hcurLt hbound
        have hacc' : acc + 1 ≤ d :=
          Nat.succ_le_of_lt ((Nat.pow_lt_pow_iff_right
            (show (1 : Nat) < 2 by decide)).mp hpowLt)
        refine ih (acc + 1) (cur * 2) ?_ ?_ hacc' hbound
        · rw [hcur, Nat.pow_succ, Nat.mul_comm]
        · exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hacc'

/-- The leastness of `chunkDepth`: `n ≤ 2 ^ d` forces
`chunkDepth n ≤ d`. -/
theorem chunkDepth_le (n d : Nat) (h : n ≤ 2 ^ d) : chunkDepth n ≤ d := by
  have h1 : (1 : Nat) = 2 ^ 0 := (Nat.pow_zero 2).symm
  have hpow2 : 2 ^ 0 ≤ 2 ^ d := Nat.pow_le_pow_right
    (by decide : (0 : Nat) < 2) (Nat.zero_le d)
  exact chunkDepth_go_le n d n 0 1 h1 hpow2 (Nat.zero_le d) h

end SizzLean.Proofs.Merkle
