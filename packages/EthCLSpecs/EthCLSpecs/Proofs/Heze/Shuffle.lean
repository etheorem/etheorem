import EthCLSpecs.Heze.EpochProcessing
import EthCLLib.Proofs.SwapOrNot

/-!
# `EthCLSpecs.Proofs.Heze.Shuffle`: `computeShuffledPermutation` is a permutation

Heze inherits `computeShuffledPermutation` from Fulu through Gloas
(`Heze/EpochProcessing.lean:79`). Heze therefore elaborates its own constant from
the Fulu body. The bridge and the proof are the Fulu ones in
`EthCLSpecs.Proofs.Fulu.Shuffle`, restated for the Heze constant. The Fulu module
docstring gives the success conditions and their reasons.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag StateTransitionError throwArithmetic liftErr le8 sha u32leBytes)
open EthCLLib.Proofs
open EthCLSpecs.Heze (Preset ValidatorIndex computeShuffledPermutation)
open EthCLSpecs.Heze.Const (shuffleRoundCount)

/-- The fold of the body is `swapOrNotArray`, at any round count. -/
private theorem shuffle_fold_eq [Preset] [HasherTag] (n : Nat) (seed : ByteArray) :
    (List.range shuffleRoundCount).foldl
      (fun indices round =>
        let seedRound := seed.push (UInt8.ofNat round)
        let pivot := (le8 (sha seedRound)) % n
        Array.ofFn (n := n) (fun i : Fin n =>
          let cur := (indices[i.val]!).toNat
          let flip := (pivot + n - cur) % n
          let position := Nat.max cur flip
          let source := sha (seedRound ++ u32leBytes (position / 256))
          let byteVal := (source.get! ((position % 256) / 8)).toNat
          let bit := (byteVal >>> (position % 8)) % 2
          if bit == 1 then UInt64.ofNat flip else UInt64.ofNat cur))
      (Array.ofFn (n := n) (fun i : Fin n => UInt64.ofNat i.val))
      = swapOrNotArray n shuffleRoundCount seed := by
  unfold swapOrNotArray
  congr 1
  funext a r
  simp only [swapOrNotStep, roundAt, swapOrNotRound, swapOrNotPivot, swapOrNotBit]
  congr 1
  funext i
  exact (apply_ite UInt64.ofNat _ _ _).symm

/-- A run succeeds exactly when the pyspec does not raise: no rounds, or `0 < n`,
`n ≤ 2 ^ 40`, and `SHUFFLE_ROUND_COUNT ≤ 256`. A successful run returns `swapOrNotArray`. -/
theorem computeShuffledPermutation_eq_ok_iff [Preset] [HasherTag] {n : Nat}
    (seed : ByteArray) (perm : Array ValidatorIndex) :
    computeShuffledPermutation n seed = .ok perm ↔
      (shuffleRoundCount = 0 ∨ (0 < n ∧ n ≤ 2 ^ 40 ∧ shuffleRoundCount ≤ 256)) ∧
        perm = swapOrNotArray n shuffleRoundCount seed := by
  unfold computeShuffledPermutation
  dsimp only
  by_cases hR0 : shuffleRoundCount = 0
  · have hc : (shuffleRoundCount == 0) = true := by simp [hR0]
    have hsw : swapOrNotArray n shuffleRoundCount seed =
        Array.ofFn (n := n) (fun i : Fin n => UInt64.ofNat i.val) := by
      simp only [swapOrNotArray, hR0, List.range_zero, List.foldl_nil]
    simp only [hc, ↓reduceIte, hsw]
    constructor
    · intro h
      exact ⟨Or.inl hR0, (Except.ok.inj h).symm⟩
    · rintro ⟨-, rfl⟩
      rfl
  · have hc : (shuffleRoundCount == 0) = false := by simp [hR0]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    by_cases hn0 : n = 0
    · have hc0 : (n == 0) = true := by simp [hn0]
      simp only [hc0, ↓reduceIte]
      refine iff_of_false (fun h => ?_) (by rintro ⟨h | ⟨h, -, -⟩, -⟩ <;> omega)
      simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at h <;> cases h
    · have hc0 : (n == 0) = false := by simp [hn0]
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, pure_bind]
      by_cases hd : 2 ^ 40 < n
      · simp only [hd, ↓reduceIte]
        refine iff_of_false (fun h => ?_) (by rintro ⟨h | ⟨-, h, -⟩, -⟩ <;> omega)
        simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at h <;> cases h
      · simp only [hd, ↓reduceIte]
        by_cases hr : 256 < shuffleRoundCount
        · simp only [hr, ↓reduceIte]
          refine iff_of_false (fun h => ?_) (by rintro ⟨h | ⟨-, -, h⟩, -⟩ <;> omega)
          simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at h <;> cases h
        · simp only [hr, ↓reduceIte]
          rw [shuffle_fold_eq]
          constructor
          · intro h
            exact ⟨Or.inr ⟨by omega, by omega, by omega⟩, (Except.ok.inj h).symm⟩
          · rintro ⟨-, rfl⟩
            rfl

/-- On the three bounds the run succeeds, and returns `swapOrNotArray`. -/
theorem computeShuffledPermutation_ok [Preset] [HasherTag] {n : Nat} (seed : ByteArray)
    (hn : 0 < n) (hdom : n ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256) :
    computeShuffledPermutation n seed = .ok (swapOrNotArray n shuffleRoundCount seed) :=
  (computeShuffledPermutation_eq_ok_iff seed _).mpr ⟨Or.inr ⟨hn, hdom, hR⟩, rfl⟩

/-- Slot `i` of a successful run holds `shuffleNat` of `i`. -/
theorem computeShuffledPermutation_getElem [Preset] [HasherTag] {n i : Nat}
    (seed : ByteArray) {perm : Array ValidatorIndex}
    (h : computeShuffledPermutation n seed = .ok perm) (h64 : n < 2 ^ 64) (hi : i < n) :
    (perm[i]!).toNat = shuffleNat n seed shuffleRoundCount i := by
  rw [((computeShuffledPermutation_eq_ok_iff seed perm).mp h).2]
  exact (swapOrNotArray_spec seed h64 _).2 i hi

/-- `compute_shuffled_permutation` returns a permutation of `[0, index_count)` whenever
it does not raise. -/
@[characterizes EthCLSpecs.Heze.computeShuffledPermutation]
theorem computeShuffledPermutation_perm [Preset] [HasherTag] (n : Nat) (seed : ByteArray)
    {perm : Array ValidatorIndex} (h : computeShuffledPermutation n seed = .ok perm)
    (h64 : n < 2 ^ 64) :
    (perm.toList.map UInt64.toNat).Perm (List.range n) := by
  rw [((computeShuffledPermutation_eq_ok_iff seed perm).mp h).2]
  exact swapOrNotArray_perm seed h64 _

end EthCLSpecs.Proofs.Heze
