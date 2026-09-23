import EthCLSpecs.Fulu.Committees
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Proofs.Fulu.CommitteeSize`: every beacon committee has a bounded, non-zero size

`compute_committee` (`phase0/beacon-chain.md:881`) slices the shuffled active set from
`len * index // count` to `len * (index + 1) // count`. `get_beacon_committee` (`:1098`) passes
`count = committees_per_slot * SLOTS_PER_EPOCH`. So a committee's size depends only on the
active count `n` and on `count`, and the shuffle plays no part.

The size is at least `1` whenever `count ≤ n`, and at most `⌈n / count⌉`. At the mainnet preset,
an active count in `[32, 2 ^ 22]` puts every committee size in `(0, MAX_VALIDATORS_PER_COMMITTEE]`.
Dafny proves the same bound as `ActiveValidatorBounds`. At the minimal preset the same holds for an
active count in `[8, 65536]`. `MAX_COMMITTEES_PER_SLOT` is `4` there, so the upper end is lower.

`computeCommittee` computes `start` and `stop` on `Nat`, where the pyspec computes them on
`uint64`. The two agree while `len * (index + 1)` stays below `2 ^ 64`. `get_beacon_committee`'s
callers bound `index` by the committee count, so that product stays far below `2 ^ 64`. These
theorems hold for any `index`, since they state only the slice length.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Fulu (Preset State ValidatorIndex Bytes32 Slot computeCommittee getBeaconCommittee
  getCommitteeCountPerSlot getActiveValidatorIndices computeEpochAtSlot minimal mainnet)

/-- A slice `[n * i / C, n * (i + 1) / C)` holds at least one element once `C ≤ n`. -/
private theorem slice_pos (n i C : Nat) (hC : 0 < C) (hn : C ≤ n) :
    1 ≤ n * (i + 1) / C - n * i / C := by
  have h : n * i / C + 1 ≤ (n * i + n) / C := by
    rw [← Nat.add_div_right _ hC]
    exact Nat.div_le_div_right (by omega)
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The same slice holds at most `⌈n / C⌉` elements. Write `n * i` as `C * q + r` with `r < C`.
The end point is `q + (r + n) / C`, and `(r + n) / C ≤ (C - 1 + n) / C`. -/
private theorem slice_le (n i C : Nat) (hC : 0 < C) :
    n * (i + 1) / C - n * i / C ≤ (n + C - 1) / C := by
  have hx := Nat.div_add_mod (n * i) C
  have hm := Nat.mod_lt (n * i) hC
  have heq : n * (i + 1) = (n * i % C + n) + C * (n * i / C) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [heq, Nat.add_mul_div_left _ _ hC]
  have : (n * i % C + n) / C ≤ (n + C - 1) / C := Nat.div_le_div_right (by omega)
  rw [Nat.add_sub_cancel]
  exact this

/-- **Size equation.** The committee is the slice's length of the shuffled active set. -/
theorem computeCommittee_size [Preset] [HasherTag] (indices : Array ValidatorIndex)
    (seed : Bytes32) (index count : Nat) :
    (computeCommittee indices seed index count).size =
      indices.size * (index + 1) / count - indices.size * index / count := by
  simp [computeCommittee]

/-- **Non-empty and bounded, at a symbolic preset.** A committee has at least one member when
the committee count for the epoch fits in the active count, and at most `⌈n / count⌉`. -/
theorem getBeaconCommittee_size_bounds [Preset] [HasherTag] (state : State) (slot : Slot)
    (index : Nat) :
    let n := (getActiveValidatorIndices state (computeEpochAtSlot slot)).size
    let count := getCommitteeCountPerSlot state (computeEpochAtSlot slot)
      * EthCLSpecs.Fulu.Const.slotsPerEpoch
    count ≤ n →
      1 ≤ (getBeaconCommittee state slot index).size ∧
        (getBeaconCommittee state slot index).size ≤ (n + count - 1) / count := by
  intro n count hcount
  have hspe := EthCLSpecs.Fulu.Const.slotsPerEpochPos
  have hcps : 1 ≤ getCommitteeCountPerSlot state (computeEpochAtSlot slot) := by
    simp only [getCommitteeCountPerSlot]
    exact Nat.le_max_left _ _
  have hC : 0 < count := Nat.mul_pos hcps hspe
  simp only [getBeaconCommittee, computeCommittee_size]
  exact ⟨slice_pos _ _ _ hC hcount, slice_le _ _ _ hC⟩

/-- **The mainnet bound.** An active count in `[32, 2 ^ 22]` puts every committee size in
`(0, MAX_VALIDATORS_PER_COMMITTEE]`, which is `(0, 2048]` at mainnet. -/
theorem getBeaconCommittee_size_mainnet [HasherTag] (state : @State mainnet _) (slot : Slot)
    (index : Nat) :
    letI : Preset := mainnet
    32 ≤ (getActiveValidatorIndices state (computeEpochAtSlot slot)).size →
      (getActiveValidatorIndices state (computeEpochAtSlot slot)).size ≤ 2 ^ 22 →
      0 < (getBeaconCommittee state slot index).size ∧
        (getBeaconCommittee state slot index).size
          ≤ EthCLSpecs.Fulu.Const.maxValidatorsPerCommittee := by
  letI : Preset := mainnet
  intro hlo hhi
  generalize hn : (getActiveValidatorIndices state (computeEpochAtSlot slot)).size = n at hlo hhi
  -- At mainnet, the committee count is `max 1 (min 64 (n / 32 / 128))`.
  have hcps : getCommitteeCountPerSlot state (computeEpochAtSlot slot)
      = max 1 (min 64 (n / 32 / 128)) := by
    rw [← hn]
    rfl
  have hspe : (@EthCLSpecs.Fulu.Const.slotsPerEpoch mainnet) = 32 := rfl
  have hmax : (@EthCLSpecs.Fulu.Const.maxValidatorsPerCommittee mainnet) = 2048 := rfl
  -- The count fits in the active set, and the set fits in 2048 committees' worth.
  have hfit : max 1 (min 64 (n / 32 / 128)) * 32 ≤ n ∧
      n ≤ 2048 * (max 1 (min 64 (n / 32 / 128)) * 32) := by
    rcases Nat.le_total 64 (n / 32 / 128) with h64 | h64
    · rw [Nat.min_eq_left h64, Nat.max_eq_right (by omega)]
      omega
    · rw [Nat.min_eq_right h64]
      rcases Nat.le_total 1 (n / 32 / 128) with h1 | h1
      · rw [Nat.max_eq_right h1]
        omega
      · rw [Nat.max_eq_left h1]
        omega
  have hb := getBeaconCommittee_size_bounds state slot index
  simp only [hn, hcps, hspe] at hb
  obtain ⟨hpos, hle⟩ := hb hfit.1
  refine ⟨hpos, ?_⟩
  rw [hmax]
  have hC : 0 < max 1 (min 64 (n / 32 / 128)) * 32 :=
    Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)) (by decide)
  have hdiv : (n + max 1 (min 64 (n / 32 / 128)) * 32 - 1) / (max 1 (min 64 (n / 32 / 128)) * 32)
      < 2049 := (Nat.div_lt_iff_lt_mul hC).mpr (by omega)
  omega

/-- **The minimal bound.** An active count in `[8, 65536]` puts every committee size in
`(0, MAX_VALIDATORS_PER_COMMITTEE]`, which is `(0, 2048]` at the minimal preset too. -/
theorem getBeaconCommittee_size_minimal [HasherTag] (state : @State minimal _) (slot : Slot)
    (index : Nat) :
    letI : Preset := minimal
    8 ≤ (getActiveValidatorIndices state (computeEpochAtSlot slot)).size →
      (getActiveValidatorIndices state (computeEpochAtSlot slot)).size ≤ 65536 →
      0 < (getBeaconCommittee state slot index).size ∧
        (getBeaconCommittee state slot index).size
          ≤ EthCLSpecs.Fulu.Const.maxValidatorsPerCommittee := by
  letI : Preset := minimal
  intro hlo hhi
  generalize hn : (getActiveValidatorIndices state (computeEpochAtSlot slot)).size = n at hlo hhi
  -- At minimal, the committee count is `max 1 (min 4 (n / 8 / 4))`.
  have hcps : getCommitteeCountPerSlot state (computeEpochAtSlot slot)
      = max 1 (min 4 (n / 8 / 4)) := by
    rw [← hn]
    rfl
  have hspe : (@EthCLSpecs.Fulu.Const.slotsPerEpoch minimal) = 8 := rfl
  have hmax : (@EthCLSpecs.Fulu.Const.maxValidatorsPerCommittee minimal) = 2048 := rfl
  have hfit : max 1 (min 4 (n / 8 / 4)) * 8 ≤ n ∧
      n ≤ 2048 * (max 1 (min 4 (n / 8 / 4)) * 8) := by
    rcases Nat.le_total 4 (n / 8 / 4) with h4 | h4
    · rw [Nat.min_eq_left h4, Nat.max_eq_right (by omega)]
      omega
    · rw [Nat.min_eq_right h4]
      rcases Nat.le_total 1 (n / 8 / 4) with h1 | h1
      · rw [Nat.max_eq_right h1]
        omega
      · rw [Nat.max_eq_left h1]
        omega
  have hb := getBeaconCommittee_size_bounds state slot index
  simp only [hn, hcps, hspe] at hb
  obtain ⟨hpos, hle⟩ := hb hfit.1
  refine ⟨hpos, ?_⟩
  rw [hmax]
  have hC : 0 < max 1 (min 4 (n / 8 / 4)) * 8 :=
    Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)) (by decide)
  have hdiv : (n + max 1 (min 4 (n / 8 / 4)) * 8 - 1) / (max 1 (min 4 (n / 8 / 4)) * 8)
      < 2049 := (Nat.div_lt_iff_lt_mul hC).mpr (by omega)
  omega

end EthCLSpecs.Proofs.Fulu
