import EthCLSpecs.Proofs.Heze.DriftRun

/-!
# `EthCLSpecs.Proofs.Heze.StakeDrift`: the stake drift along a chain run

`chainRun_drift_le` bounds the drift of the link stakes and of the total active balance
along a chain run from `st₀` to `u` (`drift`). The bound `driftBound` reads `st₀`, the end
epoch `E`, the churn bounds `CX` and `CC`, and the bounds `sq`, `U`, `S` of the run.

The proof runs the invariant `RunAcc` along the run (`runAcc_run`). At the end, `RunInv`
gives the facts of `EndFacts` (`RunInv.endFacts`), and they bound the drift
(`drift_le_of_endFacts`). The budget of the run is the potentials of `st₀`, the cost of each
block and of each epoch, and the correlation penalties of the slashed validators of `st₀`.
A validator pays its correlation penalty at one epoch at most (`sum_slEpoch_le`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- The correlation penalties of the slashed validators of `st₀`. -/
def slashTotal (st₀ : BeaconState) : Nat :=
  ((List.range (sizeOf st₀)).map fun i => if slashedOf st₀ i then 2 * maxEBN else 0).sum

omit [Preset] [HasherTag] in
theorem sum_comm {α β : Type} (f : α → β → Nat) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.map fun a => (l₂.map (f a)).sum).sum = (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp only [List.map_nil, List.sum_nil]; exact (sum_zero_of _ (by simp)).symm
  | cons a rest ih =>
    intro l₂
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← sum_map_add]

omit [Preset] [HasherTag] in
/-- A payment due at the one epoch `w - h` is paid at most once over consecutive epochs. -/
theorem sum_once (c e₀ h w : Nat) :
    ∀ k, ((List.range k).map fun j => if w = e₀ + j + h then c else 0).sum =
      if e₀ + h ≤ w ∧ w < e₀ + k + h then c else 0 := by
  intro k
  induction k with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil]; rw [if_neg (by omega)]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h1 : e₀ + h ≤ w ∧ w < e₀ + k + h
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega), Nat.add_zero]
    · rw [if_neg h1]
      by_cases h2 : w = e₀ + k + h
      · rw [if_pos h2, if_pos (by omega), Nat.zero_add]
      · rw [if_neg h2, if_neg (by omega)]

omit [HasherTag] in
/-- **The correlation penalties of consecutive epochs add up to at most `slashTotal`.** -/
theorem sum_slEpoch_le (st₀ : BeaconState) (e₀ k : Nat) :
    ((List.range k).map fun j => slEpoch st₀ (e₀ + j)).sum ≤ slashTotal st₀ := by
  unfold slEpoch slashTotal
  rw [sum_comm (fun j i => slBud st₀ (e₀ + j) i)]
  refine sum_le_sum (fun i => ?_) _
  unfold slBud
  by_cases hs : i < sizeOf st₀ ∧ slashedOf st₀ i = true
  · have e : ∀ j, (if i < sizeOf st₀ ∧ slashedOf st₀ i = true ∧
        wdrOf st₀ i = e₀ + j + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 then 2 * maxEBN
        else 0) = if wdrOf st₀ i = e₀ + j + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2
          then 2 * maxEBN else 0 := fun j => by
      by_cases hw : wdrOf st₀ i = e₀ + j + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2
      · rw [if_pos ⟨hs.1, hs.2, hw⟩, if_pos hw]
      · rw [if_neg (fun h => hw h.2.2), if_neg hw]
    simp only [e, sum_once]
    rw [if_pos hs.2]
    split <;> omega
  · have : ∀ j, (if i < sizeOf st₀ ∧ slashedOf st₀ i = true ∧
        wdrOf st₀ i = e₀ + j + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 then 2 * maxEBN
        else 0) = 0 := fun j => by rw [if_neg (fun h => hs ⟨h.1, h.2.1⟩)]
    simp only [this]
    rw [sum_zero_of _ (by simp)]
    exact Nat.zero_le _

omit [HasherTag] in
theorem ebSum_eq (t : BeaconState) :
    ebSum t = (t.validators.val.toList.map (·.effectiveBalance.toNat)).sum := by
  unfold ebSum sizeOf
  rw [← sum_range_getElem! t.validators.val (·.effectiveBalance.toNat)]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← eb!_eq, sszList_getElem!_eq]

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **The bound of the stake drift.** The EB term covers the distances at `st₀` and the
budget of the run: the potentials of `st₀`, `E - e₀ + 1` epochs of slots of blocks, `E - e₀`
epochs, and the correlation penalties. The set term covers the pending activations and the
scheduled exits of `st₀`, and the exits that the churn of the run paid for. -/
def driftBound (vals : List ValidatorIndex) (st₀ : BeaconState) (E CX CC sq U S : Nat) : Nat :=
  incN + 4 * abound aN downN (epsSum st₀ + (phi vals E st₀ +
    (E - epochN st₀ + 1) * EthCLSpecs.Heze.Const.slotsPerEpoch * blockBudget sq U +
    (E - epochN st₀) * epochBudget sq U S + slashTotal st₀)) +
  2 * (pendSum st₀ + schedSum st₀ E + neBound st₀ E CX CC)

/-- **The stake drift along a chain run.** A chain run from `st₀` to `u` ends at the epoch `E`
of `u`, within `EPOCHS_PER_SLASHINGS_VECTOR / 2` epochs of `st₀`. Each state of the run meets
`StatePre`, each block meets `BlockAmountsOK`, and `ΓX` covers the churn reservations of one
more block than the slots of the run. `vals` holds the registry of each state of the run.
Then the drift of the link stakes and of the total active balance is at most
`driftBound vals st₀ E CX CC sq U S`. -/
theorem chainRun_drift_le {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {vals : List ValidatorIndex} {st₀ u : BeaconState} {CX CC NX ΓX sq U S : Nat}
    (C : DriftConsts) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀) (h0 : 0 < sq) (hinc : incN ≤ U)
    (hU64 : U < 2 ^ 64) (run : ChainRun hi steps st₀ u)
    (hk2 : epochN u < epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2)
    (hEf : epochN u + 1 < farN)
    (hpre : ∀ s₁ s₂ t, steps = s₁ ++ s₂ → ChainRun hi s₁ st₀ t →
      StatePre vals st₀ t (epochN u) CX CC NX ΓX sq U S)
    (hblk : ∀ sb vr, ChainStep.block sb vr ∈ steps → BlockAmountsOK sb)
    (hΓ : (u.slot.toNat - st₀.slot.toNat + 1) * maxWR ≤ ΓX)
    (delay : Nat) (hdelay : 2 ≤ delay)
    (hwd₀ : ∀ i, i < sizeOf st₀ → exitOf st₀ i ≠ farN → exitOf st₀ i + delay ≤ wdrOf st₀ i) :
    drift vals st₀ u ≤ driftBound vals st₀ (epochN u) CX CC sq U S := by
  have P₀ := hpre [] steps st₀ rfl (.nil _)
  have Pu := hpre steps [] u (by simp) run
  -- The invariant at the start, carried along the run.
  have A₀ : RunAcc vals st₀ (epochN u) CX CC sq U S st₀ := ⟨_, _, _, 0, 0, by
    unfold runB
    simp only [Nat.sub_self, List.range_zero, List.map_nil, List.sum_nil, Nat.zero_mul, Nat.add_zero]
    exact RunInv.init vals st₀ _ CX CC hshape₀, Nat.zero_le _, by split <;> omega⟩
  obtain ⟨V, W, tag, Γp, nb, I, -, hnb⟩ :=
    runAcc_run hhi C hnd hshape₀ h0 hinc hk2 hEf hpre hblk hΓ steps st₀ run [] rfl (.nil _) A₀
  -- The end facts and the drift.
  have hsum : ∀ t : BeaconState, ebSum t ≤ U →
      (t.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64 := fun t ht => by
    rw [← ebSum_eq]; omega
  have he0 : epochN st₀ ≤ epochN u := by
    rw [epochN_eq, epochN_eq]; exact Nat.div_le_div_right (run.slot_le hhi).1
  have F := I.endFacts hnd P₀.cov (by have := P₀.s40; unfold sizeOf at this; omega)
    (by have := Pu.s40; unfold sizeOf at this; omega) (hsum st₀ P₀.ebU) (hsum u Pu.ebU) rfl he0
    hEf delay hdelay hshape₀ hwd₀
  refine Nat.le_trans (drift_le_of_endFacts F) ?_
  unfold driftBound
  refine Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (abound_mono
    (Nat.add_le_add_left ?_ _))) _) _
  -- The budget of the run.
  unfold runB
  have hspe := EthCLSpecs.Heze.Const.slotsPerEpochPos
  -- The blocks are at most the slots of the epochs of the run.
  have hnb' : nb ≤ (epochN u - epochN st₀ + 1) * EthCLSpecs.Heze.Const.slotsPerEpoch := by
    have h1 : nb ≤ u.slot.toNat - st₀.slot.toNat + 1 := by
      have : 0 ≤ (if u.latestBlockHeader.slot < u.slot then 1 else 0) := Nat.zero_le _
      omega
    rw [epochN_eq, epochN_eq]
    have hab := (run.slot_le hhi).1
    generalize u.slot.toNat = a at h1 hab
    generalize st₀.slot.toNat = b at h1 hab
    generalize EthCLSpecs.Heze.Const.slotsPerEpoch = n at hspe ⊢
    have h4 : b / n ≤ a / n := Nat.div_le_div_right hab
    have e : (a / n - b / n + 1) * n = a / n * n - b / n * n + n := by
      rw [Nat.add_mul, Nat.sub_mul, Nat.one_mul]
    have h2 : a < a / n * n + n := by
      have := Nat.div_add_mod a n
      have := Nat.mod_lt a hspe
      have : n * (a / n) = a / n * n := Nat.mul_comm _ _
      omega
    have h3 : b / n * n ≤ b := Nat.div_mul_le_self b n
    have h5 : b / n * n ≤ a / n * n := Nat.mul_le_mul_right n h4
    omega
  have hblk' := Nat.mul_le_mul_right (blockBudget sq U) hnb'
  have hep : ((List.range (epochN u - epochN st₀)).map fun j =>
      epochBudget sq U S + slEpoch st₀ (epochN st₀ + j)).sum ≤
      (epochN u - epochN st₀) * epochBudget sq U S + slashTotal st₀ := by
    rw [sum_map_add, List.map_const', List.sum_replicate_nat, List.length_range]
    exact Nat.add_le_add_left (sum_slEpoch_le st₀ _ _) _
  omega

end

end EthCLSpecs.Proofs.Heze
