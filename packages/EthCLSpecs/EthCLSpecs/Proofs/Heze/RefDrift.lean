import EthCLSpecs.Proofs.Heze.ForkPoint
import EthCLSpecs.Proofs.Heze.StakeDrift

/-!
# `EthCLSpecs.Proofs.Heze.RefDrift`: the stake of each chain, measured from the fork point

Accountable safety (`EthCLLib.Proofs.FFG.ffg_accountable_safety`) measures the stake of each
chain against one reference stake (`StakeClose`). Here the reference comes from the fork point
`st₀`. It holds the effective balance of each validator active at the current epoch of `st₀`
(`activeOf`). It also holds the total active balance of `st₀`. A reference sum over the validators is at
most that total.

## The measured drift

`refDrift st₀ u` measures a state `u` against the reference. It adds the distances of the link
stakes of `u` from `activeOf st₀`, over `regVals`, and the shortfall of the total of `u`.
`runDrift` takes the largest `refDrift` over the states of a run (`OnRun`). From the epoch of
`st₀` on, each weigh state of the chain is a state of the run after the fork point
(`ForkAt.stakeState_onRun`). So the chain stays within `runDrift` of the reference from that
epoch on (`ForkAt.stakeClose`).

## Against `drift`

`drift` (`DriftBound.lean`) measures against `linkStake st₀`. That stake also counts each
validator that is active at the previous epoch only. Such a validator exits at the current epoch
of `st₀`. The two references differ by the stake of those validators (`exitStake`). So
`refDrift` is at most `drift` plus `exitStake` (`refDrift_le_drift`). With this bound,
`chainRun_drift_le` bounds `refDrift` state by state.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLLib.Proofs.FFG (stakeSum absDiffSum)
open EthCLSpecs.Heze (Preset Config BeaconState ValidatorIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section
variable [Preset] [HasherTag]

/-- The reference stake of a validator: its effective balance when it is active at the current
epoch of `st₀`, else zero. -/
def activeOf (st₀ : BeaconState) (i : ValidatorIndex) : Nat :=
  if acB st₀ i.toNat then ebN st₀ i.toNat else 0

/-- The reference stake of a list of validators. -/
def activeStake (st₀ : BeaconState) (X : List ValidatorIndex) : Nat :=
  stakeSum (activeOf st₀) X

/-- The total active balance of a state, as a number (`totBal`). -/
def totalOf (u : BeaconState) : Nat :=
  (totBal u).toNat

/-- The distance of `u` from the fork point `st₀`. It adds the distances of the link stakes of
`u` from the reference, over `regVals`, and the shortfall of the total of `u`. -/
def refDrift (st₀ u : BeaconState) : Nat :=
  absDiffSum (linkStake u) (activeOf st₀) regVals + (totalOf st₀ - totalOf u)

/-- The stake of the validators of `st₀` that are active at the previous epoch only. These
validators exit at the current epoch. -/
def exitStake (st₀ : BeaconState) : Nat :=
  (regVals.map fun i => if laB st₀ i.toNat && !acB st₀ i.toNat then ebN st₀ i.toNat else 0).sum

/-- **`refDrift` against `drift`.** The measured drift is at most the stake drift plus the
stake that exits at the epoch of `st₀`. -/
theorem refDrift_le_drift (st₀ u : BeaconState) :
    refDrift st₀ u ≤ drift regVals st₀ u + exitStake st₀ := by
  unfold refDrift drift exitStake totalOf absDiffSum
  -- Each distance to the reference is at most the distance to the link stake of `st₀`, plus
  -- the stake of an exiting validator.
  have hpt : ∀ i : ValidatorIndex,
      (linkStake u i - activeOf st₀ i) + (activeOf st₀ i - linkStake u i) ≤
        ((linkStake u i - linkStake st₀ i) + (linkStake st₀ i - linkStake u i)) +
        (if laB st₀ i.toNat && !acB st₀ i.toNat then ebN st₀ i.toNat else 0) := by
    intro i
    unfold activeOf
    rw [linkStake_eq st₀ i]
    -- An index active at the current epoch has the link gate too.
    have hla : acB st₀ i.toNat = true → laB st₀ i.toNat = true := laB_of_acB
    cases hl : laB st₀ i.toNat <;> cases ha : acB st₀ i.toNat
    · simp
    · rw [hl, ha] at hla
      exact absurd (hla rfl) (by decide)
    · simp; omega
    · simp
  have := sum_map_le_sum_map _ _ hpt regVals
  have h2 := sum_map_add (fun i : ValidatorIndex =>
      (linkStake u i - linkStake st₀ i) + (linkStake st₀ i - linkStake u i))
    (fun i : ValidatorIndex =>
      if laB st₀ i.toNat && !acB st₀ i.toNat then ebN st₀ i.toNat else 0) regVals
  omega

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `u` is a state of the run of `steps` from `st₀`: the end of a prefix. -/
def OnRun (hi : Nat) (st₀ : BeaconState) (steps : List ChainStep) (u : BeaconState) : Prop :=
  ∃ s₁ s₂, steps = s₁ ++ s₂ ∧ ChainRun hi s₁ st₀ u

/-- The largest `refDrift` of a state of the run of `steps` from `st₀`. -/
noncomputable def runDrift (hi : Nat) (st₀ : BeaconState) (steps : List ChainStep) : Nat :=
  ((List.range (steps.length + 1)).map fun n =>
    (endState hi (steps.take n) st₀).elim 0 (refDrift st₀)).foldr max 0

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- A member of a list is at most its largest value. -/
theorem le_foldr_max {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.foldr max 0
  | y :: l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- Each state of the run is within `runDrift`. -/
theorem refDrift_le_runDrift {hi : Nat} {st₀ u : BeaconState} {steps : List ChainStep}
    (h : OnRun hi st₀ steps u) : refDrift st₀ u ≤ runDrift hi st₀ steps := by
  obtain ⟨s₁, s₂, hs, hr⟩ := h
  have ht : steps.take s₁.length = s₁ := by rw [hs]; exact List.take_left
  refine le_foldr_max (List.mem_map.mpr ⟨s₁.length, List.mem_range.mpr ?_, ?_⟩)
  · rw [hs, List.length_append]
    omega
  · rw [ht, endState_of hr]
    rfl

/-- Take a weigh state at an epoch from the epoch of the fork point on, or the end state. It is
a state of the rest of the run after the fork point. -/
theorem ForkAt.stakeState_onRun {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X) {e : Nat}
    (he : epochOf st₀ ≤ e) {u : BeaconState} (hs : stakeState hi steps₁ A e = some u) :
    OnRun hi st₀ r₁ u := by
  have hrest := F.rest₁ h₁
  unfold stakeState at hs
  cases hw : weighState hi steps₁ A e with
  | some w =>
    rw [hw] at hs
    have hwu : w = u := by simpa using hs
    subst hwu
    -- Case: the weigh state of `e`.
    have hwa : WeighAt hi steps₁ A e w := by
      unfold weighState at hw
      split at hw
      · rename_i hex
        cases hw
        exact hex.choose_spec
      · cases hw
    obtain ⟨s₁, s₂, hss, hr, hb, hwe⟩ := hwa
    -- The weigh slot is at or after the slot of `st₀`.
    have hslot : st₀.slot.toNat ≤ w.slot.toNat := by
      obtain ⟨hb', he'⟩ := lastSlot_facts e
      have hw' := slot_of_last hb hb' (hwe.trans he'.symm)
      have h0 := Nat.lt_mul_div_succ st₀.slot.toNat slotsPerEpochPos
      have h1 : (st₀.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ (e + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by unfold epochOf at he; omega)
      rw [Nat.mul_comm] at h0
      omega
    rw [F.eq₁] at hss
    rcases List.append_eq_append_iff.mp hss with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
    · -- `s₁ = p₁ ++ m`: the weigh state comes after `st₀`.
      rw [hm] at hr
      obtain ⟨z, hz, hzm⟩ := hr.split
      rw [← F.run₁.det hz] at hzm
      exact ⟨m, .slot :: s₂, hm', hzm⟩
    · -- `p₁ = s₁ ++ m`: then `st₀` comes after the slot step from `w`, unless `m` is empty.
      cases m with
      | nil =>
        rw [List.append_nil] at hm
        subst hm
        rw [hr.det F.run₁]
        exact ⟨[], r₁, rfl, .nil _⟩
      | cons x m =>
        have hx : x = .slot := (List.cons.inj hm').1.symm
        subst hx
        have hrun := F.run₁
        rw [hm] at hrun
        obtain ⟨z, hz, hzm⟩ := hrun.split
        rw [← hr.det hz] at hzm
        cases hzm with
        | slot hlt hstep hrest' =>
          have hlt' : w.slot.toNat < hi := hlt
          have h1 := hstep.slot (by omega)
          have h2 := (hrest'.slot_le hhi).1
          omega
  | none =>
    -- Case: the end state, which ends the rest of the run.
    rw [hw, endState_of h₁] at hs
    cases hs
    exact ⟨r₁, [], by simp, hrest⟩

/-- **The chain stays close to the fork point.** The chain of run 1 is over `regVals`. From the
epoch of the fork point on, it stays within `runDrift` of the rest of the run. The reference is
`activeOf st₀` and the total of `st₀`. -/
theorem ForkAt.stakeClose {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (hcps : AnchorCps A) (hord : StateCkptOrd A) (htot : RunTotals st₀) (E : Nat) :
    EthCLLib.Proofs.FFG.StakeClose (activeOf st₀) (totalOf st₀) (ffgChain hi steps₁ A regVals)
      (epochOf st₀) E (runDrift hi st₀ r₁) := by
  have hm := ffgChain_matches (hi := hi) (vals := regVals) hcps hord (h₁.blocks_slot_ge hhi)
  refine ⟨regVals_nodup, ?_, fun e he _ => ?_⟩
  · -- The reference sum is at most the total of `st₀`.
    obtain ⟨-, hsum, h64⟩ := htot
    have := sum_vals_le_range regVals regVals_nodup
      (fun i => if acB st₀ i then ebN st₀ i else 0) st₀.validators.val.size (fun i hi' => by
        dsimp only
        unfold acB
        rw [Array.getElem?_eq_none hi']
        rfl)
    unfold stakeSum totalOf
    rw [totalActive_toNat st₀ (by omega) h64]
    exact Nat.le_trans this (Nat.le_max_left _ _)
  · -- The state that weighs `e` is a state of the rest of the run.
    obtain ⟨u, hu⟩ : ∃ u, stakeState hi steps₁ A e = some u := by
      unfold stakeState
      split
      · exact ⟨_, rfl⟩
      · exact ⟨X, endState_of h₁⟩
    have hd := refDrift_le_runDrift (F.stakeState_onRun hhi h₁ he hu)
    obtain ⟨htot', hst⟩ := hm.stake e u hu
    have hstake : (ffgChain hi steps₁ A regVals).stake e = linkStake u := funext hst
    rw [hstake, htot', hm.vals]
    simp only [refDrift, totalOf] at hd ⊢
    constructor <;> omega

end

end EthCLSpecs.Proofs.Heze
