import EthCLSpecs.Proofs.Gloas.EpochSuccess.Registry
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Consolidations

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Deposits`: the deposit queue drains

The Gloas counterpart of `Proofs/Fulu/EpochSuccess/Deposits.lean`. `addValidatorToRegistry` takes
`set_or_append_list`'s append branch five times on a state whose registry sizes agree; Gloas's
registry lists are progressive, so no append can fail, and the queue's leftover goes back whole. A deposit either tops up a balance or
appends a validator capped at `MAX_EFFECTIVE_BALANCE_ELECTRA`; both raise the balance cap by one
deposit amount. The scan applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits.

Inside the scan the registry grows before the queue is trimmed, so the stage's registry potential
runs ahead by up to the number of deposits dequeued (`StageCaps.slack`). The trimmed queue pays
the slack back: an applied deposit leaves the queue, and a postponed one stays.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub umin umax)
open EthCLSpecs.Gloas

section

variable [Preset] [HasherTag]

section RegistryAppend

/-- Inside this section the walk's `if` rule refutes a branch guard against every hypothesis, as in
`addValidatorToRegistry_keepsCore`: the registry-size equalities rule out
`set_or_append_list`'s overwrite and reject branches. -/
local macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| (with_reducible refine runSucceeds_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [*, box_reduce] at hc; done))

theorem addValidatorToRegistry_succeeds (st : BeaconState) (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei)
    (hrs : RegistrySizes st) :
    RunSucceeds st (addValidatorToRegistry (StateTransition := GloasRun) pk wc amt)
      (fun _ st' => ∃ l1 l2 l3 l4 l5,
        st' = { st with
          validators := l1
          balances := l2
          previousEpochParticipation := l3
          currentEpochParticipation := l4
          inactivityScores := l5 } ∧
        l1.val = st.validators.val.push (getValidatorFromDeposit pk wc amt) ∧
        l2.val = st.balances.val.push amt ∧ l3.val = st.previousEpochParticipation.val.push 0 ∧
        l4.val = st.currentEpochParticipation.val.push 0 ∧ l5.val = st.inactivityScores.val.push 0) := by
  obtain ⟨hb, hi, hp, hq⟩ := hrs
  simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
  unfold addValidatorToRegistry
  run_succeeds
  -- A progressive list never refuses an append, so the walk passes all five writes.
  exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩


end RegistryAppend

/-- A pubkey lookup returns an index in the registry. -/
theorem validatorIndexByPubkey?_lt {st : BeaconState} {pk : BLSPubkey} {vi : Nat}
    (h : validatorIndexByPubkey? (pureState st) pk = some vi) : vi < st.validators.val.size :=
  (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).1

variable [Config]

omit [HasherTag] in
/-- A `Stage` state after a registry append of a deposit's validator, with the deposit's amount
under the balance cap: the registry potential grows by one, and the new validator is inactive. -/
theorem Stage.addValidator [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {st : BeaconState} (hst : Stage b v caps st) (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei)
    (hamt : amt.toNat ≤ caps.balance)
    (l1 : SizzLean.Repr.ProgressiveList Validator)
    (l2 : SizzLean.Repr.ProgressiveList Gwei)
    (l3 l4 : SizzLean.Repr.ProgressiveList ParticipationFlags)
    (l5 : SizzLean.Repr.ProgressiveList UInt64)
    (h1 : l1.val = st.validators.val.push (getValidatorFromDeposit pk wc amt))
    (h2 : l2.val = st.balances.val.push amt) (h3 : l3.val = st.previousEpochParticipation.val.push 0)
    (h4 : l4.val = st.currentEpochParticipation.val.push 0) (h5 : l5.val = st.inactivityScores.val.push 0) :
    Stage b v { caps with slack := caps.slack + 1 }
      { st with
          validators := l1
          balances := l2
          previousEpochParticipation := l3
          currentEpochParticipation := l4
          inactivityScores := l5 } := by
  obtain ⟨hb, hi, hp, hq⟩ := hst.registrySizes
  simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
  have hs1 : l1.val.size = st.validators.val.size + 1 := by rw [h1, Array.size_push]
  have hold : ∀ i (hi : i < st.validators.val.size), l1.val[i]'(by rw [hs1]; omega) = st.validators.val[i] :=
    fun i hi => by simp only [h1, Array.getElem_push, hi, dite_true]
  refine ⟨hst.slot, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hst.consolidationCount, ?_, hst.depositCap,
    hst.exitBound, hst.historyBound, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  all_goals try simp only [SizzLean.Repr.ProgressiveList.size]
  · rw [h2, hs1, Array.size_push, hb]
  · rw [h5, hs1, Array.size_push, hi]
  · rw [h3, hs1, Array.size_push, hp]
  · rw [h4, hs1, Array.size_push, hq]
  · have := hst.vGrows; rw [hs1]; omega
  · have := hst.potential; unfold registryPotential at this ⊢; dsimp only; rw [hs1]; omega
  · intro pc hpc
    have := hst.consolidationIdx pc hpc
    rw [hs1]; omega
  · intro x hx
    rw [h1] at hx
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hst.effCap x hx
    · unfold getValidatorFromDeposit
      exact Nat.le_trans (umin_toNat_le_right _ _) (getMaxEffectiveBalance_le _)
  · intro x hx
    rw [h2] at hx
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hst.balanceBound x hx
    · exact hamt
  · refine Live.mono (w := st) hst.live.1 (by rw [hs1]; omega) (fun i hi hi' ha => ?_)
    show isActiveValidator l1.val[i] _ = true
    rw [hold i hi]; exact ha
  · refine Live.mono (w := st) hst.live.2 (by rw [hs1]; omega) (fun i hi hi' ha => ?_)
    show isActiveValidator l1.val[i] _ = true
    rw [hold i hi]; exact ha
  · obtain ⟨i, hi, ha, hsl⟩ := hst.liveUnslashed
    refine ⟨i, by show i < l1.val.size; rw [hs1]; omega, ?_⟩
    show isActiveValidator l1.val[i] _ = true ∧ l1.val[i].slashed = false
    rw [hold i hi]; exact ⟨ha, hsl⟩
  · refine Nat.le_trans hst.liveCount (EthCLLib.Proofs.indicesWhere_size_mono
      (show st.validators.val.size ≤ l1.val.size by rw [hs1]; omega) (fun i hi ha => ?_))
    rw [getElem!_pos _ i hi] at ha
    rw [getElem!_pos l1.val i (by rw [hs1]; omega), hold i hi]
    exact ha


variable [CryptoBackend]

theorem applyPendingDeposit_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {st : BeaconState} (hst : Stage b v caps st) (d : PendingDeposit)
    (hd : d.amount.toNat ≤ b.deposit) (hroom : caps.balance + b.deposit < 2 ^ 64)
    (hV : st.validators.val.size < 2 ^ 64) :
    RunSucceeds st (applyPendingDeposit (StateTransition := GloasRun) d)
      (fun _ st' => Stage b v { caps with balance := caps.balance + b.deposit, slack := caps.slack + 1 } st' ∧
        st'.validators.val.size ≤ st.validators.val.size + 1 ∧
        st'.pendingDeposits = st.pendingDeposits) := by
  have hraise : Stage b v { caps with balance := caps.balance + b.deposit, slack := caps.slack + 1 } st :=
    hst.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega)
  unfold applyPendingDeposit
  run_succeeds
  split
  · -- A top-up: the deposit's amount joins an existing balance.
    rename_i vi hvi
    have hlt := validatorIndexByPubkey?_lt hvi
    have hidx := toNat_ofNat_registry (Nat.lt_trans hlt hV)
    have hbal := hst.registrySizes.1
    simp only [SizzLean.Repr.ProgressiveList.size] at hbal
    have hib : (UInt64.ofNat vi).toNat < st.balances.size := by
      show _ < st.balances.val.size; rw [hidx, hbal]; exact hlt
    have hold := hst.balanceBound _ (plist_getElem!_mem _ hib)
    run_succeeds
    refine RunSucceeds.weaken (increaseBalance_succeeds _ _ _ _ ?_ ?_) (fun _ _ h => ?_)
    · exact hib
    · omega
    obtain ⟨hu, hb'⟩ := h
    subst hb'
    replace hu := hu.symm
    subst hu
    run_succeeds
    refine ⟨?_, by simp [box_reduce], by simp [box_reduce]⟩
    have hy : (st.balances[(UInt64.ofNat vi).toNat]! + d.amount).toNat ≤ caps.balance + b.deposit := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
    have hs' := hst.setBalances (cap := caps.balance + b.deposit) _
      (SizzLean.Proofs.progressiveListSet!_size _ (UInt64.ofNat vi).toNat _)
      (plist_set!_bound (j := (UInt64.ofNat vi).toNat)
        (fun x hx => Nat.le_trans (hst.balanceBound x hx) (Nat.le_add_right _ _)) hy)
    exact hs'.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega)
  · run_succeeds
    · refine RunSucceeds.weaken (addValidatorToRegistry_succeeds _ _ _ _ hst.registrySizes)
        (fun _ _ h => ?_)
      obtain ⟨l1, l2, l3, l4, l5, rfl, h1, h2, h3, h4, h5⟩ := h
      refine ⟨?_, by simp [h1], by first | rfl | trivial⟩
      exact (hst.mono (caps' := { caps with balance := caps.balance + b.deposit })
        (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _)).addValidator _ _ _
        (by dsimp only; omega) l1 l2 l3 l4 l5 h1 h2 h3 h4 h5
    · exact ⟨hraise, by omega, by first | rfl | trivial⟩


/-- What the deposit scan keeps, with `ndi` deposits dequeued: the queue is untouched, every
postponed deposit is under the amount cap, the registry has grown by at most the deposits applied,
and the stage holds with the balance cap raised by one deposit per dequeued entry. -/
def ScanInv [PresetValid] (b : EpochBudget) (v : BeaconState) (caps : StageCaps) (w : BeaconState)
    (deposits : Array PendingDeposit) (scan : DepositScan) (st : BeaconState) : Prop :=
  scan.ndi ≤ deposits.size ∧ scan.ndi ≤ Const.maxPendingDepositsPerEpoch ∧
  (∀ d ∈ scan.postpone, d.amount.toNat ≤ b.deposit) ∧ scan.postpone.size ≤ scan.ndi ∧
  st.validators.val.size + scan.postpone.size ≤ w.validators.val.size + scan.ndi ∧
  st.pendingDeposits = w.pendingDeposits ∧
  Stage b v { caps with balance := caps.balance + scan.ndi * b.deposit, slack := caps.slack + scan.ndi } st

theorem ppdLoop_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) (deposits : Array PendingDeposit)
    (hdep : ∀ d ∈ deposits, d.amount.toNat ≤ b.deposit)
    (hreg : registryPotential v + caps.slack + Const.maxPendingDepositsPerEpoch < 2 ^ 64)
    (hroom : caps.balance + Const.maxPendingDepositsPerEpoch * b.deposit < 2 ^ 64)
    (finalizedSlot avail : Gwei) (nextEpoch : Epoch) :
    RunSucceeds w (ppdLoop (StateTransition := GloasRun) deposits finalizedSlot avail nextEpoch)
      (fun scan st => ScanInv b v caps w deposits scan st) := by
  unfold ppdLoop
  refine runSucceeds_fuelLoop (fun fuel scan st => scan.ndi + fuel = deposits.size + 1 ∧
      ScanInv b v caps w deposits scan st)
    _ (fun fuel scan st hI => ?_) (fun _ _ h => absurd h.1 (by have := h.2.1; omega)) _ _ _
    ⟨by simp, by simp, by simp, fun _ h => by simp at h, by simp, by simp, rfl, by simpa using hw⟩
  obtain ⟨hfuel, hndi, hmax, hpost, hple, hsz, hpd, hst⟩ := hI
  have hsm : (scan.ndi + 1) * b.deposit = scan.ndi * b.deposit + b.deposit := Nat.succ_mul _ _
  have hvg := hst.vGrows
  run_succeeds
  -- The scan stops: the invariant is the postcondition.
  all_goals try exact ⟨hndi, hmax, hpost, hple, hsz, hpd, hst⟩
  -- A postponed deposit: no state change, one more entry on the postpone list.
  all_goals try
    (have hlt : scan.ndi < deposits.size := by omega
     have hmem : deposits[scan.ndi]! ∈ deposits := by
       rw [getElem!_pos deposits _ hlt]; exact Array.getElem_mem _
     refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, fun d hd => ?_, ?_, ?_, hpd, ?_⟩
     · simp only [Array.mem_push] at hd
       rcases hd with hd | rfl
       · exact hpost d hd
       · exact hdep _ hmem
     · simp only [Array.size_push]; omega
     · simp only [Array.size_push]; omega
     · exact hst.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega))
  -- An applied deposit: `applyPendingDeposit` raises the caps by one deposit.
  all_goals
    have hlt : scan.ndi < deposits.size := by omega
    have hltm : scan.ndi < Const.maxPendingDepositsPerEpoch := by omega
    have hmem : deposits[scan.ndi]! ∈ deposits := by
      rw [getElem!_pos deposits _ hlt]; exact Array.getElem_mem _
    have hmul : (scan.ndi + 1) * b.deposit ≤ Const.maxPendingDepositsPerEpoch * b.deposit :=
      Nat.mul_le_mul_right _ hltm
    refine RunSucceeds.weaken (applyPendingDeposit_succeeds hst _ (hdep _ hmem)
      (by dsimp only; omega) (hst.vFits (by dsimp only; omega))) (fun _ st' h => ?_)
    obtain ⟨hst', hsz', hpd'⟩ := h
    run_succeeds
    refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, hpost, by dsimp only; omega,
      by dsimp only; omega, hpd'.trans hpd, ?_⟩
    exact hst'.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega)


omit [HasherTag] [CryptoBackend] in
/-- A `Stage` state whose deposit queue is replaced by a list of capped deposits that fits the
start's registry potential, with the slack back at `slack`. -/
theorem Stage.setPendingDeposits {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {st : BeaconState} (hst : Stage b v caps st)
    (l : SizzLean.Repr.ProgressiveList PendingDeposit) (x : Gwei) (slack : Nat)
    (hl : ∀ d ∈ l.val, d.amount.toNat ≤ b.deposit)
    (hpot : st.validators.val.size + l.val.size ≤ registryPotential v + slack) :
    Stage b v { caps with slack := slack }
      { st with pendingDeposits := l, depositBalanceToConsume := x } :=
  ⟨hst.slot, hst.registrySizes, hst.vGrows, hpot, hst.consolidationIdx, hst.consolidationCount,
    hst.effCap, hl, hst.exitBound, hst.historyBound, hst.balanceBound, hst.live, hst.liveUnslashed,
    hst.liveCount⟩

theorem processPendingDeposits_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hreg : registryPotential v + caps.slack + Const.maxPendingDepositsPerEpoch < 2 ^ 64)
    (hroom : caps.balance + Const.maxPendingDepositsPerEpoch * b.deposit < 2 ^ 64) :
    RunSucceeds w (processPendingDeposits (StateTransition := GloasRun))
      (fun _ w' => Stage b v
        { caps with balance := caps.balance + Const.maxPendingDepositsPerEpoch * b.deposit } w') := by
  unfold processPendingDeposits
  run_succeeds
  have hpotw := hw.potential
  unfold registryPotential at hpotw
  refine RunSucceeds.weaken (ppdLoop_succeeds hw _ (fun d hd => hw.depositCap d hd) hreg hroom _ _ _)
    (fun scan st h => ?_)
  obtain ⟨hndi, hmax, hpost, hple, hsz, hpd, hst⟩ := h
  have hmul : scan.ndi * b.deposit ≤ Const.maxPendingDepositsPerEpoch * b.deposit :=
    Nat.mul_le_mul_right _ hmax
  run_succeeds
  -- The leftover queue goes in whole: a progressive list has no cap to check.
  refine (hst.setPendingDeposits _ _ caps.slack ?_ ?_).mono (by dsimp only; omega) (Nat.le_refl _)
    (Nat.le_refl _)
  · intro d hd
    rcases Array.mem_append.mp hd with hd | hd
    · exact hw.depositCap d (mem_of_mem_extract_suffix hd)
    · exact hpost d hd
  · show st.validators.val.size +
      (w.pendingDeposits.val.extract scan.ndi w.pendingDeposits.val.size ++ scan.postpone).size ≤ _
    simp only [Array.size_append, Array.size_extract]
    unfold registryPotential
    omega

end

end EthCLSpecs.Proofs.Gloas
