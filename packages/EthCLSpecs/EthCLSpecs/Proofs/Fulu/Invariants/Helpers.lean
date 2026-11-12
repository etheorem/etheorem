import EthCLSpecs.Proofs.Fulu.StateInvariants
import EthCLSpecs.Fulu.Transition

/-!
# `EthCLSpecs.Proofs.Fulu.Invariants.Helpers`: the shared mutators keep the core values

The epoch and block steps reach the state through a small set of shared mutators: the
balance writes, the validator-record write, the churn accounting, exits, slashing, the
compounding switch, and the registry append. This module proves that each keeps the six core
values of `coreFields` fixed and the registry sizes equal (`KeepsCore`), or, for the
mutators that write a box handed to them, that the box they return agrees with the one they
were handed on those values (`FrameEq`). The read-only accessors get `ReadsOnly`.

`addValidatorToRegistry` is the one mutator that changes a list size. It appends to all five
lists at the index `len(validators)`, and on a state whose sizes agree each write takes the
append branch of `set_or_append_list`, so the sizes still agree afterwards.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

/-! ## Box-returning balance writes -/

/-- `increaseBalance` writes only the box it is handed: the threaded state stays, and the
returned box is the uncached box of a value that agrees with the input on the core values and
list sizes. -/
theorem increaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (increaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold increaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- `decreaseBalance` writes only the box it is handed, as `increaseBalance` does. -/
theorem decreaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (decreaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold decreaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- A box write that keeps `FrameEq` carries `StepInv` from the handed value to the returned
one: the form `call_box` reads. -/
theorem stepInv_of_box_ensures {act : FuluRun State} {s v : BeaconState} {c : CoreFields}
    (h : RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s))
    (hs : StepInv c s) :
    RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  h.weaken fun _ _ ⟨hw, s', hb, hf⟩ => ⟨hw, s', hb, hs.of_frameEq hf⟩

theorem increaseBalance_keepsCore (i : ValidatorIndex) (d : Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (increaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (increaseBalance_ensures s v i d) hs

theorem decreaseBalance_keepsCore (i : ValidatorIndex) (d : Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (decreaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (decreaseBalance_ensures s v i d) hs

/-! ## Read-only accessors -/

theorem getBlockRootAtSlot_readsOnly (s : BeaconState) (sl : Slot) :
    ReadsOnly (getBlockRootAtSlot (StateTransition := FuluRun) (pureState s) sl) := by
  intro v
  unfold getBlockRootAtSlot
  run_ensures
  all_goals rfl

theorem getBlockRoot_readsOnly (s : BeaconState) (e : Epoch) :
    ReadsOnly (getBlockRoot (StateTransition := FuluRun) (pureState s) e) :=
  getBlockRootAtSlot_readsOnly s _

theorem getRandaoMix_readsOnly (e : Epoch) :
    ReadsOnly (getRandaoMix (StateTransition := FuluRun) e) := by
  intro v
  unfold getRandaoMix
  run_ensures

theorem getCurrentEpoch_readsOnly : ReadsOnly (getCurrentEpoch (StateTransition := FuluRun)) := by
  intro v
  unfold getCurrentEpoch
  run_ensures

variable [Config] [CryptoBackend]

/-! ## Churn accounting and the validator-lifecycle mutators -/

omit [CryptoBackend] in
theorem computeExitEpochAndUpdateChurn_keepsCore (b : Gwei) :
    KeepsCore (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) b) := by
  intro c v hv
  unfold computeExitEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem computeConsolidationEpochAndUpdateChurn_keepsCore (b : Gwei) :
    KeepsCore (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) b) := by
  intro c v hv
  unfold computeConsolidationEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateValidatorExit_keepsCore (i : ValidatorIndex) :
    KeepsCore (initiateValidatorExit (StateTransition := FuluRun) i) := by
  intro c v hv
  unfold initiateValidatorExit
  run_ensures
  all_goals try frame_close
  call computeExitEpochAndUpdateChurn_keepsCore _
  run_ensures
  frame_close

omit [CryptoBackend] in
theorem slashValidator_keepsCore (i : ValidatorIndex) :
    KeepsCore (slashValidator (StateTransition := FuluRun) i) := by
  intro c v hv
  unfold slashValidator
  run_ensures
  call initiateValidatorExit_keepsCore _
  run_ensures
  call_box decreaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  frame_close

/-! ## Compounding and the registry append -/

omit [Config] [CryptoBackend] in
theorem queueExcessActiveBalance_keepsCore (i : ValidatorIndex) :
    KeepsCore (queueExcessActiveBalance (StateTransition := FuluRun) i) := by
  intro c v hv
  unfold queueExcessActiveBalance
  run_ensures
  all_goals try frame_close
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem switchToCompoundingValidator_keepsCore (i : ValidatorIndex) :
    KeepsCore (switchToCompoundingValidator (StateTransition := FuluRun) i) := by
  intro c v hv
  unfold switchToCompoundingValidator
  run_ensures
  call queueExcessActiveBalance_keepsCore _
  run_ensures
  frame_close

section RegistryAppend

/-- Inside this section the walk's `if` rule refutes a branch guard against every hypothesis.
`set_or_append_list` compares the new index with each list's length, and the registry-size
equalities in the context rule out its overwrite and reject branches. -/
local macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| (with_reducible refine runEnsures_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [*, box_reduce] at hc; done))

omit [Config] [CryptoBackend] in
/-- The one mutator that changes the list sizes. On a state whose registry sizes agree, each
`set_or_append_list` at `len(validators)` takes its append branch, so all five lists grow by
one together. The other branches contradict the size equalities. -/
theorem addValidatorToRegistry_keepsCore (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei) :
    KeepsCore (addValidatorToRegistry (StateTransition := FuluRun) pk wc amt) := by
  intro c v hv
  obtain ⟨hcore, hb, hi, hp, hq⟩ := hv
  simp only [SizzLean.Repr.SSZList.size] at hb hi hp hq
  unfold addValidatorToRegistry
  run_ensures
  iterate 5 (all_goals (try (append_split <;> run_ensures)))
  refine ⟨by rw [← hcore]; rfl, ?_⟩
  simp only [RegistrySizes, SizzLean.Repr.SSZList.size, box_reduce]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end RegistryAppend

theorem applyPendingDeposit_keepsCore (d : PendingDeposit) :
    KeepsCore (applyPendingDeposit (StateTransition := FuluRun) d) := by
  intro c v hv
  unfold applyPendingDeposit
  run_ensures
  split
  · run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    frame_close
  · run_ensures
    · call addValidatorToRegistry_keepsCore _ _ _
      frame_close
    · frame_close

end

end EthCLSpecs.Proofs.Fulu
