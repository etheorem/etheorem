import EthCLSpecs.Proofs.Fulu.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Fulu.Invariants.Epoch`: the epoch substeps keep the core values

`processEpoch` (`Fulu/Transition.lean:53-68`), the spec's `process_epoch`, runs fifteen
substeps. Fourteen of them keep the six core values of `coreFields` fixed and the registry sizes
equal (`KeepsCore`): they write balances, validator records, inactivity scores, queues, mixes and
committees, overwrite list entries in place, or, in `processPendingDeposits`, append to all five
registry lists at once.
`processParticipationFlagUpdates` rebuilds both participation lists, at the registry's length.

The fifteenth, `processJustificationAndFinalization`, writes the checkpoints. Its fact is in
`Proofs/Fulu/Invariants/Justification.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
theorem processInactivityUpdates_keepsCore :
    KeepsCore (processInactivityUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processInactivityUpdates
  run_ensures
  all_goals try frame_close
  refine runEnsures_modifyThe (pureState_forIn_array_inv (StepInv c)
    (by intro _ _ _; exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem applyDeltas_keepsCore (rewards penalties : Array Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (applyDeltas (StateTransition := FuluRun) rewards penalties (pureState s))
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') := by
  unfold applyDeltas
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) s v hs).weaken ?_
  · run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    call_box decreaseBalance_keepsCore _ _
    run_ensures
    exact ⟨rfl, _, rfl, ‹_›⟩
  · intro b w hb
    run_ensures
    exact hb

omit [CryptoBackend] in
theorem processRewardsAndPenalties_keepsCore :
    KeepsCore (processRewardsAndPenalties (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processRewardsAndPenalties
  run_ensures
  all_goals try frame_close
  refine (Preserves.forIn_list _ _ (fun x _ w hw => ?_)).run (by frame_close) (fun _ w hw => ?_)
  · obtain ⟨_, _⟩ := x
    run_ensures
    call_box applyDeltas_keepsCore _ _
    run_ensures
    frame_close
  · run_ensures
    call_box applyDeltas_keepsCore _ _
    run_ensures
    frame_close

omit [CryptoBackend] in
theorem processRegistryUpdates_keepsCore :
    KeepsCore (processRegistryUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processRegistryUpdates
  run_ensures
  refine (Preserves.forIn_range _ _ (fun _ _ _ w hw => ?_)).run hv (fun _ _ h => ?_)
  · run_ensures
    all_goals try frame_close
    all_goals try (call initiateValidatorExit_keepsCore _; run_ensures)
    all_goals frame_close
  · run_ensures
    exact h

omit [Config] [CryptoBackend] in
theorem processSlashings_keepsCore :
    KeepsCore (processSlashings (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSlashings
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) v v hv).weaken ?_
  · run_ensures
    · call_box decreaseBalance_keepsCore _ _
      run_ensures
      exact ⟨rfl, _, rfl, ‹_›⟩
    · exact ⟨rfl, _, rfl, hs⟩
  · intro b w ⟨hw, s', hb, hs'⟩
    subst hw hb
    run_ensures
    exact hs'

omit [Config] [CryptoBackend] in
theorem processEth1DataReset_keepsCore :
    KeepsCore (processEth1DataReset (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processEth1DataReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  all_goals frame_close

theorem ppdLoop_keepsCore (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei)
    (nextEpoch : Epoch) :
    KeepsCore (ppdLoop (StateTransition := FuluRun) deposits finalizedSlot avail nextEpoch) := by
  intro c
  unfold ppdLoop
  refine Preserves.fuelLoop _ _ _ (fun _ w hw => ?_)
  run_ensures
  all_goals try frame_close
  all_goals try (split <;> run_ensures)
  all_goals try frame_close
  all_goals (call applyPendingDeposit_keepsCore _; run_ensures; frame_close)

theorem processPendingDeposits_keepsCore :
    KeepsCore (processPendingDeposits (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processPendingDeposits
  run_ensures
  call ppdLoop_keepsCore _ _ _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem pcLoop_keepsCore (cons : Array PendingConsolidation) (nextEpoch : Epoch) :
    KeepsCore (pcLoop (StateTransition := FuluRun) cons nextEpoch) := by
  intro c
  unfold pcLoop
  refine Preserves.fuelLoop _ _ _ (fun _ w hw => ?_)
  run_ensures
  all_goals try frame_close
  call_box decreaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processPendingConsolidations_keepsCore :
    KeepsCore (processPendingConsolidations (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processPendingConsolidations
  run_ensures
  call pcLoop_keepsCore _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEffectiveBalanceUpdates_keepsCore :
    KeepsCore (processEffectiveBalanceUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processEffectiveBalanceUpdates
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem processSlashingsReset_keepsCore :
    KeepsCore (processSlashingsReset (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSlashingsReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processRandaoMixesReset_keepsCore :
    KeepsCore (processRandaoMixesReset (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processRandaoMixesReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  call_ro getRandaoMix_readsOnly _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processHistoricalSummariesUpdate_keepsCore :
    KeepsCore (processHistoricalSummariesUpdate (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processHistoricalSummariesUpdate
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  all_goals try frame_close
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
/-- The rotation writes `previous := current` and a fresh all-zero `current` of the registry's
length, so both participation lists still have that length. -/
theorem processParticipationFlagUpdates_keepsCore :
    KeepsCore (processParticipationFlagUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processParticipationFlagUpdates
  run_ensures
  rename_i l hl
  obtain ⟨hc, hb, hi, hp, hq⟩ := hv
  refine ⟨by rw [← hc]; rfl, ?_⟩
  simp only [RegistrySizes, SizzLean.Repr.SSZList.size, box_reduce]
  simp only [SizzLean.Repr.SSZList.size] at hb hi hp hq
  refine ⟨hb, hi, hq, ?_⟩
  rw [hl]
  simp

omit [Config] in
theorem processSyncCommitteeUpdates_keepsCore :
    KeepsCore (processSyncCommitteeUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSyncCommitteeUpdates
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem processProposerLookahead_keepsCore :
    KeepsCore (processProposerLookahead (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processProposerLookahead
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Fulu
