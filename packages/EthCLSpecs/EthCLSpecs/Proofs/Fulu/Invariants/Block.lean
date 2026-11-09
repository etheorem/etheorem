import EthCLSpecs.Proofs.Fulu.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Fulu.Invariants.Block`: the block substeps keep the core values

`processBlock` (`Fulu/Transition.lean:207-214`), the spec's `process_block`, runs seven
substeps. Six keep the six core values of `coreFields` fixed and the registry sizes equal
(`KeepsCore`): the withdrawals, the execution payload, RANDAO, the eth1 vote, the operations, and
the sync aggregate write balances, validator records, queues, mixes and the payload header, and
none of them appends to the registry.

The seventh, `processBlockHeader`, runs first and writes the latest block header. Its slot is the
block's slot, which the step asserts equals the state's. So the header slot stays at most the state
slot, and every other invariant is untouched (`processBlockHeader_ensures`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## Withdrawals -/

omit [Config] [CryptoBackend] in
theorem balanceAfterWithdrawals_readsOnly (s : BeaconState) (vi : ValidatorIndex)
    (ws : Array Withdrawal) :
    ReadsOnly (balanceAfterWithdrawals (StateTransition := FuluRun) (pureState s) vi ws) := by
  intro v
  unfold balanceAfterWithdrawals
  run_ensures
  refine (runEnsures_foldlM_array_inv (fun _ w => w = v) (fun _ _ w hw => ?_) _ _ rfl).weaken
    (fun _ w hw => ?_)
  · subst hw; run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getExpectedWithdrawals_readsOnly (s : BeaconState) :
    ReadsOnly (getExpectedWithdrawals (StateTransition := FuluRun) (pureState s)) := by
  intro v
  unfold getExpectedWithdrawals
  run_ensures
  refine (Preserves.forIn_array (P := fun w => w = v) _ _ (fun _ _ w hw => ?_)).run rfl
    (fun _ w hw => ?_)
  · subst hw
    run_ensures
    all_goals try rfl
    refine (balanceAfterWithdrawals_readsOnly _ _ _ w).weaken fun _ w' hw' => ?_
    subst hw'
    run_ensures
  · subst hw
    run_ensures
    refine (Preserves.forIn_range (P := fun w' => w' = w) _ _ (fun _ _ _ w' hw' => ?_)).run rfl
      (fun _ w' hw' => ?_)
    · subst hw'
      run_ensures
      all_goals try rfl
      refine (balanceAfterWithdrawals_readsOnly _ _ _ w').weaken fun _ w'' hw'' => ?_
      subst hw''
      run_ensures
    · subst hw'
      run_ensures

omit [Config] [CryptoBackend] in
theorem processWithdrawals_keepsCore (payload : ExecutionPayload) :
    KeepsCore (processWithdrawals (StateTransition := FuluRun) payload) := by
  intro c v hv
  unfold processWithdrawals
  run_ensures
  call_ro getExpectedWithdrawals_readsOnly _
  run_ensures
  refine (runEnsures_forIn_array_box (StepInv c) _ (fun _ s w hs => ?_) v _ hv).weaken
    (fun b w hb => ?_)
  · run_ensures
    call_box decreaseBalance_keepsCore _ _
    run_ensures
    exact ⟨rfl, _, rfl, ‹_›⟩
  · obtain ⟨hw, s', hb, hs'⟩ := hb
    subst hw hb
    run_ensures
    all_goals frame_close

/-! ## Payload, RANDAO, eth1 vote, sync aggregate -/

omit [CryptoBackend] in
theorem processExecutionPayload_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processExecutionPayload (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processExecutionPayload
  run_ensures
  frame_close

omit [Config] in
theorem processRandao_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processRandao (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processRandao
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEth1Data_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processEth1Data (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processEth1Data
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] in
theorem processSyncAggregate_keepsCore (agg : SyncAggregate) :
    KeepsCore (processSyncAggregate (StateTransition := FuluRun) agg) := by
  intro c v hv
  unfold processSyncAggregate
  run_ensures
  call_ro getBlockRootAtSlot_readsOnly _ _
  run_ensures
  refine (runEnsures_forIn'_range_inv _ (BoxInv (StepInv c) _)
    (fun _ _ b w hb => ?_) _ ⟨rfl, v, rfl, hv⟩).weaken (fun b w hb => ?_)
  · obtain ⟨hw, s, hb, hs⟩ := hb
    subst hw hb
    run_ensures
    run_ensures_beta
    split
    · run_ensures
      · call_box increaseBalance_keepsCore _ _
        run_ensures
        call_box increaseBalance_keepsCore _ _
        run_ensures
        exact ⟨rfl, _, rfl, ‹_›⟩
      · call_box decreaseBalance_keepsCore _ _
        run_ensures
        exact ⟨rfl, _, rfl, ‹_›⟩
    · run_ensures
      exact ⟨rfl, _, rfl, hs⟩
  · obtain ⟨hw, s, hb, hs⟩ := hb
    subst hw hb
    run_ensures
    exact hs

/-! ## Operations -/

omit [Config] [CryptoBackend] in
theorem getAttestationParticipationFlagIndices_readsOnly (s : BeaconState) (data : AttestationData)
    (delay : UInt64) :
    ReadsOnly (getAttestationParticipationFlagIndices (StateTransition := FuluRun) (pureState s)
      data delay) := by
  intro v
  unfold getAttestationParticipationFlagIndices
  run_ensures
  all_goals try rfl
  refine (getBlockRoot_readsOnly _ _ v).weaken fun _ w hw => ?_
  subst hw
  run_ensures
  refine (getBlockRootAtSlot_readsOnly _ _ w).weaken fun _ w' hw' => ?_
  subst hw'
  run_ensures

omit [Config] in
theorem processAttestation_keepsCore (att : Attestation) :
    KeepsCore (processAttestation (StateTransition := FuluRun) att) := by
  intro c v hv
  unfold processAttestation
  run_ensures
  call_ro getAttestationParticipationFlagIndices_readsOnly _ _ _
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  refine (runEnsures_forIn_array_boxFst (StepInv c) _ (fun _ s n w hs => ?_) v _ 0 hv).weaken
    (fun acc w hacc => ?_)
  · run_ensures
    refine (runEnsures_forIn_range_boxFst (StepInv c) 3 (fun _ s' n' w' _ hs' => ?_) s w n hs).weaken
      (fun acc' w' hacc' => ?_)
    · run_ensures
      all_goals first
        | exact ⟨rfl, _, rfl, hs'⟩
        | (refine ⟨rfl, ?_⟩
           split_ite
           all_goals first
             | (exfalso; contradiction)
             | exact ⟨_, rfl, by frame_close⟩)
    · obtain ⟨b', n''⟩ := acc'
      obtain ⟨hw', s'', hb', hs''⟩ := hacc'
      try simp only at hb'
      subst hw' hb'
      run_ensures
      exact ⟨rfl, _, rfl, hs''⟩
  · obtain ⟨b, n⟩ := acc
    obtain ⟨hw, s', hb, hs'⟩ := hacc
    try simp only at hb
    subst hw hb
    run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    frame_close

theorem processProposerSlashing_keepsCore (ps : ProposerSlashing) :
    KeepsCore (processProposerSlashing (StateTransition := FuluRun) ps) := by
  intro c v hv
  unfold processProposerSlashing
  run_ensures
  call slashValidator_keepsCore _
  frame_close

theorem processAttesterSlashing_keepsCore (asl : AttesterSlashing) :
    KeepsCore (processAttesterSlashing (StateTransition := FuluRun) asl) := by
  intro c v hv
  unfold processAttesterSlashing
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ w hw => ?_)).run hv (fun _ w hw => ?_)
  · run_ensures
    · call slashValidator_keepsCore _
      run_ensures
      frame_close
    · frame_close
  · run_ensures
    frame_close

theorem processVoluntaryExit_keepsCore (sve : SignedVoluntaryExit) :
    KeepsCore (processVoluntaryExit (StateTransition := FuluRun) sve) := by
  intro c v hv
  unfold processVoluntaryExit
  run_ensures
  call initiateValidatorExit_keepsCore _
  frame_close

theorem processBlsToExecutionChange_keepsCore (sbc : SignedBLSToExecutionChange) :
    KeepsCore (processBlsToExecutionChange (StateTransition := FuluRun) sbc) := by
  intro c v hv
  unfold processBlsToExecutionChange
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processDepositRequest_keepsCore (dr : DepositRequest) :
    KeepsCore (processDepositRequest (StateTransition := FuluRun) dr) := by
  intro c v hv
  unfold processDepositRequest
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem processWithdrawalRequest_keepsCore (wr : WithdrawalRequest) :
    KeepsCore (processWithdrawalRequest (StateTransition := FuluRun) wr) := by
  intro c v hv
  unfold processWithdrawalRequest
  run_ensures
  all_goals try frame_close
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try frame_close
  all_goals try (call initiateValidatorExit_keepsCore _; run_ensures; frame_close)
  call computeExitEpochAndUpdateChurn_keepsCore _
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem processConsolidationRequest_keepsCore (req : ConsolidationRequest) :
    KeepsCore (processConsolidationRequest (StateTransition := FuluRun) req) := by
  intro c v hv
  unfold processConsolidationRequest
  run_ensures
  all_goals try frame_close
  all_goals (run_ensures_beta; split)
  all_goals run_ensures
  all_goals try frame_close
  all_goals try (call switchToCompoundingValidator_keepsCore _; run_ensures; frame_close)
  call computeConsolidationEpochAndUpdateChurn_keepsCore _
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

theorem processOperations_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processOperations (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processOperations
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hv (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processProposerSlashing_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttesterSlashing_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttestation_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processVoluntaryExit_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processBlsToExecutionChange_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processDepositRequest_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processWithdrawalRequest_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processConsolidationRequest_keepsCore _; run_ensures; frame_close
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Fulu
