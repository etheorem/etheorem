import EthCLSpecs.Proofs.Gloas.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Gloas.Invariants.Block`: the block substeps keep the core values

The Gloas counterpart of `Proofs/Fulu/Invariants/Block.lean`. `processBlock`
(`Gloas/Transition.lean:107-116`), the spec's `process_block` under EIP-7732, runs eight substeps.
Seven keep the six core values of `coreFields` fixed and the registry sizes equal (`KeepsCore`):

* the parent payload's application, which settles builder payments and runs the execution
  requests the parent block's payload carried;
* the withdrawals, which now also sweep builders and write the payload commitment;
* the execution payload bid, RANDAO, the eth1 vote, the operations, and the sync aggregate.

None of them appends to the registry. The builder registry is a separate list, which no
invariant reads. The eighth, `processBlockHeader`, is the header step of
`Proofs/Gloas/ReachableInvariants.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Gloas

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## Withdrawals -/

omit [Config] [CryptoBackend] in
theorem balanceAfterWithdrawals_readsOnly (s : BeaconState) (vi : ValidatorIndex)
    (ws : Array Withdrawal) :
    ReadsOnly (balanceAfterWithdrawals (StateTransition := GloasRun) (pureState s) vi ws) := by
  intro v
  unfold balanceAfterWithdrawals
  run_ensures
  refine (runEnsures_foldlM_array_inv (fun _ w => w = v) (fun _ _ w hw => ?_) _ _ rfl).weaken
    (fun _ w hw => ?_)
  · subst hw; run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getBuilderBalanceAfterWithdrawals_readsOnly (s : BeaconState) (bi : BuilderIndex)
    (ws : Array Withdrawal) :
    ReadsOnly (getBuilderBalanceAfterWithdrawals (StateTransition := GloasRun) (pureState s)
      bi ws) := by
  intro v
  unfold getBuilderBalanceAfterWithdrawals
  run_ensures
  refine (runEnsures_foldlM_array_inv (fun _ w => w = v) (fun _ _ w hw => ?_) _ _ rfl).weaken
    (fun _ w hw => ?_)
  · subst hw; run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getBuilderWithdrawals_readsOnly (wi : WithdrawalIndex) (prior : Array Withdrawal) :
    ReadsOnly (getBuilderWithdrawals (StateTransition := GloasRun) wi prior) := by
  intro v
  unfold getBuilderWithdrawals
  run_ensures
  refine (Preserves.forIn_array (P := fun w => w = v) _ _ (fun _ _ w hw => ?_)).run rfl
    (fun _ w hw => ?_)
  · subst hw; run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getPendingPartialWithdrawals_readsOnly (wi : WithdrawalIndex) (prior : Array Withdrawal) :
    ReadsOnly (getPendingPartialWithdrawals (StateTransition := GloasRun) wi prior) := by
  intro v
  unfold getPendingPartialWithdrawals
  run_ensures
  refine (Preserves.forIn_array (P := fun w => w = v) _ _ (fun _ _ w hw => ?_)).run rfl
    (fun _ w hw => ?_)
  · subst hw
    run_ensures
    all_goals try rfl
    refine (balanceAfterWithdrawals_readsOnly _ _ _ w).weaken fun _ w' hw' => ?_
    subst hw'
    run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getBuildersSweepWithdrawals_readsOnly (wi : WithdrawalIndex) (prior : Array Withdrawal) :
    ReadsOnly (getBuildersSweepWithdrawals (StateTransition := GloasRun) wi prior) := by
  intro v
  unfold getBuildersSweepWithdrawals
  run_ensures
  refine (Preserves.forIn_range (P := fun w => w = v) _ _ (fun _ _ _ w hw => ?_)).run rfl
    (fun _ w hw => ?_)
  · subst hw
    run_ensures
    all_goals try rfl
    refine (getBuilderBalanceAfterWithdrawals_readsOnly _ _ _ w).weaken fun _ w' hw' => ?_
    subst hw'
    run_ensures
  · subst hw; run_ensures

omit [Config] [CryptoBackend] in
theorem getValidatorsSweepWithdrawals_readsOnly (wi : WithdrawalIndex) (prior : Array Withdrawal) :
    ReadsOnly (getValidatorsSweepWithdrawals (StateTransition := GloasRun) wi prior) := by
  intro v
  unfold getValidatorsSweepWithdrawals
  run_ensures
  refine (Preserves.forIn_range (P := fun w => w = v) _ _ (fun _ _ _ w hw => ?_)).run rfl
    (fun _ w hw => ?_)
  · subst hw
    run_ensures
    all_goals try rfl
    refine (balanceAfterWithdrawals_readsOnly _ _ _ w).weaken fun _ w' hw' => ?_
    subst hw'
    run_ensures
  · subst hw; run_ensures

/-- Step over a read-only call with any postcondition: the state after it is the state
before it. -/
local macro "call_reads " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h _) (fun _ _ hro => ?_); subst hro))

omit [Config] [CryptoBackend] in
theorem getExpectedWithdrawals_readsOnly :
    ReadsOnly (getExpectedWithdrawals (StateTransition := GloasRun)) := by
  intro v
  unfold getExpectedWithdrawals
  run_ensures
  call_reads getBuilderWithdrawals_readsOnly _ _
  run_ensures
  call_reads getPendingPartialWithdrawals_readsOnly _ _
  run_ensures
  call_reads getBuildersSweepWithdrawals_readsOnly _ _
  run_ensures
  call_reads getValidatorsSweepWithdrawals_readsOnly _ _
  run_ensures

omit [Config] [CryptoBackend] in
theorem applyWithdrawals_keepsCore (ws : Array Withdrawal) :
    KeepsCore (applyWithdrawals (StateTransition := GloasRun) ws) := by
  intro c v hv
  unfold applyWithdrawals
  run_ensures
  refine (runEnsures_forIn_array_box (StepInv c) _ (fun _ s w hs => ?_) v _ hv).weaken
    (fun b w hb => ?_)
  · run_ensures
    · exact ⟨rfl, _, rfl, by frame_close⟩
    · call_box decreaseBalance_keepsCore _ _
      run_ensures
      exact ⟨rfl, _, rfl, ‹_›⟩
  · obtain ⟨hw, s', hb, hs'⟩ := hb
    subst hw hb
    run_ensures
    exact hs'

omit [Config] [CryptoBackend] in
theorem processWithdrawals_keepsCore :
    KeepsCore (processWithdrawals (StateTransition := GloasRun)) := by
  intro c v hv
  unfold processWithdrawals
  run_ensures
  all_goals try frame_close
  call_ro getExpectedWithdrawals_readsOnly
  run_ensures
  call applyWithdrawals_keepsCore _
  run_ensures
  all_goals write_split
  all_goals run_ensures
  all_goals frame_close

/-! ## The bid, the parent payload, and the builder requests -/

omit [Config] [CryptoBackend] in
theorem settleBuilderPayment_keepsCore (i : Nat) :
    KeepsCore (settleBuilderPayment (StateTransition := GloasRun) i) := by
  intro c v hv
  unfold settleBuilderPayment
  run_ensures
  all_goals frame_close

theorem processExecutionPayloadBid_keepsCore (sb : SignedExecutionPayloadBid) :
    KeepsCore (processExecutionPayloadBid (StateTransition := GloasRun) sb) := by
  intro c v hv
  unfold processExecutionPayloadBid
  run_ensures
  all_goals (call_ro getBlockRootAtSlot_readsOnly _ _; run_ensures)
  all_goals (call_ro getRandaoMix_readsOnly _; run_ensures)
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateBuilderExit_keepsCore (bi : BuilderIndex) :
    KeepsCore (initiateBuilderExit (StateTransition := GloasRun) bi) := by
  intro c v hv
  unfold initiateBuilderExit
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem addBuilderToRegistry_keepsCore (pk : BLSPubkey) (ver : UInt8) (addr : ExecutionAddress)
    (amt : Gwei) (slot : Slot) :
    KeepsCore (addBuilderToRegistry (StateTransition := GloasRun) pk ver addr amt slot) := by
  intro c v hv
  unfold addBuilderToRegistry
  run_ensures
  all_goals frame_close

theorem processBuilderDepositRequest_keepsCore (r : BuilderDepositRequest) :
    KeepsCore (processBuilderDepositRequest (StateTransition := GloasRun) r) := by
  intro c v hv
  unfold processBuilderDepositRequest
  run_ensures
  all_goals try frame_close
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call addBuilderToRegistry_keepsCore _ _ _ _ _; run_ensures)
  all_goals frame_close

omit [CryptoBackend] in
theorem processBuilderExitRequest_keepsCore (r : BuilderExitRequest) :
    KeepsCore (processBuilderExitRequest (StateTransition := GloasRun) r) := by
  intro c v hv
  unfold processBuilderExitRequest
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call initiateBuilderExit_keepsCore _; run_ensures)
  all_goals frame_close

/-! ## The execution requests and the parent payload -/

omit [Config] [CryptoBackend] in
theorem processDepositRequest_keepsCore (dr : DepositRequest) :
    KeepsCore (processDepositRequest (StateTransition := GloasRun) dr) := by
  intro c v hv
  unfold processDepositRequest
  run_ensures
  frame_close

omit [CryptoBackend] in
theorem processWithdrawalRequest_keepsCore (wr : WithdrawalRequest) :
    KeepsCore (processWithdrawalRequest (StateTransition := GloasRun) wr) := by
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
  frame_close

omit [CryptoBackend] in
theorem processConsolidationRequest_keepsCore (req : ConsolidationRequest) :
    KeepsCore (processConsolidationRequest (StateTransition := GloasRun) req) := by
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
  frame_close

theorem applyParentExecutionPayload_keepsCore (requests : ExecutionRequests) :
    KeepsCore (applyParentExecutionPayload (StateTransition := GloasRun) requests) := by
  intro c v hv
  unfold applyParentExecutionPayload
  run_ensures
  all_goals try (call settleBuilderPayment_keepsCore _; run_ensures)
  all_goals
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run (by frame_close) (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processDepositRequest_keepsCore _; run_ensures; frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processWithdrawalRequest_keepsCore _; run_ensures; frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processConsolidationRequest_keepsCore _; run_ensures
      frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processBuilderDepositRequest_keepsCore _; run_ensures
      frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processBuilderExitRequest_keepsCore _; run_ensures
      frame_close
    run_ensures
    frame_close

theorem processParentExecutionPayload_keepsCore (block : BeaconBlock) :
    KeepsCore (processParentExecutionPayload (StateTransition := GloasRun) block) := by
  intro c v hv
  unfold processParentExecutionPayload
  run_ensures
  all_goals try frame_close
  call applyParentExecutionPayload_keepsCore _
  frame_close

/-! ## Attestations and payload attestations -/

omit [Config] [CryptoBackend] in
theorem isAttestationSameSlot_readsOnly (s : BeaconState) (data : AttestationData) :
    ReadsOnly (isAttestationSameSlot (StateTransition := GloasRun) (pureState s) data) := by
  intro v
  unfold isAttestationSameSlot
  run_ensures
  all_goals try rfl
  call_reads getBlockRootAtSlot_readsOnly _ _
  run_ensures
  call_reads getBlockRootAtSlot_readsOnly _ _
  run_ensures

omit [Config] [CryptoBackend] in
theorem getAttestationParticipationFlagIndices_readsOnly (s : BeaconState) (data : AttestationData)
    (delay : UInt64) (parentSlot : Slot) :
    ReadsOnly (getAttestationParticipationFlagIndices (StateTransition := GloasRun) (pureState s)
      data delay parentSlot) := by
  intro v
  unfold getAttestationParticipationFlagIndices
  run_ensures
  all_goals try rfl
  call_reads getBlockRoot_readsOnly _ _
  run_ensures
  call_reads isAttestationSameSlot_readsOnly _ _
  run_ensures
  all_goals try rfl
  call_reads getBlockRootAtSlot_readsOnly _ _
  run_ensures

omit [CryptoBackend] in
theorem getPtc_readsOnly (s : BeaconState) (slot : Slot) :
    ReadsOnly (getPtc (StateTransition := GloasRun) (pureState s) slot) := by
  intro v
  unfold getPtc
  run_ensures

omit [CryptoBackend] in
theorem getIndexedPayloadAttestation_readsOnly (s : BeaconState) (pa : PayloadAttestation) :
    ReadsOnly (getIndexedPayloadAttestation (StateTransition := GloasRun) (pureState s) pa) := by
  intro v
  unfold getIndexedPayloadAttestation
  run_ensures
  call_reads getPtc_readsOnly _ _
  run_ensures

theorem processPayloadAttestation_keepsCore (pa : PayloadAttestation) :
    KeepsCore (processPayloadAttestation (StateTransition := GloasRun) pa) := by
  intro c v hv
  unfold processPayloadAttestation
  run_ensures
  call_ro getIndexedPayloadAttestation_readsOnly _ _
  run_ensures
  frame_close

omit [Config] in
theorem processAttestation_keepsCore (att : Attestation) (parentSlot : Slot) :
    KeepsCore (processAttestation (StateTransition := GloasRun) att parentSlot) := by
  intro c v hv
  unfold processAttestation
  run_ensures
  call_ro getAttestationParticipationFlagIndices_readsOnly _ _ _ _
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  call_ro isAttestationSameSlot_readsOnly _ _
  run_ensures
  refine (runEnsures_forIn_array_boxFst (StepInv c) _ (fun _ s n w hs => ?_) v _ _ hv).weaken
    (fun acc w hacc => ?_)
  · run_ensures
    all_goals refine (runEnsures_forIn_range_boxFst (StepInv c) 3
      (fun _ s' n' w' _ hs' => ?_) s w _ hs).weaken (fun acc' w' hacc' => ?_)
    all_goals first
      | (obtain ⟨b', n''⟩ := acc'
         obtain ⟨hw', s'', hb', hs''⟩ := hacc'
         try simp only at hb'
         subst hw' hb'
         run_ensures
         all_goals exact ⟨rfl, _, rfl, hs''⟩)
      | (run_ensures
         all_goals first
           | exact ⟨rfl, _, rfl, hs'⟩
           | (refine ⟨rfl, ?_⟩
              split_ite
              all_goals first
                | (exfalso; contradiction)
                | exact ⟨_, rfl, by frame_close⟩))
  · obtain ⟨b, n⟩ := acc
    obtain ⟨hw, s', hb, hs'⟩ := hacc
    try simp only at hb
    subst hw hb
    run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    frame_close

/-! ## RANDAO, the eth1 vote, the sync aggregate, and the inherited operations -/

omit [Config] in
theorem processRandao_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processRandao (StateTransition := GloasRun) body) := by
  intro c v hv
  unfold processRandao
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEth1Data_keepsCore (body : BeaconBlockBody) :
    KeepsCore (processEth1Data (StateTransition := GloasRun) body) := by
  intro c v hv
  unfold processEth1Data
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] in
theorem processSyncAggregate_keepsCore (agg : SyncAggregate) :
    KeepsCore (processSyncAggregate (StateTransition := GloasRun) agg) := by
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

theorem processProposerSlashing_keepsCore (ps : ProposerSlashing) :
    KeepsCore (processProposerSlashing (StateTransition := GloasRun) ps) := by
  intro c v hv
  unfold processProposerSlashing
  run_ensures
  call slashValidator_keepsCore _
  frame_close

theorem processAttesterSlashing_keepsCore (asl : AttesterSlashing) :
    KeepsCore (processAttesterSlashing (StateTransition := GloasRun) asl) := by
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
    KeepsCore (processVoluntaryExit (StateTransition := GloasRun) sve) := by
  intro c v hv
  unfold processVoluntaryExit
  run_ensures
  call initiateValidatorExit_keepsCore _
  frame_close

theorem processBlsToExecutionChange_keepsCore (sbc : SignedBLSToExecutionChange) :
    KeepsCore (processBlsToExecutionChange (StateTransition := GloasRun) sbc) := by
  intro c v hv
  unfold processBlsToExecutionChange
  run_ensures
  frame_close

theorem processOperations_keepsCore (body : BeaconBlockBody) (parentSlot : Slot) :
    KeepsCore (processOperations (StateTransition := GloasRun) body parentSlot) := by
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
  · intro w hw; run_ensures; call processAttestation_keepsCore _ _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processVoluntaryExit_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processBlsToExecutionChange_keepsCore _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processPayloadAttestation_keepsCore _; run_ensures; frame_close
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Gloas
