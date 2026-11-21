import EthCLSpecs.Proofs.Heze.CommitteeFrame

/-!
# `EthCLSpecs.Proofs.Heze.StakeFrame`: a block keeps the stake of each validator

The target test of an epoch weighs effective balances of validators active at that epoch
against the total active balance. A block changes neither of the two inputs:

- No block function writes an effective balance. Only the epoch step does
  (`process_effective_balance_updates`, `process_pending_deposits`). A slashing, an exit, a
  switch to compounding credentials, and a credential change write one validator through
  `modValidator`, and each such write keeps the effective balance. `ebView` holds the effective
  balance of each validator, and each block function keeps it (`processBlock_frame_eb`).
- An exit sets an exit epoch after the current epoch, so each validator keeps its activity at
  the current and the previous epoch. `CommitteeFrame.lean` proves this for the functions
  before and inside the attestation loop. This file adds the functions after the loop, so
  `processBlock` keeps `comView` of an epoch of the window (`processBlock_frame_com`).

A slot step that does not end an epoch writes the roots and the slot only. So it keeps the
registry, and with it both views (`SlotStep.validators_of_not_boundary`).

`frame_invert` proves a frame lemma for each function that writes the state, as in
`KeyFrame.lean`. A function that only reads the state needs no lemma here. Its lemma in
`PaymentFrame.lean` applies to each view.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState pureState_inj run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState ValidatorIndex Validator Gwei Epoch)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

section
variable [Preset] [HasherTag]

/-! ## The view -/

/-- The effective balance of each validator of the registry. -/
def ebView (st : State) := (sszGet st validators).val.map (·.effectiveBalance)

/-- A write at index `j` keeps `ebView` when the new validator has the effective balance of
the old validator at `j`. -/
theorem ebView_setValidator (a : BeaconState) (j : Nat) (v' : Validator)
    (hv : v'.effectiveBalance = a.validators[j]!.effectiveBalance) :
    ebView (pureState { a with validators := a.validators.set! j v' }) =
      ebView (pureState a) := by
  show (a.validators.val.setIfInBounds j v').map (fun x => x.effectiveBalance) =
    a.validators.val.map (fun x => x.effectiveBalance)
  rw [Array.map_setIfInBounds]
  apply Array.ext_getElem?
  intro k
  rw [Array.getElem?_setIfInBounds]
  split
  · rename_i hk
    subst hk
    split
    · rename_i hb
      rw [Array.size_map] at hb
      rw [hv, getElem!_pos a.validators j hb, Array.getElem?_map, Array.getElem?_eq_getElem hb]
      rfl
    · rename_i hb
      exact (Array.getElem?_eq_none (Nat.le_of_not_lt hb)).symm
  · rfl

/-- A write of one validator that keeps its effective balance keeps `ebView`. Each record
update of a validator in the block functions has this form. -/
@[frame_close] theorem ebView_modValidator {acc : BeaconState} {i : ValidatorIndex}
    {pk : Validator → EthCLSpecs.Heze.BLSPubkey} {wc : Validator → EthCLSpecs.Heze.Bytes32}
    {sl : Validator → Bool} {aee ae ee we : Validator → Epoch} {v : _}
    (hacc : ebView (pureState acc) = v) :
    ebView (EthCLSpecs.Heze.modValidator (pureState acc) i fun w =>
      { pubkey := pk w, withdrawalCredentials := wc w, effectiveBalance := w.effectiveBalance,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := ae w,
        exitEpoch := ee w, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidator_pureState]
  exact ebView_setValidator acc _ _ rfl

/-- `ebView_modValidator` for a write at a list position (`modValidatorAt`). -/
@[frame_close] theorem ebView_modValidatorAt {acc : BeaconState} {i : Nat}
    {pk : Validator → EthCLSpecs.Heze.BLSPubkey} {wc : Validator → EthCLSpecs.Heze.Bytes32}
    {sl : Validator → Bool} {aee ae ee we : Validator → Epoch} {v : _}
    (hacc : ebView (pureState acc) = v) :
    ebView (EthCLSpecs.Heze.modValidatorAt (pureState acc) i fun w =>
      { pubkey := pk w, withdrawalCredentials := wc w, effectiveBalance := w.effectiveBalance,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := ae w,
        exitEpoch := ee w, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidatorAt_pureState]
  exact ebView_setValidator acc _ _ rfl

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The block functions keep `ebView` -/

/-- `increaseBalance` returns a state value with the `ebView` of its argument. -/
@[frame] theorem increaseBalance_ret_eb {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    ebView (pureState b) = ebView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `ebView` of its argument. -/
@[frame] theorem decreaseBalance_ret_eb {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    ebView (pureState b) = ebView (pureState u) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `ebView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_eb {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `ebView`. -/
@[frame] theorem initiateValidatorExit_frame_eb {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- The payment loop of `slashValidator` writes the payment window only, so it keeps
`ebView`. -/
theorem voidPayments_frame_eb (i : ValidatorIndex) (u : BeaconState) :
    ebView (voidPayments i (pureState u)) = ebView (pureState u) := by
  let P : State → Prop := fun s => ∃ w, s = pureState w ∧ ebView (pureState w) = ebView (pureState u)
  obtain ⟨w, hw, hk⟩ : P (voidPayments i (pureState u)) := by
    unfold voidPayments
    simp only [bind_pure]
    refine EthCLLib.Proofs.id_forIn_range_inv P _ ?_ _ _ ⟨u, rfl, rfl⟩
    rintro d s ⟨w, rfl, hk⟩
    try dsimp only
    split
    · exact ⟨{ w with builderPendingPayments := w.builderPendingPayments.set! d default }, rfl,
        hk⟩
    · exact ⟨w, rfl, hk⟩
  rw [hw]
  exact hk

/-- `slashValidator` keeps `ebView`. The proof inverts the run step by step, as
`slashValidator_frame_key` does: the write of the slashed validator sits inside the
`sszUpdate` of the slashings vector, where no `@[frame_close]` lemma matches. -/
@[frame] theorem slashValidator_frame_eb {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  rw [slashValidator_eq] at h
  obtain ⟨_, s9, h9, h⟩ :=
    EthCLLib.Proofs.run_bind_eq_ok_pure (keepsUncached_slashValidatorPrefix i) h
  rw [modifyState_run_eq h, voidPayments_frame_eb]
  clear h
  have h := h9
  unfold slashValidatorPrefix at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, a1, h1, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure
    (keepsUncached_initiateValidatorExit i) h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v1, s, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hv
  simp only [modValidator_pureState] at h
  simp only [pureState_eq_ofValue, uncached_ofValue_view] at h
  simp only [box_view_uncached, uncached_ofValue_view, uncached_mk_eq] at h
  simp only [← pureState_eq_ofValue] at h
  obtain ⟨_, s0, hs0, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0 := checkedAdd_run_state hs0
  subst e0
  obtain ⟨_, s0', hs0', h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0' := checkedAdd_run_state hs0'
  subst e0'
  obtain ⟨x1, s1, h2, h⟩ := run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) h
  obtain ⟨u1, s2, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h3
  subst e3
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, s2', hs2', h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2' : s2' = pureState x1 := by
    unfold checkedMul throwArithmetic at hs2'
    rcases EthCLLib.Proofs.run_ite_eq_ok hs2' with ⟨-, hs2'⟩ | ⟨-, hs2'⟩
    · cases hs2'
    · exact EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hs2'
  subst e2'
  obtain ⟨x2, s3, h4, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  obtain ⟨x3, s4, h5, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  have e6 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  rw [e6, increaseBalance_ret_eb h5, increaseBalance_ret_eb h4, decreaseBalance_ret_eb h2,
    ← initiateValidatorExit_frame_eb h1]
  exact ebView_setValidator a1 _ _ rfl

/-- `applyWithdrawals` keeps `ebView`. -/
@[frame] theorem applyWithdrawals_frame_eb {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `ebView`. -/
@[frame] theorem processWithdrawals_frame_eb {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `ebView`. -/
@[frame] theorem processRandao_frame_eb {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processAttesterSlashing` keeps `ebView`. -/
@[frame] theorem processAttesterSlashing_frame_eb {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `ebView`. It moves balance to the deposit queue and keeps
the effective balance. -/
@[frame] theorem queueExcessActiveBalance_frame_eb {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `ebView`. -/
@[frame] theorem switchToCompoundingValidator_frame_eb {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `ebView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_eb {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `ebView`. -/
@[frame] theorem initiateBuilderExit_frame_eb {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `ebView`. -/
@[frame] theorem addBuilderToRegistry_frame_eb {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `ebView`. It appends to the deposit queue. -/
@[frame] theorem processDepositRequest_frame_eb {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps `ebView`. -/
@[frame] theorem processWithdrawalRequest_frame_eb {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps `ebView`. -/
@[frame] theorem processConsolidationRequest_frame_eb {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `ebView`. -/
@[frame] theorem processBuilderDepositRequest_frame_eb {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `ebView`. -/
@[frame] theorem processBuilderExitRequest_frame_eb {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `ebView`. -/
@[frame] theorem settleBuilderPayment_frame_eb {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps `ebView`. -/
@[frame] theorem processProposerSlashing_frame_eb {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps `ebView`. -/
@[frame] theorem applyParentExecutionPayload_frame_eb {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps `ebView`. -/
@[frame] theorem processParentExecutionPayload_frame_eb {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps `ebView`. Its two nested loops need more than the default
heartbeat limit. -/
@[frame] theorem processAttestation_frame_eb {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation} {parentSlot : Slot}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att parentSlot).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `ebView`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_eb {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps `ebView`. -/
@[frame] theorem processBlockHeader_frame_eb {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps `ebView`. -/
@[frame] theorem processVoluntaryExit_frame_eb {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `ebView`. It writes the withdrawal credentials. -/
@[frame] theorem processBlsToExecutionChange_frame_eb {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `ebView`. It writes balances only. -/
@[frame] theorem processSyncAggregate_frame_eb {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-- **`processBlock` keeps `ebView`.** -/
@[frame] theorem processBlock_frame_eb {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    ebView (pureState t') = ebView (pureState t) := by
  frame_invert h

/-! ## The functions after the attestation loop keep `comView` -/

/-- **A voluntary exit keeps the committees of the window.** It runs `initiateValidatorExit`
(`initiateValidatorExit_frame_com`). -/
@[frame] theorem processVoluntaryExit_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `comView`. Its write keeps the activation and exit
epochs. -/
@[frame] theorem processBlsToExecutionChange_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `comView`. -/
@[frame] theorem processSyncAggregate_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- **`processBlock` keeps the committees of the window.** -/
theorem processBlock_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-! ## The slot step -/

/-- **A slot step that does not end an epoch keeps the registry.** It runs `processSlot`,
which writes the roots and the header (`slotWrite`), then the slot increment. -/
theorem SlotStep.validators_of_not_boundary {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch ≠ 0) :
    u'.validators = u.validators := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  split at h2
  · rename_i htest
    exact absurd ((epochTest_iff (slotWrite u).slot hlt).mp htest) hb
  · subst h2
    have := congrArg (fun s : State => s.view.validators) hst'
    exact this

end

end EthCLSpecs.Proofs.Heze
