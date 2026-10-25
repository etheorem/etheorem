import EthCLSpecs.Proofs.Heze.CheckpointFrame
import EthCLSpecs.Proofs.Heze.Participation

/-!
# `EthCLSpecs.Proofs.Heze.KeyFrame`: a block step keeps the fields that attestation validity reads

`isValidIndexedAttestation` reads three fields of a state: the registry, the fork, and the
genesis validators root. From the registry it reads the size and the public key at each
attesting index. `keyView` holds the public keys of the registry, the fork, and the genesis
validators root.

A block step changes validators at their indices, and only the epoch step adds validators. A
slashing, an exit, or a switch to compounding credentials writes one validator through
`modValidator`. Each such write keeps the public key (`keyView_modValidator`). A deposit
request appends to the deposit queue, and the epoch step adds its validator. So each function that a block step
runs before the attestation loop, and each one inside the loop, keeps `keyView`.
`RunVotes.lean` uses this fact: the state on which `processAttestation` accepts an attestation
has the `keyView` of the run state before the block.

`frame_invert` proves a frame lemma for each function that writes the state. The lemmas come
in the order of the block functions of `CheckpointFrame.lean`. The proof for `slashValidator`
inverts the run step by step. A function that only reads the state needs no lemma here. Its
lemma in `PaymentFrame.lean` applies to each view.

The module also holds the plain-state forms of a write (`modValidator_pureState` and the box
forms). The drift proofs use them too.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_bind_eq_ok run_get_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-! ## Plain-state forms of a write -/

/-- `pureState x` as the constructor of the uncached box. A field write through `sszUpdate`
matches on the box. With this form, `simp` takes the uncached branch of that match. -/
theorem pureState_eq_ofValue (x : BeaconState) :
    (pureState x : State) = .uncached (SizzLean.Cache.UncachedSSZ.ofValue HasherTag.H x) := rfl

theorem uncached_ofValue_view (x : BeaconState) :
    (SizzLean.Cache.UncachedSSZ.ofValue HasherTag.H x).view = x := rfl

/-- An uncached box built from its field is the uncached box of the value. -/
theorem uncached_mk_eq (x : BeaconState) :
    (SizzLean.Cache.SSZ.Box.uncached ({ view := x } : SizzLean.Cache.UncachedSSZ HasherTag.H
      BeaconState) : State) = pureState x := rfl

theorem box_view_uncached (t : SizzLean.Cache.UncachedSSZ HasherTag.H BeaconState) :
    (SizzLean.Cache.SSZ.Box.uncached t : State).view = t.view := rfl

/-- `modValidator` on a plain state writes one validator, with `f` applied to the old one. -/
theorem modValidator_pureState (t : BeaconState) (i : ValidatorIndex)
    (f : Validator → Validator) :
    EthCLSpecs.Heze.modValidator (pureState t) i f =
      pureState { t with validators := t.validators.set! i.toNat (f t.validators[i.toNat]!) } := rfl

/-! ## The view -/

/-- The public keys of the registry, the fork, and the genesis validators root. -/
def keyView (st : State) :=
  ((sszGet st validators).val.map (·.pubkey), sszGet st forkData, sszGet st genesisValidatorsRoot)

/-- A write at index `j` keeps `keyView` when the new validator has the public key of the old
validator at `j`. -/
theorem keyView_setValidator (a : BeaconState) (j : Nat) (v' : Validator)
    (hv : v'.pubkey = a.validators[j]!.pubkey) :
    keyView (pureState { a with validators := a.validators.set! j v' }) =
      keyView (pureState a) := by
  simp only [keyView, Prod.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  show (a.validators.val.setIfInBounds j v').map (fun x => x.pubkey) =
    a.validators.val.map (fun x => x.pubkey)
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

/-- A write of one validator that keeps its public key keeps `keyView`. Each record update of
a validator in the block functions has this form. The new validator has the public key of the
old one, and its other seven fields are functions of the old one. `frame_invert` closes such a
write with this lemma. -/
@[frame_close] theorem keyView_modValidator {acc : BeaconState} {i : ValidatorIndex}
    {wc : Validator → EthCLSpecs.Heze.Bytes32} {eb : Validator → Gwei} {sl : Validator → Bool}
    {aee ae ee we : Validator → EthCLSpecs.Heze.Epoch} {v : _}
    (hacc : keyView (pureState acc) = v) :
    keyView (EthCLSpecs.Heze.modValidator (pureState acc) i fun w =>
      { pubkey := w.pubkey, withdrawalCredentials := wc w, effectiveBalance := eb w,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := ae w,
        exitEpoch := ee w, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidator_pureState]
  exact keyView_setValidator acc _ _ rfl

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `increaseBalance` returns a state value with the `keyView` of its argument. -/
@[frame] theorem increaseBalance_ret_key {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    keyView (pureState b) = keyView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `keyView` of its argument. -/
@[frame] theorem decreaseBalance_ret_key {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    keyView (pureState b) = keyView (pureState u) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `keyView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_key {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `keyView`. -/
@[frame] theorem initiateValidatorExit_frame_key {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `slashValidator` keeps `keyView`. The write of the slashed validator is inside the
`sszUpdate` of the slashings vector. That update matches on the box with a matcher of its own
declaration, and a `@[frame_close]` lemma cannot match it. So the proof inverts the run step by
step, as `slashValidator_run` (`DriftSlash.lean`) does. -/
@[frame] theorem slashValidator_frame_key {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  unfold EthCLSpecs.Heze.slashValidator at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, a1, h1, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure
    (keepsUncached_initiateValidatorExit i) h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v1, s, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hv
  -- Write the two updates of `pureState a1` as `pureState` of a record of `a1`.
  simp only [modValidator_pureState] at h
  simp only [pureState_eq_ofValue, uncached_ofValue_view] at h
  simp only [box_view_uncached, uncached_ofValue_view, uncached_mk_eq] at h
  simp only [← pureState_eq_ofValue] at h
  -- The two checked sums keep the state.
  obtain ⟨_, s0, hs0, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0 := checkedAdd_run_state hs0
  subst e0
  obtain ⟨_, s0', hs0', h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0' := checkedAdd_run_state hs0'
  subst e0'
  -- The penalty, then the two rewards of the proposer.
  obtain ⟨x1, s1, h2, h⟩ := run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) h
  obtain ⟨u1, s2, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h3
  subst e3
  have h := run_get_bind_eq_ok _ _ _ h
  -- The checked product `whistleblower_reward * PROPOSER_WEIGHT` keeps the state.
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
  rw [e6, increaseBalance_ret_key h5, increaseBalance_ret_key h4, decreaseBalance_ret_key h2,
    ← initiateValidatorExit_frame_key h1]
  exact keyView_setValidator a1 _ _ rfl

/-- `applyWithdrawals` keeps `keyView`. -/
@[frame] theorem applyWithdrawals_frame_key {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `keyView`. -/
@[frame] theorem processWithdrawals_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `keyView`. -/
@[frame] theorem processRandao_frame_key {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `keyView`. -/
@[frame] theorem processEth1Data_frame_key {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processAttesterSlashing` keeps `keyView`. -/
@[frame] theorem processAttesterSlashing_frame_key {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `keyView`. -/
@[frame] theorem queueExcessActiveBalance_frame_key {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `keyView`. -/
@[frame] theorem switchToCompoundingValidator_frame_key {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `keyView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_key {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `keyView`. -/
@[frame] theorem initiateBuilderExit_frame_key {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `keyView`. -/
@[frame] theorem addBuilderToRegistry_frame_key {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `keyView`. It appends to the deposit queue. -/
@[frame] theorem processDepositRequest_frame_key {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps `keyView`. -/
@[frame] theorem processWithdrawalRequest_frame_key {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps `keyView`. -/
@[frame] theorem processConsolidationRequest_frame_key {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `keyView`. -/
@[frame] theorem processBuilderDepositRequest_frame_key {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `keyView`. -/
@[frame] theorem processBuilderExitRequest_frame_key {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `keyView`. -/
@[frame] theorem settleBuilderPayment_frame_key {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps `keyView`. -/
@[frame] theorem processProposerSlashing_frame_key {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps `keyView`. -/
@[frame] theorem applyParentExecutionPayload_frame_key {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps `keyView`. -/
@[frame] theorem processParentExecutionPayload_frame_key {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps `keyView`. Its two nested loops need more than the default
heartbeat limit. -/
@[frame] theorem processAttestation_frame_key {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `keyView`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_key {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps `keyView`. -/
@[frame] theorem processBlockHeader_frame_key {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
