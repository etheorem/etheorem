import EthCLSpecs.Proofs.Heze.JustificationAndFinalization
import EthCLSpecs.Proofs.Heze.PaymentCarried

/-!
# `EthCLSpecs.Proofs.Heze.CheckpointFrame`: the functions that keep the checkpoints

Only `process_justification_and_finalization` writes the three checkpoints of a beacon
state and the justification bits. This module proves that every other function of a slot
step and a block step keeps them, and keeps the slot. The view is `ordView`: the four
fields of `ckView` (`JustificationAndFinalization.lean`) and the slot.

Each function that writes the state has a frame lemma by `frame_invert`, in the same order
as the `windowView` lemmas of `PaymentFrame.lean`. A function that reads the state only
needs no lemma here: its `PaymentFrame.lean` lemma serves each view. `processBlock_frame_ord`
covers a block step. `processEpochAfterJF_frame_ord` covers the substeps of `processEpoch`
after `processJustificationAndFinalization` (`processEpoch_eq_jf`). `CheckpointInvariants.lean`
uses both for the order of the checkpoints along a chain run.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState ValidatorIndex Gwei)

section
variable [Preset] [HasherTag]

/-- The four fields that the weigh step writes, and the slot. -/
def ordView (st : State) : CkView × Slot :=
  (ckView st, sszGet st slot)

end

/-! ## The epoch functions -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processSlashingsReset` keeps `ordView`. -/
@[frame] theorem processSlashingsReset_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `ordView`. -/
@[frame] theorem processEth1Data_frame_ord {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `ordView`. -/
@[frame] theorem processEth1DataReset_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps `ordView`. -/
@[frame] theorem processRandaoMixesReset_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps `ordView`. -/
@[frame] theorem processHistoricalSummariesUpdate_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processParticipationFlagUpdates` keeps `ordView`. -/
@[frame] theorem processParticipationFlagUpdates_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps `ordView`. -/
@[frame] theorem processSyncCommitteeUpdates_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps `ordView`. -/
@[frame] theorem processProposerLookahead_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps `ordView`. -/
@[frame] theorem processPtcWindow_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `increaseBalance` returns a state value with the `ordView` of its argument. -/
@[frame] theorem increaseBalance_ret_ord {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    ordView (pureState b) = ordView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `ordView` of its argument. -/
@[frame] theorem decreaseBalance_ret_ord {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    ordView (pureState b) = ordView (pureState u) := by
  frame_invert h

/-- `applyDeltas` returns a state value with the `ordView` of its argument. -/
@[frame] theorem applyDeltas_ret_ord {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    ordView (pureState b) = ordView (pureState u) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps `ordView`. -/
@[frame] theorem processRewardsAndPenalties_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps `ordView`. -/
@[frame] theorem processSlashings_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processInactivityUpdates` keeps `ordView`. -/
@[frame] theorem processInactivityUpdates_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processEffectiveBalanceUpdates` keeps `ordView`. -/
@[frame] theorem processEffectiveBalanceUpdates_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `ordView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_ord {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `ordView`. -/
@[frame] theorem initiateValidatorExit_frame_ord {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps `ordView`. -/
@[frame] theorem processRegistryUpdates_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `addValidatorToRegistry` keeps `ordView`. -/
@[frame] theorem addValidatorToRegistry_frame_ord {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `applyPendingDeposit` keeps `ordView`. -/
@[frame] theorem applyPendingDeposit_frame_ord {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps `ordView`. -/
@[frame] theorem ppdLoop_frame_ord {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processPendingDeposits` keeps `ordView`. -/
@[frame] theorem processPendingDeposits_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processPendingConsolidations` keeps `ordView`. -/
@[frame] theorem processPendingConsolidations_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processSlot` keeps `ordView`. It writes the state and block roots, the state root of
the latest header, and the next availability bit. -/
@[frame] theorem processSlot_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps `ordView`. It writes the withdrawal queue and the
payment window. -/
@[frame] theorem processBuilderPendingPayments_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-! ## The block functions -/

/-- `slashValidator` keeps `ordView`. -/
@[frame] theorem slashValidator_frame_ord {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `applyWithdrawals` writes the balances of validators and builders only. -/
@[frame] theorem applyWithdrawals_frame_ord {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `ordView`. -/
@[frame] theorem processWithdrawals_frame_ord {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `ordView`. -/
@[frame] theorem processRandao_frame_ord {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `ordView`. -/
@[frame] theorem processSyncAggregate_frame_ord {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processAttesterSlashing` keeps `ordView`. -/
@[frame] theorem processAttesterSlashing_frame_ord {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps `ordView`. -/
@[frame] theorem processVoluntaryExit_frame_ord {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `ordView`. -/
@[frame] theorem processBlsToExecutionChange_frame_ord {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `ordView`. -/
@[frame] theorem queueExcessActiveBalance_frame_ord {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `ordView`. -/
@[frame] theorem switchToCompoundingValidator_frame_ord {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `ordView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_ord {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `ordView`. -/
@[frame] theorem initiateBuilderExit_frame_ord {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `ordView`. -/
@[frame] theorem addBuilderToRegistry_frame_ord {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `ordView`. -/
@[frame] theorem processDepositRequest_frame_ord {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps `ordView`. -/
@[frame] theorem processWithdrawalRequest_frame_ord {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps `ordView`. -/
@[frame] theorem processConsolidationRequest_frame_ord {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `ordView`. -/
@[frame] theorem processBuilderDepositRequest_frame_ord {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `ordView`. -/
@[frame] theorem processBuilderExitRequest_frame_ord {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `ordView`. -/
@[frame] theorem settleBuilderPayment_frame_ord {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps `ordView`. -/
@[frame] theorem processProposerSlashing_frame_ord {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps `ordView`. -/
@[frame] theorem applyParentExecutionPayload_frame_ord {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps `ordView`. -/
@[frame] theorem processParentExecutionPayload_frame_ord {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps `ordView`. Its two nested loops need more than the default
heartbeat limit. -/
@[frame] theorem processAttestation_frame_ord {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `ordView`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_ord {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps `ordView`. -/
@[frame] theorem processBlockHeader_frame_ord {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processOperations` keeps `ordView`. -/
@[frame] theorem processOperations_frame_ord {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run
      (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- `processBlock` keeps `ordView`. -/
@[frame] theorem processBlock_frame_ord {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

/-- The fifteen substeps of `processEpoch` after `processJustificationAndFinalization`. -/
def processEpochAfterJF : HezeRun Unit := do
  EthCLSpecs.Heze.processInactivityUpdates
  EthCLSpecs.Heze.processRewardsAndPenalties
  EthCLSpecs.Heze.processRegistryUpdates
  EthCLSpecs.Heze.processSlashings
  EthCLSpecs.Heze.processEth1DataReset
  EthCLSpecs.Heze.processPendingDeposits
  EthCLSpecs.Heze.processPendingConsolidations
  EthCLSpecs.Heze.processBuilderPendingPayments
  processEpochSuffix

/-- `processEpoch` is `processJustificationAndFinalization`, then the other substeps. -/
theorem processEpoch_eq_jf :
    (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)) =
      (EthCLSpecs.Heze.processJustificationAndFinalization >>= fun _ => processEpochAfterJF) := by
  unfold EthCLSpecs.Heze.processEpoch processEpochAfterJF processEpochSuffix
  rfl

/-- The substeps after `processJustificationAndFinalization` keep `ordView`. -/
@[frame] theorem processEpochAfterJF_frame_ord {t t' : BeaconState} {a : Unit}
    (h : processEpochAfterJF.run (pureState t) = .ok (a, pureState t')) :
    ordView (pureState t') = ordView (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
