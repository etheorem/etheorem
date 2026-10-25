import EthCLSpecs.Proofs.Heze.CheckpointFrame

/-!
# `EthCLSpecs.Proofs.Heze.HeaderFrame`: the functions that keep the header and the block roots

Two functions write the latest block header of a beacon state. `processBlockHeader` writes
the header of the new block, with a zero state root. `processSlot` fills that state root and
caches the root of the header in `blockRoots`. No other function writes the header or
`blockRoots` (`BlockRootsRun.lean`).

This module proves that every other function of a slot step and a block step keeps both
fields. The view is `hdrView`: the header and `blockRoots`. `processEpoch_frame_hdr` covers
the epoch step. `processBlockTail_frame_hdr` covers the part of a block step after
`processBlockHeader` (`processBlock_eq_tail`).

Each lemma is a `frame_invert` proof, as the `ordView` lemmas of `CheckpointFrame.lean` are,
in the same order. A function that reads the state only needs no lemma here.
`processJustificationAndFinalization` names its join points through `jf_frame`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconBlockHeader Root BeaconState ValidatorIndex
  Gwei)

section
variable [Preset] [HasherTag]

/-- The latest block header and the block roots. -/
def hdrView (st : State) : BeaconBlockHeader × Vector Root EthCLSpecs.Heze.Const.slotsPerHistoricalRoot :=
  (sszGet st latestBlockHeader, sszGet st blockRoots)

end

/-! ## The epoch functions -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processSlashingsReset` keeps `hdrView`. -/
@[frame] theorem processSlashingsReset_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `hdrView`. -/
@[frame] theorem processEth1Data_frame_hdr {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `hdrView`. -/
@[frame] theorem processEth1DataReset_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps `hdrView`. -/
@[frame] theorem processRandaoMixesReset_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps `hdrView`. -/
@[frame] theorem processHistoricalSummariesUpdate_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processParticipationFlagUpdates` keeps `hdrView`. -/
@[frame] theorem processParticipationFlagUpdates_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps `hdrView`. -/
@[frame] theorem processSyncCommitteeUpdates_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps `hdrView`. -/
@[frame] theorem processProposerLookahead_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps `hdrView`. -/
@[frame] theorem processPtcWindow_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `increaseBalance` returns a state value with the `hdrView` of its argument. -/
@[frame] theorem increaseBalance_ret_hdr {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    hdrView (pureState b) = hdrView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `hdrView` of its argument. -/
@[frame] theorem decreaseBalance_ret_hdr {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    hdrView (pureState b) = hdrView (pureState u) := by
  frame_invert h

/-- `applyDeltas` returns a state value with the `hdrView` of its argument. -/
@[frame] theorem applyDeltas_ret_hdr {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    hdrView (pureState b) = hdrView (pureState u) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps `hdrView`. -/
@[frame] theorem processRewardsAndPenalties_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps `hdrView`. -/
@[frame] theorem processSlashings_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processInactivityUpdates` keeps `hdrView`. -/
@[frame] theorem processInactivityUpdates_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processEffectiveBalanceUpdates` keeps `hdrView`. -/
@[frame] theorem processEffectiveBalanceUpdates_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `hdrView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_hdr {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `hdrView`. -/
@[frame] theorem initiateValidatorExit_frame_hdr {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps `hdrView`. -/
@[frame] theorem processRegistryUpdates_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `addValidatorToRegistry` keeps `hdrView`. -/
@[frame] theorem addValidatorToRegistry_frame_hdr {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `applyPendingDeposit` keeps `hdrView`. -/
@[frame] theorem applyPendingDeposit_frame_hdr {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps `hdrView`. -/
@[frame] theorem ppdLoop_frame_hdr {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processPendingDeposits` keeps `hdrView`. -/
@[frame] theorem processPendingDeposits_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processPendingConsolidations` keeps `hdrView`. -/
@[frame] theorem processPendingConsolidations_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps `hdrView`. It writes the withdrawal queue and the
payment window. -/
@[frame] theorem processBuilderPendingPayments_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps `hdrView`. The join points of the weigh step
need `jf_frame`. -/
@[frame] theorem processJustificationAndFinalization_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  jf_frame hdrView h

/-! ## The block functions -/

/-- `slashValidator` keeps `hdrView`. -/
@[frame] theorem slashValidator_frame_hdr {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `applyWithdrawals` writes the balances of validators and builders only. -/
@[frame] theorem applyWithdrawals_frame_hdr {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `hdrView`. -/
@[frame] theorem processWithdrawals_frame_hdr {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `hdrView`. -/
@[frame] theorem processRandao_frame_hdr {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `hdrView`. -/
@[frame] theorem processSyncAggregate_frame_hdr {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processAttesterSlashing` keeps `hdrView`. -/
@[frame] theorem processAttesterSlashing_frame_hdr {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps `hdrView`. -/
@[frame] theorem processVoluntaryExit_frame_hdr {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `hdrView`. -/
@[frame] theorem processBlsToExecutionChange_frame_hdr {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `hdrView`. -/
@[frame] theorem queueExcessActiveBalance_frame_hdr {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `hdrView`. -/
@[frame] theorem switchToCompoundingValidator_frame_hdr {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `hdrView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_hdr {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `hdrView`. -/
@[frame] theorem initiateBuilderExit_frame_hdr {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `hdrView`. -/
@[frame] theorem addBuilderToRegistry_frame_hdr {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `hdrView`. -/
@[frame] theorem processDepositRequest_frame_hdr {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps `hdrView`. -/
@[frame] theorem processWithdrawalRequest_frame_hdr {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps `hdrView`. -/
@[frame] theorem processConsolidationRequest_frame_hdr {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `hdrView`. -/
@[frame] theorem processBuilderDepositRequest_frame_hdr {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `hdrView`. -/
@[frame] theorem processBuilderExitRequest_frame_hdr {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `hdrView`. -/
@[frame] theorem settleBuilderPayment_frame_hdr {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps `hdrView`. -/
@[frame] theorem processProposerSlashing_frame_hdr {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps `hdrView`. -/
@[frame] theorem applyParentExecutionPayload_frame_hdr {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps `hdrView`. -/
@[frame] theorem processParentExecutionPayload_frame_hdr {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps `hdrView`. Its two nested loops need more than the default
heartbeat limit. -/
@[frame] theorem processAttestation_frame_hdr {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `hdrView`. Its builder checks read the header, and
need more than the default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_hdr {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processOperations` keeps `hdrView`. -/
@[frame] theorem processOperations_frame_hdr {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run
      (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- The six substeps of `processBlock` after `processBlockHeader`. -/
def processBlockTail (b : EthCLSpecs.Heze.BeaconBlock) : HezeRun Unit := do
  EthCLSpecs.Heze.processWithdrawals
  EthCLSpecs.Heze.processExecutionPayloadBid b.body.signedExecutionPayloadBid
  EthCLSpecs.Heze.processRandao b.body
  EthCLSpecs.Heze.processEth1Data b.body
  EthCLSpecs.Heze.processOperations b.body
  EthCLSpecs.Heze.processSyncAggregate b.body.syncAggregate

/-- `processBlock` is the parent payload step, the header step, and the tail. -/
theorem processBlock_eq_tail (b : EthCLSpecs.Heze.BeaconBlock) :
    (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b) =
      (EthCLSpecs.Heze.processParentExecutionPayload b >>= fun _ =>
        EthCLSpecs.Heze.processBlockHeader b >>= fun _ => processBlockTail b) := by
  unfold EthCLSpecs.Heze.processBlock processBlockTail
  rfl

/-- The tail of `processBlock` keeps `hdrView`. -/
@[frame] theorem processBlockTail_frame_hdr {t t' : BeaconState} {a : Unit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (processBlockTail b).run (pureState t) = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  frame_invert h

/-- `processEpoch` keeps `hdrView`. -/
@[frame] theorem processEpoch_frame_hdr {t t' : BeaconState} {a : Unit}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    hdrView (pureState t') = hdrView (pureState t) := by
  rw [processEpoch_eq_jf] at h
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
