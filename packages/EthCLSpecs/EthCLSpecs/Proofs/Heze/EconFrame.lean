import EthCLSpecs.Proofs.Heze.DriftInv
import EthCLSpecs.Proofs.Heze.PaymentFrame

/-!
# `EthCLSpecs.Proofs.Heze.EconFrame`: the functions that keep the reads of the drift

`RunInv` reads a state through `econView`: the registry, the balances, the two queues it
weighs, and the four churn fields. This module proves that every function of a run that
writes none of them keeps `econView`. With `RunInv.of_econ`, such a function keeps the
invariant.

Each function that writes the state has a frame lemma by `frame_invert`. A function that
reads the state only needs no lemma here: its `PaymentFrame.lean` lemma serves each view.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState Gwei)

section
variable [Preset] [HasherTag]

/-- `econView` of the view of a box. -/
def econBox (st : State) := econView st.view

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processSlashingsReset` keeps `econBox`. -/
@[frame] theorem processSlashingsReset_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `econBox`. -/
@[frame] theorem processEth1Data_frame_econ {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `econBox`. -/
@[frame] theorem processEth1DataReset_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps `econBox`. -/
@[frame] theorem processRandaoMixesReset_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps `econBox`. -/
@[frame] theorem processHistoricalSummariesUpdate_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processParticipationFlagUpdates` keeps `econBox`. -/
@[frame] theorem processParticipationFlagUpdates_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps `econBox`. -/
@[frame] theorem processSyncCommitteeUpdates_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps `econBox`. -/
@[frame] theorem processProposerLookahead_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps `econBox`. -/
@[frame] theorem processPtcWindow_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processInactivityUpdates` keeps `econBox`. -/
@[frame] theorem processInactivityUpdates_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps `econBox`. -/
@[frame] theorem processBuilderPendingPayments_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processSlot` keeps `econBox`. It writes the state and block roots, the state root of the
latest header, and the next availability bit. -/
@[frame] theorem processSlot_frame_econ {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps `econBox`. It writes the justification bits
and the three checkpoints. -/
@[frame] theorem processJustificationAndFinalization_frame_econ {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  jf_frame econBox h

/-- `processBlockHeader` keeps `econBox`. -/
@[frame] theorem processBlockHeader_frame_econ {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `econBox`. -/
@[frame] theorem processRandao_frame_econ {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `econBox`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_econ {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `econBox`. It appends to the deposit queue. -/
@[frame] theorem processDepositRequest_frame_econ {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `econBox`. -/
@[frame] theorem settleBuilderPayment_frame_econ {t t' : BeaconState} {a : PUnit} {j : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `econBox`. -/
@[frame] theorem initiateBuilderExit_frame_econ {t t' : BeaconState} {a : PUnit}
    {j : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `econBox`. -/
@[frame] theorem addBuilderToRegistry_frame_econ {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `econBox`. -/
@[frame] theorem processBuilderDepositRequest_frame_econ {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `econBox`. -/
@[frame] theorem processBuilderExitRequest_frame_econ {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    econBox (pureState t') = econBox (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
