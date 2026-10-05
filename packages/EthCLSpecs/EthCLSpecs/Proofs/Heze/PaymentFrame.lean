import EthCLSpecs.Heze.Transition
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.FrameInvert

/-!
# `EthCLSpecs.Proofs.Heze.PaymentFrame`: the functions that keep the payment window

`processBuilderPendingPayments` judges the payment of a bid one epoch after the block.
Between the two, the chain runs slots, epochs, and blocks. Five spec functions write the
payment window `builderPendingPayments` (`PaymentWriters.lean`). This module proves that the
others keep it.

The run argument (`PaymentCarried.lean`) tracks three more fields: the state slot,
the slot of the latest block header, and the cached bid `latestExecutionPayloadBid`. The
writers settle or record the index of a slot that these fields fix. So each frame lemma
here states one fact for all four fields, the view `windowView`. A function that writes the
window but keeps the other three has a frame lemma for `spineView`.

Each lemma states its run over plain values,
`(h : f.run (pureState t) = .ok (a, pureState t')) : windowView (pureState t') = windowView
(pureState t)`, and `frame_invert` (`FrameInvert.lean`) proves it. The attribute `@[frame]`
lets a caller's proof close the call by the lemma. A function that reads the state only has
one lemma with the conclusion `(pureState t').view = (pureState t).view`, which serves each
view through `frame_of_reads`. `spine_of_window` takes a `windowView` fact to a `spineView`
fact, so a writer proof can call every function below.

A helper that takes the state as an argument and returns a state value (`increaseBalance`,
`decreaseBalance`, `applyDeltas`) has a `_ret` lemma too: the value it returns has the view
of its argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot ExecutionPayloadBid BuilderPendingPayment BeaconState
  ValidatorIndex Gwei)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

attribute [frame_proj] frame_of_reads

section
variable [Preset] [HasherTag]

/-- The three fields that fix which payment index a writer touches: the state slot, the
slot of the latest block header, and the cached bid. -/
def spineView (st : State) : Slot × Slot × ExecutionPayloadBid :=
  (sszGet st slot, (sszGet st latestBlockHeader).slot, sszGet st latestExecutionPayloadBid)

/-- The spine fields and the payment window. -/
def windowView (st : State) :
    (Slot × Slot × ExecutionPayloadBid) × Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  (spineView st, sszGet st builderPendingPayments)

/-- A run that keeps `windowView` keeps `spineView`, the first part of the view. -/
@[frame_proj] theorem spine_of_window {a b : BeaconState}
    (h : windowView (pureState a) = windowView (pureState b)) :
    spineView (pureState a) = spineView (pureState b) :=
  congrArg Prod.fst h

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The epoch functions -/

/-- `processSlashingsReset` keeps the tracked fields. -/
@[frame] theorem processSlashingsReset_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps the tracked fields. -/
@[frame] theorem processEth1Data_frame {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps the tracked fields. -/
@[frame] theorem processEth1DataReset_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps the tracked fields. -/
@[frame] theorem processRandaoMixesReset_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps the tracked fields. -/
@[frame] theorem processHistoricalSummariesUpdate_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processParticipationFlagUpdates` keeps the tracked fields. -/
@[frame] theorem processParticipationFlagUpdates_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps the tracked fields. -/
@[frame] theorem processSyncCommitteeUpdates_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps the tracked fields. -/
@[frame] theorem processProposerLookahead_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps the tracked fields. -/
@[frame] theorem processPtcWindow_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `increaseBalance` keeps the state it runs on. -/
@[frame] theorem increaseBalance_frame {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `increaseBalance` returns a state value with the tracked fields of its argument. -/
@[frame] theorem increaseBalance_ret {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    windowView (pureState b) = windowView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` keeps the state it runs on. -/
@[frame] theorem decreaseBalance_frame {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the tracked fields of its argument. -/
@[frame] theorem decreaseBalance_ret {u t t' b : BeaconState} {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    windowView (pureState b) = windowView (pureState u) := by
  frame_invert h

/-- `applyDeltas` keeps the state it runs on. It threads its state argument through a loop. -/
@[frame] theorem applyDeltas_frame {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `applyDeltas` returns a state value with the tracked fields of its argument. Each loop
step runs `increaseBalance` and `decreaseBalance` on the accumulator. -/
@[frame] theorem applyDeltas_ret {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    windowView (pureState b) = windowView (pureState u) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps the tracked fields. -/
@[frame] theorem processRewardsAndPenalties_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps the tracked fields. -/
@[frame] theorem processSlashings_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps the tracked fields. It writes the
justification bits and the three checkpoints. The join points of the weigh step need
`jf_frame` (`FrameInvert.lean`). -/
@[frame] theorem processJustificationAndFinalization_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  jf_frame windowView h

/-- `processInactivityUpdates` keeps the tracked fields. -/
@[frame] theorem processInactivityUpdates_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processEffectiveBalanceUpdates` keeps the tracked fields. -/
@[frame] theorem processEffectiveBalanceUpdates_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps the tracked fields. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame {t t' : BeaconState} {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps the tracked fields. -/
@[frame] theorem initiateValidatorExit_frame {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps the tracked fields. -/
@[frame] theorem processRegistryUpdates_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `addValidatorToRegistry` keeps the tracked fields. -/
@[frame] theorem addValidatorToRegistry_frame {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `applyPendingDeposit` keeps the tracked fields. -/
@[frame] theorem applyPendingDeposit_frame {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps the tracked fields. -/
@[frame] theorem ppdLoop_frame {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processPendingDeposits` keeps the tracked fields. -/
@[frame] theorem processPendingDeposits_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processPendingConsolidations` keeps the tracked fields. -/
@[frame] theorem processPendingConsolidations_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processSlot` keeps the tracked fields. It writes the state and block roots, the
state root of the latest header, and the next availability bit. The header keeps its
slot. -/
@[frame] theorem processSlot_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps the spine fields. It writes the withdrawal
queue and the payment window. -/
@[frame] theorem processBuilderPendingPayments_frame_spine {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

/-- The eight substeps of `processEpoch` before `processBuilderPendingPayments`. -/
def processEpochPrefix : HezeRun Unit := do
  EthCLSpecs.Heze.processJustificationAndFinalization
  EthCLSpecs.Heze.processInactivityUpdates
  EthCLSpecs.Heze.processRewardsAndPenalties
  EthCLSpecs.Heze.processRegistryUpdates
  EthCLSpecs.Heze.processSlashings
  EthCLSpecs.Heze.processEth1DataReset
  EthCLSpecs.Heze.processPendingDeposits
  EthCLSpecs.Heze.processPendingConsolidations

/-- The eight substeps of `processEpoch` after `processBuilderPendingPayments`. -/
def processEpochSuffix : HezeRun Unit := do
  EthCLSpecs.Heze.processEffectiveBalanceUpdates
  EthCLSpecs.Heze.processSlashingsReset
  EthCLSpecs.Heze.processRandaoMixesReset
  EthCLSpecs.Heze.processHistoricalSummariesUpdate
  EthCLSpecs.Heze.processParticipationFlagUpdates
  EthCLSpecs.Heze.processSyncCommitteeUpdates
  EthCLSpecs.Heze.processProposerLookahead
  EthCLSpecs.Heze.processPtcWindow

/-- `processEpoch` is the prefix, the payment substep, and the suffix. -/
theorem processEpoch_eq :
    (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)) =
      (processEpochPrefix >>= fun _ =>
        EthCLSpecs.Heze.processBuilderPendingPayments >>= fun _ => processEpochSuffix) := by
  unfold EthCLSpecs.Heze.processEpoch processEpochPrefix processEpochSuffix
  simp only [bind_assoc]

/-- The epoch prefix keeps the tracked fields. -/
@[frame] theorem processEpochPrefix_frame {t t' : BeaconState} {a : Unit}
    (h : processEpochPrefix.run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- The epoch suffix keeps the tracked fields. -/
@[frame] theorem processEpochSuffix_frame {t t' : BeaconState} {a : Unit}
    (h : processEpochSuffix.run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
