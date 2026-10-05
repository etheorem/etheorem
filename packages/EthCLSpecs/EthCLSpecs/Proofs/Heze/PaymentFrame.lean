import EthCLSpecs.Heze.Transition
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.FrameInvert
import EthCLSpecs.Proofs.Heze.SyncFrame

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

/-! ## The block functions

`processBlock` runs the functions below. Each one that does not write the window keeps
`windowView`. The writers keep `spineView`. -/

/-- `slashValidator` keeps the tracked fields. -/
@[frame] theorem slashValidator_frame {t t' : BeaconState} {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `balanceAfterWithdrawals` reads the state only. -/
@[frame] theorem balanceAfterWithdrawals_frame {u t t' : BeaconState} {a : _}
    {vi : ValidatorIndex} {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.balanceAfterWithdrawals (StateTransition := HezeRun) (pureState u)
      vi ws).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getBuilderWithdrawals` reads the state only. -/
@[frame] theorem getBuilderWithdrawals_frame {t t' : BeaconState} {a : _}
    {wi : EthCLSpecs.Heze.WithdrawalIndex} {prior : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.getBuilderWithdrawals (StateTransition := HezeRun) wi prior).run
      (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getPendingPartialWithdrawals` reads the state only. -/
@[frame] theorem getPendingPartialWithdrawals_frame {t t' : BeaconState} {a : _}
    {wi : EthCLSpecs.Heze.WithdrawalIndex} {prior : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.getPendingPartialWithdrawals (StateTransition := HezeRun) wi
      prior).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getBuildersSweepWithdrawals` reads the state only. -/
@[frame] theorem getBuildersSweepWithdrawals_frame {t t' : BeaconState} {a : _}
    {wi : EthCLSpecs.Heze.WithdrawalIndex} {prior : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.getBuildersSweepWithdrawals (StateTransition := HezeRun) wi
      prior).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getValidatorsSweepWithdrawals` reads the state only. -/
@[frame] theorem getValidatorsSweepWithdrawals_frame {t t' : BeaconState} {a : _}
    {wi : EthCLSpecs.Heze.WithdrawalIndex} {prior : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.getValidatorsSweepWithdrawals (StateTransition := HezeRun) wi
      prior).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `applyWithdrawals` writes the balances of validators and builders only. -/
@[frame] theorem applyWithdrawals_frame {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `getExpectedWithdrawals` reads the state only. -/
@[frame] theorem getExpectedWithdrawals_frame {t t' : BeaconState} {a : _}
    (h : (EthCLSpecs.Heze.getExpectedWithdrawals (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `processWithdrawals` keeps the tracked fields. It writes the balances, the withdrawal
cursors, the expected withdrawals, and the two withdrawal queues. -/
@[frame] theorem processWithdrawals_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps the tracked fields. It writes one RANDAO mix. -/
@[frame] theorem processRandao_frame {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps the tracked fields. It writes the balances. The join point
after its key choice needs `sync_frame` (`SyncFrame.lean`). -/
@[frame] theorem processSyncAggregate_frame {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  sync_frame windowView h

/-- `processAttesterSlashing` keeps the tracked fields. -/
@[frame] theorem processAttesterSlashing_frame {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps the tracked fields. -/
@[frame] theorem processVoluntaryExit_frame {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps the tracked fields. -/
@[frame] theorem processBlsToExecutionChange_frame {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `getPtc` reads the state only. -/
@[frame] theorem getPtc_frame {u t t' : BeaconState} {a : _} {slot : Slot}
    (h : (EthCLSpecs.Heze.getPtc (StateTransition := HezeRun) (pureState u) slot).run
      (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getIndexedPayloadAttestation` reads the state only. -/
@[frame] theorem getIndexedPayloadAttestation_frame {u t t' : BeaconState} {a : _}
    {pa : EthCLSpecs.Heze.PayloadAttestation}
    (h : (EthCLSpecs.Heze.getIndexedPayloadAttestation (StateTransition := HezeRun)
      (pureState u) pa).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `processPayloadAttestation` reads the state only. -/
@[frame] theorem processPayloadAttestation_frame {t t' : BeaconState} {a : PUnit}
    {pa : EthCLSpecs.Heze.PayloadAttestation}
    (h : (EthCLSpecs.Heze.processPayloadAttestation (StateTransition := HezeRun) pa).run
      (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps the tracked fields. -/
@[frame] theorem queueExcessActiveBalance_frame {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps the tracked fields. -/
@[frame] theorem switchToCompoundingValidator_frame {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps the tracked fields. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps the tracked fields. -/
@[frame] theorem initiateBuilderExit_frame {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps the tracked fields. -/
@[frame] theorem addBuilderToRegistry_frame {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps the tracked fields. -/
@[frame] theorem processDepositRequest_frame {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps the tracked fields. -/
@[frame] theorem processWithdrawalRequest_frame {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps the tracked fields. -/
@[frame] theorem processConsolidationRequest_frame {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps the tracked fields. -/
@[frame] theorem processBuilderDepositRequest_frame {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps the tracked fields. -/
@[frame] theorem processBuilderExitRequest_frame {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps the spine fields. It writes one entry of the window and
the builder withdrawal queue. -/
@[frame] theorem settleBuilderPayment_frame_spine {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps the spine fields. It clears one entry of the window. -/
@[frame] theorem processProposerSlashing_frame_spine {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps the spine fields. It settles one entry of the
window and writes `latestBlockHash` and `executionPayloadAvailability`. The cached bid
stays. -/
@[frame] theorem applyParentExecutionPayload_frame_spine {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps the spine fields. -/
@[frame] theorem processParentExecutionPayload_frame_spine {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

/-- `isAttestationSameSlot` reads the state only. -/
@[frame] theorem isAttestationSameSlot_frame {u t t' : BeaconState} {a : _}
    {data : EthCLSpecs.Heze.AttestationData}
    (h : (EthCLSpecs.Heze.isAttestationSameSlot (StateTransition := HezeRun) (pureState u)
      data).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

/-- `getAttestationParticipationFlagIndices` reads the state only. -/
@[frame] theorem getAttestationParticipationFlagIndices_frame {u t t' : BeaconState} {a : _}
    {data : EthCLSpecs.Heze.AttestationData} {d : UInt64}
    (h : (EthCLSpecs.Heze.getAttestationParticipationFlagIndices (StateTransition := HezeRun)
      (pureState u) data d).run (pureState t) = .ok (a, pureState t')) :
    (pureState t').view = (pureState t).view := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps the spine fields. It writes the participation flags, one
entry of the window, and the balance of the proposer. The body threads the state through
two nested loops, next to counters. The inversion needs more than the default heartbeat
limit. -/
@[frame] theorem processAttestation_frame_spine {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
