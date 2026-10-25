import EthCLSpecs.Proofs.Heze.KeepsUncached.Block

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached.Epoch`: epoch processing keeps the uncached box

`processEpoch` runs seventeen substeps in order. This file proves `KeepsUncached` for each
substep, for the callees that write the state, and for `processEpoch`. All the bodies are
inherited from Fulu or Gloas.

Most substeps read the state, gate, and write through record updates or `appendState`,
and the `keeps_uncached` tactic closes them. Three shapes need more:

* A body that returns a box. `applyDeltas` threads a local state through a range loop and
  returns it, so its fact is `ReturnsUncached`.
* A body that feeds a returned box to `set`: `processRewardsAndPenalties`,
  `applyPendingDeposit` and the `pcLoop` step. The proof binds through `ReturnsUncached`
  first, so the box that `set` writes is known to be pure.
* A body that threads a local state through a loop of balance writes: `processSlashings`.
  The loop invariant says that the local state is pure (`IsPure`).

All the lemmas are supporting facts, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config Gwei Epoch BeaconState PendingDeposit
  PendingConsolidation BLSPubkey Bytes32
  getCurrentEpoch weighJustificationAndFinalization processJustificationAndFinalization
  processInactivityUpdates applyDeltas processRewardsAndPenalties processRegistryUpdates
  processSlashings addValidatorToRegistry applyPendingDeposit ppdLoop processPendingDeposits
  pcLoop processPendingConsolidations processEffectiveBalanceUpdates processSlashingsReset
  processRandaoMixesReset processEth1DataReset processHistoricalSummariesUpdate
  processParticipationFlagUpdates processSyncCommitteeUpdates processProposerLookahead
  processBuilderPendingPayments processPtcWindow processEpoch)
open EthCLLib.Proofs (pureState KeepsUncached ReturnsUncached keepsUncached_bind
  keepsUncached_get keepsUncached_ite keepsUncached_pure keepsUncached_liftErr
  keepsUncached_forIn_list keepsUncachedFrom_liftErr keepsUncachedFrom_ite
  keepsUncached_fuelLoop keepsUncached_get_bind keepsUncached_iff_forall_from
  keepsUncachedFrom_get_bind keepsUncachedFrom_bind keepsUncachedFrom_set
  keepsUncachedFrom_pure keepsUncachedFrom_forIn_range_bind_P returnsUncachedFrom_bind
  returnsUncached_bind IsPure returnsUncached_forIn_range returnsPureVia_bind_returns
  returnsPureVia_bind_keeps keepsUncached_foldlM_list
  returnsPureVia_pure step_of_returnsPureVia)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `getCurrentEpoch` keeps the flavour: one read and a pure return. -/
theorem keepsUncached_getCurrentEpoch :
    KeepsUncached (getCurrentEpoch (StateTransition := HezeRun)) := by
  unfold getCurrentEpoch
  keeps_uncached

/-- `weighJustificationAndFinalization` keeps the flavour: two block-root reads under
their gates, then one writer that branches on the justification bits. `is_pure` closes
that writer. -/
theorem keepsUncached_weighJustificationAndFinalization (total prev curr : Gwei) :
    KeepsUncached (weighJustificationAndFinalization (StateTransition := HezeRun) total prev
      curr) := by
  unfold weighJustificationAndFinalization
  keeps_uncached_using [keepsUncached_getBlockRoot _ _]

/-- `applyDeltas` returns a pure box when it starts from one: a range loop of balance
writes, each through `increaseBalance` and `decreaseBalance`, then the return of the
local state. -/
theorem returnsUncached_applyDeltas (rewards penalties : Array Gwei) (state : BeaconState) :
    ReturnsUncached (applyDeltas (StateTransition := HezeRun) rewards penalties
      (pureState state)) := by
  unfold applyDeltas
  refine returnsPureVia_bind_returns
    (returnsUncached_forIn_range _ (fun _ w => ?_) _ _ ⟨state, rfl⟩)
    (fun w => returnsPureVia_pure _ ⟨w, rfl⟩)
  exact returnsPureVia_bind_returns (returnsUncached_increaseBalance _ _ _)
    (fun w₁ => returnsPureVia_bind_returns (returnsUncached_decreaseBalance _ _ _)
      (fun w₂ => returnsPureVia_pure _ ⟨w₂, rfl⟩))

/-- `processJustificationAndFinalization` keeps the flavour: a read, a gate on the
epoch, then `weighJustificationAndFinalization`. -/
theorem keepsUncached_processJustificationAndFinalization :
    KeepsUncached (processJustificationAndFinalization (StateTransition := HezeRun)) := by
  unfold processJustificationAndFinalization
  keeps_uncached_using [keepsUncached_weighJustificationAndFinalization _ _ _]

/-- `processInactivityUpdates` keeps the flavour: a read, a gate, then one writer whose
`Id` loop runs over the eligible validators. `is_pure` closes that writer. -/
theorem keepsUncached_processInactivityUpdates :
    KeepsUncached (processInactivityUpdates (StateTransition := HezeRun)) := by
  unfold processInactivityUpdates
  keeps_uncached

/-- `processRewardsAndPenalties` keeps the flavour. After the read and the gate, each
loop step reads the state, runs `applyDeltas` on it, and writes the result back with
`set`. `returnsUncached_applyDeltas` says that the box `set` writes is pure. The final
inactivity step has the same shape. -/
theorem keepsUncached_processRewardsAndPenalties :
    KeepsUncached (processRewardsAndPenalties (StateTransition := HezeRun)) := by
  unfold processRewardsAndPenalties
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_liftErr _) (fun flagDeltas => ?_)
  refine keepsUncached_bind (keepsUncached_liftErr _) (fun inactPenalties => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_list _ (fun x _ => ?body) _ _) (fun _ => ?tail)
  case body =>
    rcases x with ⟨rewards, penalties⟩
    refine keepsUncached_get_bind (fun v => ?_)
    refine returnsUncachedFrom_bind (returnsUncached_applyDeltas _ _ _) (fun w w' => ?_)
    exact keepsUncachedFrom_bind (keepsUncachedFrom_set w' w)
      (fun _ w'' => keepsUncachedFrom_pure w'' _)
  case tail =>
    refine keepsUncached_get_bind (fun v => ?_)
    exact returnsUncachedFrom_bind (returnsUncached_applyDeltas _ _ _)
      (fun w w' => keepsUncachedFrom_set w' w)

/-- `processRegistryUpdates` keeps the flavour: two reads, then a range loop over the
validators. Each step reads the state, writes the eligibility and the activation, and
calls `initiateValidatorExit` for an ejection. -/
theorem keepsUncached_processRegistryUpdates :
    KeepsUncached (processRegistryUpdates (StateTransition := HezeRun)) := by
  unfold processRegistryUpdates
  keeps_uncached_using [keepsUncached_initiateValidatorExit _]

/-- `processSlashings` keeps the flavour. It reads the total balance, sums the slashings
with checked adds, and scales the sum with a checked product. None of these writes the
state. Then it reads the state into a local state, runs a range loop that applies
`decreaseBalance` to each slashed validator in the window, and writes the local state back
with `set`. The loop checks the window epoch and the penalty too. The loop invariant says that
the local state is pure. -/
theorem keepsUncached_processSlashings :
    KeepsUncached (processSlashings (StateTransition := HezeRun)) := by
  intro preState
  unfold processSlashings
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind (T := BeaconState)
    (keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _) (fun _ w₁ => ?_)
  refine keepsUncachedFrom_bind (keepsUncached_iff_forall_from.mp (by
      rw [← Array.foldlM_toList]
      exact keepsUncached_foldlM_list _ (fun _ _ => keepsUncached_checkedAdd _ _ _) _ _) _)
    (fun _ w₂ => ?_)
  refine keepsUncachedFrom_bind
    (keepsUncached_iff_forall_from.mp (keepsUncached_checkedMul _ _ _) _) (fun _ w₃ => ?_)
  refine keepsUncachedFrom_forIn_range_bind_P _ _ IsPure ?body ?tail _ _ ⟨state, rfl⟩
  · intro i b
    rintro v r s ⟨w, rfl⟩ hrun
    revert v r s hrun
    -- The `refine` unifies the action of `step_of_returnsPureVia` with the body that the
    -- goal names.
    refine step_of_returnsPureVia ?_
    dsimp only
    split
    · refine returnsPureVia_bind_keeps (keepsUncached_checkedAdd _ _ _) (fun _ => ?_)
      dsimp only
      split
      · exact returnsPureVia_bind_keeps (keepsUncached_checkedMul _ _ _)
          (fun _ => returnsPureVia_bind_returns (returnsUncached_decreaseBalance _ _ _)
            (fun w₁ => returnsPureVia_pure _ ⟨w₁, rfl⟩))
      · exact returnsPureVia_pure _ ⟨w, rfl⟩
    · exact returnsPureVia_pure _ ⟨w, rfl⟩
  · intro b w' hb
    obtain ⟨w, rfl⟩ := hb
    exact keepsUncachedFrom_set w' w

/-- `addValidatorToRegistry` keeps the flavour: a read, then five `setOrAppendState`
writes, one per registry list. -/
theorem keepsUncached_addValidatorToRegistry (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    KeepsUncached (addValidatorToRegistry (StateTransition := HezeRun) pubkey wc amount) := by
  unfold addValidatorToRegistry
  keeps_uncached

/-- `applyPendingDeposit` keeps the flavour. A known key tops up the balance: the
`increaseBalance` result is a pure box, which `set` writes. A new key with a valid
signature runs `addValidatorToRegistry`. -/
theorem keepsUncached_applyPendingDeposit (deposit : PendingDeposit) :
    KeepsUncached (applyPendingDeposit (StateTransition := HezeRun) deposit) := by
  unfold applyPendingDeposit
  refine keepsUncached_get_bind (fun v => ?_)
  split
  · exact returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
      (fun w w' => keepsUncachedFrom_set w' w)
  · refine keepsUncached_iff_forall_from.mp ?_ v
    keeps_uncached_using [keepsUncached_addValidatorToRegistry _ _ _]

/-- `ppdLoop` keeps the flavour: a `fuelLoop` whose step reads the state, gates, and
calls `applyPendingDeposit`. -/
theorem keepsUncached_ppdLoop (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei)
    (nextEpoch : Epoch) :
    KeepsUncached (ppdLoop (StateTransition := HezeRun) deposits finalizedSlot avail
      nextEpoch) := by
  unfold ppdLoop
  refine keepsUncached_fuelLoop _ _ (fun _ => ?_) _ _
  keeps_uncached_using [keepsUncached_applyPendingDeposit _]

/-- `processPendingDeposits` keeps the flavour: a read, `ppdLoop`, the checked list of
the remaining deposits, and one write. -/
theorem keepsUncached_processPendingDeposits :
    KeepsUncached (processPendingDeposits (StateTransition := HezeRun)) := by
  unfold processPendingDeposits
  keeps_uncached_using [keepsUncached_ppdLoop _ _ _ _]

/-- `pcLoop` keeps the flavour: a `fuelLoop` whose step reads the state and moves a
balance. The move returns a pure box through `decreaseBalance` and then
`increaseBalance`, and `set` writes it. -/
theorem keepsUncached_pcLoop (cons : Array PendingConsolidation) (nextEpoch : Epoch) :
    KeepsUncached (pcLoop (StateTransition := HezeRun) cons nextEpoch) := by
  unfold pcLoop
  refine keepsUncached_fuelLoop _ _ (fun npc => ?_) _ _
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_get_bind (fun v => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftErr _ _) (fun src w₁ => ?_)
  refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => ?_)
  refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftErr _ _) (fun srcBal w₂ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ _ _) (fun s₁ w₃ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _) (fun s₂ w₄ => ?_)
  exact keepsUncachedFrom_bind (keepsUncachedFrom_set w₄ s₂)
    (fun _ w₅ => keepsUncachedFrom_pure w₅ _)

/-- `processPendingConsolidations` keeps the flavour: a read, `pcLoop`, and one write. -/
theorem keepsUncached_processPendingConsolidations :
    KeepsUncached (processPendingConsolidations (StateTransition := HezeRun)) := by
  unfold processPendingConsolidations
  keeps_uncached_using [keepsUncached_pcLoop _ _]

/-- `processEffectiveBalanceUpdates` keeps the flavour: one writer whose `Id` loop runs
over the validators. `is_pure` closes that writer. -/
theorem keepsUncached_processEffectiveBalanceUpdates :
    KeepsUncached (processEffectiveBalanceUpdates (StateTransition := HezeRun)) := by
  unfold processEffectiveBalanceUpdates
  keeps_uncached

/-- `processSlashingsReset` keeps the flavour: `getCurrentEpoch`, then one write. -/
theorem keepsUncached_processSlashingsReset :
    KeepsUncached (processSlashingsReset (StateTransition := HezeRun)) := by
  unfold processSlashingsReset
  keeps_uncached_using [keepsUncached_getCurrentEpoch, keepsUncached_getRandaoMix _]

/-- `processRandaoMixesReset` keeps the flavour: `getCurrentEpoch` and `getRandaoMix`,
then one write. -/
theorem keepsUncached_processRandaoMixesReset :
    KeepsUncached (processRandaoMixesReset (StateTransition := HezeRun)) := by
  unfold processRandaoMixesReset
  keeps_uncached_using [keepsUncached_getCurrentEpoch, keepsUncached_getRandaoMix _]

/-- `processEth1DataReset` keeps the flavour: `getCurrentEpoch`, then one write at the
end of a voting period. -/
theorem keepsUncached_processEth1DataReset :
    KeepsUncached (processEth1DataReset (StateTransition := HezeRun)) := by
  unfold processEth1DataReset
  keeps_uncached_using [keepsUncached_getCurrentEpoch, keepsUncached_getRandaoMix _]

/-- `processHistoricalSummariesUpdate` keeps the flavour: `getCurrentEpoch`, then a read
and an `appendState` at the end of a historical period. -/
theorem keepsUncached_processHistoricalSummariesUpdate :
    KeepsUncached (processHistoricalSummariesUpdate (StateTransition := HezeRun)) := by
  unfold processHistoricalSummariesUpdate
  keeps_uncached_using [keepsUncached_getCurrentEpoch, keepsUncached_getRandaoMix _]

/-- `processParticipationFlagUpdates` keeps the flavour: a read, a checked list of
zero flags, and one write. -/
theorem keepsUncached_processParticipationFlagUpdates :
    KeepsUncached (processParticipationFlagUpdates (StateTransition := HezeRun)) := by
  unfold processParticipationFlagUpdates
  keeps_uncached

/-- `processSyncCommitteeUpdates` keeps the flavour: a read, then a `set` of the updated
state at a period boundary. -/
theorem keepsUncached_processSyncCommitteeUpdates :
    KeepsUncached (processSyncCommitteeUpdates (StateTransition := HezeRun)) := by
  unfold processSyncCommitteeUpdates
  keeps_uncached

/-- `processProposerLookahead` keeps the flavour: a read, then a `set` of the updated
state. -/
theorem keepsUncached_processProposerLookahead :
    KeepsUncached (processProposerLookahead (StateTransition := HezeRun)) := by
  unfold processProposerLookahead
  keeps_uncached

/-- `processBuilderPendingPayments` keeps the flavour: a read, a range loop with an
`appendState` for each payment over the quorum, and one write that shifts the window. -/
theorem keepsUncached_processBuilderPendingPayments :
    KeepsUncached (processBuilderPendingPayments (StateTransition := HezeRun)) := by
  unfold processBuilderPendingPayments
  keeps_uncached

/-- `processPtcWindow` keeps the flavour: a read, then one write that shifts the window. -/
theorem keepsUncached_processPtcWindow :
    KeepsUncached (processPtcWindow (StateTransition := HezeRun)) := by
  unfold processPtcWindow
  keeps_uncached

/-- `processEpoch` keeps the flavour: its seventeen substeps run in order, and each has a
lemma above. -/
theorem keepsUncached_processEpoch :
    KeepsUncached (processEpoch (StateTransition := HezeRun)) := by
  unfold processEpoch
  refine keepsUncached_bind keepsUncached_processJustificationAndFinalization (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processInactivityUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processRewardsAndPenalties (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processRegistryUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processSlashings (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processEth1DataReset (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processPendingDeposits (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processPendingConsolidations (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processBuilderPendingPayments (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processEffectiveBalanceUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processSlashingsReset (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processRandaoMixesReset (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processHistoricalSummariesUpdate (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processParticipationFlagUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processSyncCommitteeUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processProposerLookahead (fun _ => ?_)
  exact keepsUncached_processPtcWindow

end

end EthCLSpecs.Proofs.Heze
