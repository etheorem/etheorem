import EthCLSpecs.Gloas.Containers

/-!
# `EthCLSpecs.Gloas.EpochProcessing`: the inherited Fulu epoch substeps

The flagship of the fork-inheritance model (`SPEC_AUTHORING_MODEL.md` §4,
`SPECS_ARCHITECTURE.md` §4.1). Gloas's `BeaconState` carries every field the Fulu
epoch substeps read, and EIP-7732 changes none of those substeps' bodies, so they
are `inherit`ed verbatim: each captured Fulu `forkdef` is re-elaborated in the
Gloas namespace against `Gloas.State` (`= SSZ.Box _ Gloas.BeaconState`), with its
sibling calls rebinding to the Gloas copies. No substep body is restated.

The two shuffle-dependent substeps (`process_sync_committee_updates`,
`process_proposer_lookahead`) and the Gloas-new `process_builder_pending_payments`
are not inherited: the committee / proposer helpers are plain `def`s bound to
`Fulu.State`, and the builder-payment substep is an ePBS addition. They stay
`todo` in the Gloas interface.

The `inherit` order is the Fulu load order (the `Time` … `Deposits` concern files,
then `Committees` and `EpochProcessing`), so every body's dependencies are already
in the Gloas namespace when it is replayed.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

state_section

-- Time / RANDAO accessors.
inherit computeEpochAtSlot
inherit computeStartSlotAtEpoch
inherit getCurrentEpoch
inherit getPreviousEpoch
inherit secondsToMilliseconds millisecondsToSeconds
inherit computeTimeAtSlotMs computeSlotAtTimeMs
inherit computeTimeAtSlot computeSlotAtTime
inherit BlobParameters getBlobParameters
inherit getRandaoMix

-- Balance / validator mutators, accessors, predicates.
inherit modBalance
inherit increaseBalance
inherit decreaseBalance
inherit modValidator
inherit computeActivationExitEpoch
inherit currentEpochOf
inherit previousEpochOf
inherit getBeaconProposerIndex
inherit getBlockRootAtSlot
inherit getBlockRoot
inherit isActiveValidator
inherit isSlashableValidator
inherit isEligibleForActivationQueue
inherit isEligibleForActivation
inherit credPrefix
inherit hasEth1WithdrawalCredential
inherit hasCompoundingWithdrawalCredential
inherit hasExecutionWithdrawalCredential
inherit getMaxEffectiveBalance
inherit hasNotInitiatedExit
inherit passedShardCommitteePeriod
inherit getActiveValidatorIndices
inherit getTotalBalance
inherit getTotalActiveBalance
inherit getBaseRewardPerIncrement
inherit getBaseReward
inherit getUnslashedParticipatingIndices
inherit getEligibleValidatorIndices
inherit validatorIndexByPubkey?
inherit getFinalityDelay
inherit isInInactivityLeak
inherit getBalanceChurnLimit
inherit getActivationExitChurnLimit

-- The churn reservation helper the two overrides below call.
inherit reserveChurn

-- Gloas (EIP-8061) churn: `get_exit_churn_limit` / `get_activation_churn_limit` are
-- derived through `CHURN_LIMIT_QUOTIENT_GLOAS` and override the inherited Fulu versions;
-- `compute_exit_epoch_and_update_churn` uses `get_exit_churn_limit` rather than Fulu's
-- capped `get_activation_exit_churn_limit`. `initiateValidatorExit`/`slashValidator`
-- (inherited below) bind to this `computeExitEpochAndUpdateChurn`.
/-- `get_exit_churn_limit` (`gloas/beacon-chain.md:1461-1472`): the EIP-8061 per-epoch exit
churn, uncapped, rounded to `EFFECTIVE_BALANCE_INCREMENT`. Supersedes the inherited Fulu
`getActivationExitChurnLimit` (which caps at `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`) in
the exit path; the `computeExitEpochAndUpdateChurn` below binds to this copy. -/
forkdef getExitChurnLimit (state : State) : Checked Gwei := do
  let churn := max Const.minPerEpochChurnLimitElectra
    (← getTotalActiveBalance state / Const.churnLimitQuotientGloas.toNat)
  churn - churn % Const.effectiveBalanceIncrementG

/-- `get_activation_churn_limit` (`gloas/beacon-chain.md:1445-1456`): the same rounded churn,
capped at `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. Supersedes the inherited Fulu
`getActivationExitChurnLimit` in the deposit path; `processPendingDeposits` below binds to
this copy. -/
forkdef getActivationChurnLimit (state : State) : Checked Gwei := do
  let churn := max Const.minPerEpochChurnLimitElectra
    (← getTotalActiveBalance state / Const.churnLimitQuotientGloas.toNat)
  return min Const.maxPerEpochActivationChurnLimitGloas
    (← churn - churn % Const.effectiveBalanceIncrementG)

/-- `compute_exit_epoch_and_update_churn` (`gloas/beacon-chain.md:1495-1518`, modified in
Gloas:EIP8061): reserve exit churn against the uncapped `get_exit_churn_limit`; the
reservation arithmetic is the shared `reserveChurn`. Overrides the inherited Fulu version,
whose per-epoch churn is the capped `getActivationExitChurnLimit`. -/
forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let exitCandidate ← computeActivationExitEpoch currentEpoch
  let earliest := max (sszGet state earliestExitEpoch) exitCandidate
  let perEpochChurn ← getExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)

  let (ee, ebtc) ← reserveChurn exitBalance consume perEpochChurn earliest
  let remaining ← ebtc - exitBalance
  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := remaining, earliestExitEpoch := ee
  return ee

inherit initiateValidatorExit
/-- `slash_validator` (Gloas, `gloas/beacon-chain.md:1549-1581`): Fulu's slashing, then the
EIP-7732 cleanup. Every pending builder payment whose recorded proposer is the slashed
validator is voided, across both epochs of the payment window.

v1.7.0-beta.4 moves the cleanup here from `process_proposer_slashing` and widens it. alpha.12
voided only the one payment at the slashed proposal's slot, and only on the proposer-slashing
path. Now every path that slashes a validator (proposer and attester slashings alike) voids
every payment the validator proposed. The Fulu body is restated because the spec restates it;
`whistleblower_index` defaults to the proposer, as the spec's `None` does. -/
forkdef slashValidator (i : ValidatorIndex) : StateTransition Unit := do
  let epoch := computeEpochAtSlot (sszGet (← get) slot)
  initiateValidatorExit i
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i
  let slashIdx := umodIdx epoch Const.epochsPerSlashingsVector

  -- Mark slashed, extend withdrawability, record the effective balance in the
  -- slashings ring buffer, and apply the slashing penalty. The withdrawability sum is the
  -- checked `epoch + EPOCHS_PER_SLASHINGS_VECTOR`, bound where the pyspec's assignment forms it.
  let withdrawableAt ← epoch + Const.epochsPerSlashingsVector
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := max validator.withdrawableEpoch withdrawableAt }
  let slashed ← vget (sszGet state slashings) slashIdx + validator.effectiveBalance
  let state := sszUpdate state with slashings[slashIdx]! := slashed
  let state ← decreaseBalance state i (← validator.effectiveBalance / Const.minSlashingPenaltyQuotientElectra)
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward ← validator.effectiveBalance / Const.whistleblowerRewardQuotientElectra
  let proposerReward ← whistleblowerReward * Const.proposerWeight / Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  set (← increaseBalance state proposerIdx (← whistleblowerReward - proposerReward))

  -- [New in Gloas:EIP7732] Void the pending builder payments for blocks the slashed
  -- validator proposed. `default` is the all-zero `BuilderPendingPayment.empty()`.
  let empty : BuilderPendingPayment := default
  modifyState fun state => Id.run do
    let mut state := state
    for paymentIndex in [0:2 * Const.slotsPerEpoch] do
      if (vget (sszGet state builderPendingPayments) paymentIndex).proposerIndex == i then
        state := sszUpdate state with builderPendingPayments[paymentIndex]! := empty
    return state
inherit getDomain
inherit getPendingBalanceToWithdraw

-- Gloas (EIP-8061) consolidation churn: `total_active // CONSOLIDATION_CHURN_LIMIT_QUOTIENT`
-- (no `MIN` floor, no balance-churn subtraction). Overrides the inherited Fulu
-- version; the inherited `computeConsolidationEpochAndUpdateChurn` below binds to it.
/-- `get_consolidation_churn_limit` (`gloas/beacon-chain.md:1479-1487`): the Gloas churn is
derived directly from the total active balance through `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`.
Overrides the inherited Fulu version (which subtracts the exit churn from the balance churn
limit); the inherited `computeConsolidationEpochAndUpdateChurn` binds to this copy. -/
forkdef getConsolidationChurnLimit (state : State) : Checked Gwei := do
  let churn := (← getTotalActiveBalance state / Const.consolidationChurnLimitQuotient.toNat)
  churn - churn % Const.effectiveBalanceIncrementG

inherit computeConsolidationEpochAndUpdateChurn
inherit queueExcessActiveBalance
inherit switchToCompoundingValidator
inherit getValidatorFromDeposit
inherit addValidatorToRegistry
inherit isValidDepositSignature
inherit applyPendingDeposit

-- Committee layer (forkdef-converted in Fulu, inherited verbatim over `Gloas.State`).
-- EIP-7732 changes none of the shuffle / seed / committee-assignment helpers, so the
-- selection of beacon committees and the sync committee is identical to Fulu.
inherit computeShuffledPermutation
inherit getSeed
inherit getCommitteeCountPerSlot
inherit computeCommittee
inherit getBeaconCommittee
inherit getCommitteeIndices
inherit cbwsAux
inherit computeBalanceWeightedSelection
inherit computeProposerIndices
inherit getNextSyncCommittee

/-- `get_beacon_proposer_indices` (Gloas, EIP-8045): the proposer lookahead is drawn
only from *unslashed* active validators. This overrides the inherited Fulu version
(which has no slashed filter); the inherited `process_proposer_lookahead` below
late-binds its `getBeaconProposerIndices` call to this Gloas copy. When every active
validator is slashed, the candidate set is empty, and `compute_balance_weighted_selection`'s
`assert total > 0` rejects. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let validators := sszGet state validators
  let indices := (getActiveValidatorIndices state epoch).filter (fun vi => !(validators[vi.toPlainInt]!).slashed)
  -- The seed binds where the pyspec assigns it (`gloas/beacon-chain.md:1304`).
  let seed ← getSeed state epoch Const.domainBeaconProposer
  computeProposerIndices state epoch seed indices

-- Epoch substeps (all but the two shuffle-dependent ones).
inherit weighJustificationAndFinalization
inherit processJustificationAndFinalization
inherit processInactivityUpdates
inherit getFlagIndexDeltas
inherit getInactivityPenaltyDeltas
inherit applyDeltas
inherit processRewardsAndPenalties
inherit processRegistryUpdates
inherit processSlashings

-- Gloas (EIP-8061) `process_pending_deposits` (`gloas/beacon-chain.md:1659-1713`): Fulu's,
-- with one difference: the churn budget is `get_activation_churn_limit` (Gloas) rather
-- than the activation-exit one. Neither text at the pin carries the Electra eth1-bridge
-- stop (`deposit.slot > GENESIS_SLOT and state.eth1_deposit_index <
-- state.deposit_requests_start_index`); Fulu dropped it with the former deposit mechanism
-- (consensus-specs #4704, in the text since alpha.12).

/-- Gloas's `process_pending_deposits`: the Fulu scan on the activation-only churn budget. -/
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  let availableForProcessing ← (sszGet state depositBalanceToConsume) + getActivationChurnLimit state
  let mut processedAmount : Gwei := 0
  let mut nextDepositIndex : Nat := 0
  let mut depositsToPostpone : Array PendingDeposit := #[]
  let mut isChurnLimitReached := false
  let finalizedSlot ← computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch

  for deposit in (sszGet state pendingDeposits) do
    -- Check if deposit has been finalized, otherwise, stop processing.
    if deposit.slot > finalizedSlot then break

    -- Check if number of processed deposits has not reached the limit, otherwise, stop processing.
    if nextDepositIndex ≥ Const.maxPendingDepositsPerEpoch then break

    -- Read validator state
    let state ← get
    let mut isValidatorExited := false
    let mut isValidatorWithdrawn := false
    if let some vi := validatorIndexByPubkey? state deposit.pubkey then
      -- `vi` came from the registry scan itself, so the read cannot miss; the raising
      -- route keeps the read honest anyway.
      let validator ← sszGetIdx (sszGet state validators) vi
      isValidatorExited := validator.exitEpoch < Const.farFutureEpoch
      isValidatorWithdrawn := validator.withdrawableEpoch < nextEpoch

    if isValidatorWithdrawn then
      -- Deposited balance will never become active. Increase balance but do not consume churn
      applyPendingDeposit deposit
    else if isValidatorExited then
      -- Validator is exiting, postpone the deposit until after withdrawable epoch
      depositsToPostpone := depositsToPostpone.push deposit
    else
      -- Check if deposit fits in the churn, otherwise, do no more deposit processing in this epoch.
      if (← processedAmount + deposit.amount) > availableForProcessing then
        isChurnLimitReached := true
        break

      -- Consume churn and apply deposit.
      processedAmount := ← processedAmount + deposit.amount
      applyPendingDeposit deposit

    -- Regardless of how the deposit was handled, we move on in the queue.
    nextDepositIndex := nextDepositIndex + 1

  -- `pendingDeposits` is a progressive list at alpha.12, so the leftover array goes in
  -- whole: no `PENDING_DEPOSITS_LIMIT` cap, no `.listFull` raise to mirror.
  let remaining : ProgressiveList PendingDeposit :=
    ⟨(sszGet (← get) pendingDeposits).toArray.drop nextDepositIndex ++ depositsToPostpone⟩

  -- Accumulate churn only if the churn limit has been hit.
  let leftover : Gwei ← if isChurnLimitReached then availableForProcessing - processedAmount else pure 0
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := leftover

inherit pcLoop
inherit processPendingConsolidations
inherit processEffectiveBalanceUpdates
inherit processSlashingsReset
inherit processRandaoMixesReset
inherit processEth1DataReset
inherit processHistoricalSummariesUpdate

/-- `process_participation_flag_updates` (Gloas override of the Fulu substep): rotate
current participation into previous and reset current to all-zero flags, one per
validator. Fulu's body builds the zero flags through the capped `SSZList`
constructor, the raise #120 added; Gloas's `currentEpochParticipation` is an
uncapped progressive list at alpha.12, so the reset takes the array whole and
nothing can raise. Heze inherits this override. -/
forkdef processParticipationFlagUpdates : StateTransition Unit := do
  let state ← get
  let current := sszGet state currentEpochParticipation
  let count := (sszGet state validators).size
  let zeros : ProgressiveList ParticipationFlags :=
    ⟨Array.replicate count (0 : ParticipationFlags)⟩
  modifyState fun state =>
    sszUpdate state with
      previousEpochParticipation := current,
      currentEpochParticipation  := zeros

-- Shuffle-dependent substeps: now inheritable since the committee layer is in the
-- Gloas namespace. `processProposerLookahead`'s `getBeaconProposerIndices` call binds
-- to the Gloas EIP-8045 override above.
inherit processSyncCommitteeUpdates
inherit processProposerLookahead

/-! ## Gloas-new epoch substep (EIP-7732) -/

/-- `process_builder_pending_payments` (`gloas/beacon-chain.md:1719-1731`): for each of the previous
epoch's pending payments whose weight clears the quorum threshold
(`get_total_active_balance / SLOTS_PER_EPOCH * NUMERATOR / DENOMINATOR`, `>=`),
queue its withdrawal directly; then shift the payment window down by
`SLOTS_PER_EPOCH` and pad with empties. No churn reservation. -/
forkdef processBuilderPendingPayments : StateTransition Unit := do
  let state ← get

  -- Quorum threshold: `get_builder_payment_quorum_threshold`
  -- (`gloas/beacon-chain.md:1433-1440`):
  -- `get_total_active_balance // Uint64(SLOTS_PER_EPOCH) * NUMERATOR // DENOMINATOR`.
  -- The pyspec operands are checked `Uint64` values; here `SLOTS_PER_EPOCH` is a `Nat`
  -- preset constant and the numerator and denominator sit in raw `UInt64` constants, so
  -- all three run through the `Nat` operands (same zero-divisor raise, same quotient).
  let quorum ← (← getTotalActiveBalance state / Const.slotsPerEpoch)
    * Const.builderPaymentThresholdNumerator.toNat / Const.builderPaymentThresholdDenominator.toNat

  -- Queue the withdrawal of every previous-epoch payment whose weight clears the quorum.
  let payments := sszGet state builderPendingPayments
  for i in [0:Const.slotsPerEpoch] do
    let p := vget payments i
    if p.weight ≥ quorum then
      appendState builderPendingWithdrawals p.withdrawal

  -- Shift the payment window down by `SLOTS_PER_EPOCH` and pad with empties.
  let empty : BuilderPendingPayment := default
  modifyState fun state =>
    sszUpdate state with builderPendingPayments :=
      shiftWindow (sszGet state builderPendingPayments) Const.slotsPerEpoch Const.slotsPerEpoch
        (fun _ => empty)

/-- `compute_ptc` (EIP-7732, `gloas/beacon-chain.md:1266-1282`): the payload-timeliness committee for
`slot`, with possible duplicates. Concatenate every beacon committee for the slot in
order, then take a `PTC_SIZE` balance-weighted selection with no shuffle. The seed
mixes `DOMAIN_PTC_ATTESTER` and the slot. A slot whose committees are all empty (fewer
active validators than `SLOTS_PER_EPOCH`) rejects through
`compute_balance_weighted_selection`'s `assert total > 0`. -/
forkdef computePtc (state : State) (slot : Slot) :
    Except StateTransitionError (Vector ValidatorIndex Const.ptcSize) := do
  let epoch := computeEpochAtSlot slot
  -- The seed binds where the pyspec assigns it (`gloas/beacon-chain.md:1271`), and the
  -- slot serializes through its `val` projection, the SSZ iso read.
  let seed ← getSeed state epoch Const.domainPtcAttester
  let sd := sha (seed ++ uint64ToBytes slot.val)
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices ← (Array.range committeesPerSlot).foldlM
    (fun acc i => do let committee ← getBeaconCommittee state slot i; pure (acc ++ committee))
    (#[] : Array ValidatorIndex)
  let sel ← computeBalanceWeightedSelection state indices sd Const.ptcSize false
  return Vector.ofFn (fun i : Fin Const.ptcSize => sel[i.val]!)

/-- `process_ptc_window` (EIP-7732, `gloas/beacon-chain.md:1737-1748`): shift the cached PTC window down
by `SLOTS_PER_EPOCH` and recompute the last epoch's per-slot PTCs from the snapshot
state. The window length is `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH = 3 *
SLOTS_PER_EPOCH` (MIN_SEED_LOOKAHEAD = 1). The per-slot PTCs are computed in slot order,
so the run surfaces the first slot whose `compute_ptc` rejects. -/
forkdef processPtcWindow : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + Const.minSeedLookahead + 1
  let startSlot ← computeStartSlotAtEpoch nextEpoch
  let fresh : Array (Vector ValidatorIndex Const.ptcSize) ← liftErr
    ((Array.range Const.slotsPerEpoch).mapM (fun i => do
      -- `start_slot + i`, the checked `CLUint64` route; the same sum Fulu's
      -- `computeProposerIndices` loop binds per slot.
      let slotI ← startSlot + i
      computePtc state slotI))

  modifyState fun state =>
    sszUpdate state with ptcWindow :=
      shiftWindow (sszGet state ptcWindow) Const.slotsPerEpoch (2 * Const.slotsPerEpoch)
        (fun k => fresh[k]!)

end

end EthCLSpecs.Gloas
