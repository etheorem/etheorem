import EthCLSpecs.Gloas.Containers

/-!
# `EthCLSpecs.Gloas.EpochProcessing`: the inherited Fulu epoch substeps

The flagship of the fork-inheritance model (`SPEC_AUTHORING_MODEL.md` §4,
`SPECS_ARCHITECTURE.md` §4.1). Gloas's `BeaconState` carries every field the Fulu
epoch substeps read, so most substeps are `inherit`ed verbatim: each captured Fulu
`forkdef` is re-elaborated in the Gloas namespace against `Gloas.State`
(the plain `Gloas.BeaconState` record), with its sibling calls rebinding to the Gloas
copies. Gloas restates only the bodies its pinned text changes: the EIP-8061 churn
helpers, `slash_validator`, `get_next_sync_committee_indices`,
`get_beacon_proposer_indices`, `process_pending_deposits`, and
`process_participation_flag_updates`. The two shuffle-dependent substeps are
inherited too, after the committee layer. The Gloas-new substeps
`process_builder_pending_payments` and `process_ptc_window` close the file, with
their helpers.

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

-- Gloas (EIP-8061) churn: `get_exit_churn_limit` / `get_activation_churn_limit`
-- use `CHURN_LIMIT_QUOTIENT_GLOAS`, and `compute_exit_epoch_and_update_churn` uses
-- `get_exit_churn_limit` rather than Fulu's `get_activation_exit_churn_limit`. These
-- override the inherited Fulu versions; the inherited `initiateValidatorExit` binds to
-- this `computeExitEpochAndUpdateChurn`, and the restated `slashValidator` calls it.
/-- `get_exit_churn_limit` (`gloas/mainnet.py:7889-7898`): the Gloas quotient in
place of Fulu's, the checked `Gwei` chain as `getBalanceChurnLimit` ports it. -/
forkdef getExitChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.churnLimitQuotientGloas
  let churn := max Const.minPerEpochChurnLimitElectra scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  let limit ← churn - rounded
  return limit

/-- `get_activation_churn_limit` (`gloas/mainnet.py:7876-7886`): the rounded
churn capped at `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. -/
forkdef getActivationChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.churnLimitQuotientGloas
  let churn := max Const.minPerEpochChurnLimitElectra scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  let churn ← churn - rounded
  return min Const.maxPerEpochActivationChurnLimitGloas churn

forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  -- `max(state.earliest_exit_epoch, compute_activation_exit_epoch(get_current_epoch(state)))`:
  -- the exit epoch is the checked `Epoch` chain, bound before the `max` that reads it
  -- (`SPEC_ARITHMETIC.md` §4.3).
  let exitEpoch ← computeActivationExitEpoch currentEpoch
  let earliest := max (sszGet state earliestExitEpoch) exitEpoch
  let perEpochChurn ← liftErr (getExitChurnLimit state)
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
  let slashIdx ← epoch % Const.epochsPerSlashingsVectorC

  -- Mark slashed, extend withdrawability, record the effective balance in the
  -- slashings ring buffer, and apply the slashing penalty. The withdrawability
  -- extension is the pyspec's `max(validator.withdrawable_epoch, epoch +
  -- EPOCHS_PER_SLASHINGS_VECTOR)` checked `Epoch` add, bound before the store; the
  -- ring index is the checked modulo feeding the underlying-value projection the
  -- read and write cite (`SPEC_ARITHMETIC.md` §4.5).
  let extended ← epoch + Const.epochsPerSlashingsVectorC
  let withdrawable := max validator.withdrawableEpoch extended
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := withdrawable }
  let ringTotal ← vget (sszGet state slashings) slashIdx.toPlainNat + validator.effectiveBalance
  let state := sszUpdate state with
    slashings[slashIdx.toPlainNat]! := ringTotal
  let slashingPenalty ← validator.effectiveBalance / Const.minSlashingPenaltyQuotientElectra
  let state ← decreaseBalance state i slashingPenalty
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward ← validator.effectiveBalance / Const.whistleblowerRewardQuotientElectra
  let proposerReward ← whistleblowerReward * Const.proposerWeight / Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  let remainder ← whistleblowerReward - proposerReward
  set (← increaseBalance state proposerIdx remainder)

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
/-- `get_consolidation_churn_limit` (`gloas/mainnet.py:6678-6685`): the
EIP-7732 quotient, the checked `Gwei` chain as `getBalanceChurnLimit` ports it. -/
forkdef getConsolidationChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.consolidationChurnLimitQuotient
  let churn := scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  let limit ← churn - rounded
  return limit

inherit computeConsolidationEpochAndUpdateChurn
inherit queueExcessActiveBalance
inherit switchToCompoundingValidator
inherit getValidatorFromDeposit
inherit addValidatorToRegistry
inherit isValidDepositSignature
inherit applyPendingDeposit

-- Committee layer (forkdef-converted in Fulu, inherited verbatim over `Gloas.State`).
-- EIP-7732 changes none of the shuffle / seed / committee-assignment helpers, so the
-- selection of beacon committees is identical to Fulu. The sync-committee index draw below
-- moves to `compute_balance_weighted_selection`.
inherit computeShuffledPermutation
inherit getSeed
inherit getCommitteeCountPerSlot
inherit computeCommittee
inherit getBeaconCommittee
inherit getCommitteeIndices
inherit cbwsAux
inherit computeBalanceWeightedSelection
inherit computeProposerIndices

/-- `get_next_sync_committee_indices` (Gloas, `gloas/minimal.py:5055-5064`): the pyspec forms
the seed first, then the active set, and hands both to `compute_balance_weighted_selection`.
This overrides the Fulu loop. An empty active set rejects on the selection's
`assert total > 0`, the assert class, where Fulu raises `ZeroDivisionError`. The inherited
`getNextSyncCommittee` below late-binds its index draw to this Gloas copy. -/
forkdef getNextSyncCommitteeIndices (state : State) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch ← currentEpochOf state + 1
  let seed ← getSeed state epoch Const.domainSyncCommittee
  let active ← getActiveValidatorIndices state epoch
  computeBalanceWeightedSelection state active seed Const.syncCommitteeSize true

inherit getNextSyncCommittee

/-- `get_beacon_proposer_indices` (Gloas, EIP-8045): the proposer lookahead is drawn
only from *unslashed* active validators. This overrides the inherited Fulu version
(which has no slashed filter); the inherited `process_proposer_lookahead` below
late-binds its `getBeaconProposerIndices` call to this Gloas copy. When every active
validator is slashed, the candidate set is empty, and `compute_balance_weighted_selection`'s
`assert total > 0` rejects. The unslashed filter reads `state.validators[index]`, a raising
list read through `getAt`, before the seed, as the pinned comprehension does. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let validators := sszGet state validators
  let active ← getActiveValidatorIndices state epoch
  let indices ← active.filterM fun vi => do
    let validator ← liftErr (getAt validators vi)
    pure !validator.slashed
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

-- Gloas (EIP-8061) `process_pending_deposits` (`gloas/mainnet.py:6796-6850`): Fulu's body,
-- with one difference. The churn budget is `get_activation_churn_limit` (Gloas) rather than
-- the activation-exit one. The Electra eth1-bridge stop is gone, as in Fulu. The pending
-- queue is a progressive list, so the leftover array goes in whole: no
-- `PENDING_DEPOSITS_LIMIT` cap and no `.listFull` raise to mirror.
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  -- [Modified in Gloas:EIP8061] Deposits still consume the activation-only churn budget.
  let availableForProcessing ←
    (sszGet state depositBalanceToConsume) + (← liftErr (getActivationChurnLimit state))
  let mut processedAmount : Gwei := 0
  let mut nextDepositIndex := 0
  let mut depositsToPostpone : Array PendingDeposit := #[]
  let mut isChurnLimitReached := false
  let finalizedSlot ← computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let pendingDeposits := (sszGet state pendingDeposits).toArray

  for deposit in pendingDeposits do
    -- Check if deposit has been finalized, otherwise, stop processing.
    if deposit.slot > finalizedSlot then break
    -- Check if number of processed deposits has not reached the limit, otherwise, stop
    -- processing.
    if nextDepositIndex ≥ Const.maxPendingDepositsPerEpoch then break

    -- Read validator state. `apply_pending_deposit` can add a validator, so each
    -- deposit reads the current registry. An unknown pubkey leaves both flags false.
    let state ← get
    let (isValidatorExited, isValidatorWithdrawn) :=
      match validatorIndexByPubkey? state deposit.pubkey with
      | some vi =>
        -- `state.validators[ValidatorIndex(validator_pubkeys.index(deposit.pubkey))]`: the
        -- read is in range, because `findIdx?` returned `vi`. The cast is omitted and cannot
        -- raise. Gloas's registry is a `ProgressiveList` with no SSZ cap, but a Lean array of
        -- 8-byte entries holds fewer than `2^61` of them, so the position is below `2^64`.
        let validator := sszGet state validators[vi]!
        (decide (validator.exitEpoch < Const.farFutureEpoch),
          decide (validator.withdrawableEpoch < nextEpoch))
      | none => (false, false)

    if isValidatorWithdrawn then
      -- Deposited balance will never become active. Increase balance but do not consume
      -- churn.
      applyPendingDeposit deposit
    else if isValidatorExited then
      -- Validator is exiting, postpone the deposit until after withdrawable epoch.
      depositsToPostpone := depositsToPostpone.push deposit
    else
      -- Check if deposit fits in the churn, otherwise, do no more deposit processing in
      -- this epoch. The sum is the checked `Gwei` add, formed only in this branch.
      isChurnLimitReached := (← processedAmount + deposit.amount) > availableForProcessing
      if isChurnLimitReached then break
      -- Consume churn and apply deposit.
      processedAmount ← processedAmount + deposit.amount
      applyPendingDeposit deposit

    -- Regardless of how the deposit was handled, we move on in the queue.
    nextDepositIndex := nextDepositIndex + 1

  let remaining : ProgressiveList PendingDeposit :=
    ⟨pendingDeposits.extract nextDepositIndex ++ depositsToPostpone⟩
  -- Accumulate churn only if the churn limit has been hit. The checked subtraction forms
  -- only in that branch, as Python's does.
  let depositBalance : Gwei ←
    if isChurnLimitReached then availableForProcessing - processedAmount else pure 0
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := depositBalance

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
constructor, which raises `.listFull` past the cap. Gloas's `currentEpochParticipation`
is an uncapped progressive list at the pin, so the reset takes the array whole and
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

/-- `get_builder_payment_quorum_threshold` (`gloas/mainnet.py:7867-7873`):
`get_total_active_balance(state) // Uint64(SLOTS_PER_EPOCH) *
BUILDER_PAYMENT_THRESHOLD_NUMERATOR // BUILDER_PAYMENT_THRESHOLD_DENOMINATOR`. The
per-slot division takes the proved-total `PositiveDivisor` view; the product and
the fraction are the checked `Gwei` chain over the `Uint64` threshold constants,
each bound where the pyspec forms it. The total active balance reads the registry, so
the result also carries its `IndexError`. -/
forkdef getBuilderPaymentQuorumThreshold (state : State) : Except StateTransitionError Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let perSlotBalance := totalActiveBalance / Const.slotsPerEpochDiv
  let scaled ← perSlotBalance * Const.builderPaymentThresholdNumerator
  let quorum ← scaled / Const.builderPaymentThresholdDenominator
  return quorum

/-- `process_builder_pending_payments` (`gloas/beacon-chain.md:1719-1731`): for each of the previous
epoch's pending payments whose weight clears the quorum threshold, queue its
withdrawal directly; then shift the payment window down by `SLOTS_PER_EPOCH` and
pad with empties. No churn reservation. -/
forkdef processBuilderPendingPayments : StateTransition Unit := do
  let state ← get

  let quorum ← liftErr (getBuilderPaymentQuorumThreshold state)

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
  -- `sha256(get_seed(...) + uint_to_bytes(slot))`: the seed walk carries the checked
  -- `Epoch` chain, so it binds before the hash; the slot bytes are the raw word's codec
  -- bytes (`SPEC_ARITHMETIC.md` §4.5).
  let seedBytes ← getSeed state epoch Const.domainPtcAttester
  -- The slot bytes are the checked value's wire bytes: `uint64ToBytes` reads the
  -- underlying word, the codec boundary §4.5 asks each projection to name.
  let seed := sha (seedBytes ++ uint64ToBytes slot.val)
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  -- The committees concatenate in slot order, each `get_beacon_committee` bound as it
  -- forms; the first rejecting slot surfaces (§4.3). `toPlainNat`: `range(committees_per_slot)`
  -- iterates the plain positions below the checked count, which its value names.
  let indices ← (Array.range committeesPerSlot.toPlainNat).foldlM
    (fun acc i => do
      -- `CommitteeIndex(i)`: the pyspec's checked cast of the plain loop variable.
      let committeeIndex ← CLUint64.ofNat? i
      let committee ← getBeaconCommittee state slot committeeIndex
      pure (acc ++ committee))
    (#[] : Array ValidatorIndex)
  let sel ← computeBalanceWeightedSelection state indices seed Const.ptcSize false
  return Vector.ofFn (fun i : Fin Const.ptcSize => sel[i.val]!)

/-- `process_ptc_window` (EIP-7732, `gloas/beacon-chain.md:1737-1748`): shift the cached PTC window down
by `SLOTS_PER_EPOCH` and recompute the last epoch's per-slot PTCs from the snapshot
state. The window length is `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH = 3 *
SLOTS_PER_EPOCH` (MIN_SEED_LOOKAHEAD = 1). The per-slot PTCs are computed in slot order,
so the run surfaces the first slot whose `compute_ptc` rejects. -/
forkdef processPtcWindow : StateTransition Unit := do
  let state ← get
  -- `get_current_epoch(state) + MIN_SEED_LOOKAHEAD + 1`: the checked `Epoch` chain, tested
  -- per operation and bound once (`SPEC_ARITHMETIC.md` §4.3).
  let nextEpoch ← currentEpochOf state + Const.minSeedLookahead + 1
  let startSlot ← computeStartSlotAtEpoch nextEpoch
  -- `range(start_slot, start_slot + SLOTS_PER_EPOCH)` (`gloas/minimal.py:7934-7936`) forms
  -- the checked `Slot + Slot` range end once, before any `compute_ptc`, so a range fault
  -- there precedes every committee read.
  let _rangeEnd ← startSlot + Const.slotsPerEpochC
  -- The comprehension then runs `compute_ptc(state, Slot(slot))` in slot order, so the run
  -- surfaces the first slot whose `compute_ptc` rejects. Python iterates plain ints below the
  -- range end, where `Slot(slot)` cannot fault. Lean forms each slot as the checked
  -- `start_slot + i`. That add cannot fault either, since `i < SLOTS_PER_EPOCH` keeps it below
  -- the range end just bound.
  let fresh : Array (Vector ValidatorIndex Const.ptcSize) ← liftErr
    ((Array.range Const.slotsPerEpoch).mapM (fun i => do
      let slot ← startSlot + i
      computePtc state slot))

  modifyState fun state =>
    sszUpdate state with ptcWindow :=
      -- `keep` is the window minus the shifted-out epoch:
      -- `(MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH`.
      shiftWindow (sszGet state ptcWindow) Const.slotsPerEpoch
        ((Const.minSeedLookahead.toPlainNat + 1) * Const.slotsPerEpoch)
        (fun k => fresh[k]!)

end

end EthCLSpecs.Gloas
