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

-- Gloas (EIP-8061) churn: `get_exit_churn_limit` / `get_activation_churn_limit`
-- use `CHURN_LIMIT_QUOTIENT_GLOAS`, and `compute_exit_epoch_and_update_churn` uses
-- `get_exit_churn_limit` rather than Fulu's `get_activation_exit_churn_limit`. These
-- override the inherited Fulu versions; `initiateValidatorExit`/`slashValidator`
-- (inherited below) bind to this `computeExitEpochAndUpdateChurn`.
-- Each limit fails only where `get_total_active_balance` fails.
forkdef getExitChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let churn := umax Const.minPerEpochChurnLimitElectra
    ((← getTotalActiveBalance state) / Const.churnLimitQuotientGloas)
  pure (churn - churn % Const.effectiveBalanceIncrementG)

forkdef getActivationChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let churn := umax Const.minPerEpochChurnLimitElectra
    ((← getTotalActiveBalance state) / Const.churnLimitQuotientGloas)
  pure (umin Const.maxPerEpochActivationChurnLimitGloas (churn - churn % Const.effectiveBalanceIncrementG))

forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let activationExitEpoch ← liftErr (computeActivationExitEpoch currentEpoch)
  let earliest := umax (sszGet state earliestExitEpoch) activationExitEpoch
  let perEpochChurn ← liftErr (getExitChurnLimit state)
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)
  let (ee, ebtc) ← liftErr (reserveChurn exitBalance consume perEpochChurn earliest)
  let remaining ← checkedSub ebtc exitBalance
    "compute_exit_epoch_and_update_churn: exit_balance_to_consume - exit_balance"

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
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  let slashIdx := umodIdx epoch Const.epochsPerSlashingsVector

  -- Mark slashed, extend withdrawability, record the effective balance in the
  -- slashings ring buffer, and apply the slashing penalty. The epoch sum and the
  -- slashings sum are checked `uint64` adds, in the pyspec's order.
  let slashedEpoch ← checkedAdd epoch (UInt64.ofNat Const.epochsPerSlashingsVector)
    "slash_validator: epoch + EPOCHS_PER_SLASHINGS_VECTOR"
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := umax validator.withdrawableEpoch slashedEpoch }
  let slashed ← checkedAdd (vget (sszGet state slashings) slashIdx) validator.effectiveBalance
    "slash_validator: state.slashings[epoch % EPOCHS_PER_SLASHINGS_VECTOR] + effective_balance"
  let state := sszUpdate state with slashings[slashIdx]! := slashed
  let state ← decreaseBalance state i (validator.effectiveBalance / UInt64.ofNat Const.minSlashingPenaltyQuotientElectra)
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward := validator.effectiveBalance / UInt64.ofNat Const.whistleblowerRewardQuotientElectra
  let proposerReward := whistleblowerReward * UInt64.ofNat Const.proposerWeight / UInt64.ofNat Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  set (← increaseBalance state proposerIdx (whistleblowerReward - proposerReward))

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
forkdef getConsolidationChurnLimit (state : State) : Except StateTransitionError Gwei := do
  let churn := (← getTotalActiveBalance state) / Const.consolidationChurnLimitQuotient
  pure (churn - churn % Const.effectiveBalanceIncrementG)

inherit computeConsolidationEpochAndUpdateChurn
inherit queueExcessActiveBalance
inherit switchToCompoundingValidator
inherit getValidatorFromDeposit
inherit addValidatorToRegistry
inherit isValidDepositSignature
inherit applyPendingDeposit

-- Committee layer (forkdef-converted in Fulu, inherited verbatim over `Gloas.State`).
-- EIP-7732 changes none of the shuffle / seed / committee-assignment helpers, so the
-- selection of beacon committees is identical to Fulu. The proposer and sync-committee
-- selection is new below: Gloas replaces Electra's loops with
-- `compute_balance_weighted_selection`.
inherit computeShuffledPermutation
inherit seedOf
inherit getSeed
inherit getCommitteeCountPerSlot
inherit computeCommittee
inherit getBeaconCommittee
inherit getCommitteeIndices

/-- `compute_balance_weighted_selection` inner loop (`gloas/beacon-chain.md:1217-1229`), one
call per pass of the spec's `while len(selected) < size`. The size check exits first, and the
tail increment runs the spec's `uint64` `i += 1` through `checkedSucc`, so the last pass at
`i = 2**64 - 1` throws `.arithmetic`, the spec's overflow, whether or not it filled the
selection.

The pyspec checks two products as `uint64` arithmetic, in this order in each iteration:
`effective_balance * MAX_RANDOM_VALUE`, then `MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`
after the read of `random_value`. A product at or above `2 ^ 64` raises `.arithmetic`. The
second product overflows only when the `Preset` field `MAX_EFFECTIVE_BALANCE_ELECTRA` is large. -/
forkdef cbwsAux [Preset] (indices effBals : Array Nat) (perm : Array ValidatorIndex)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) (i : Nat) (randomBytes : ByteArray)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  if selected.size ≥ size then pure selected
  else
    let offset := (i % 16) * 2
    let randomBytes := if offset == 0 then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else randomBytes
    let nextIndex := if shuffle then (perm[i % total]!).toNat else i % total
    let weight := effBals[nextIndex]! * Const.maxRandomValue
    if 2 ^ 64 ≤ weight then
      throwArithmetic "compute_balance_weighted_selection: effective_balance * MAX_RANDOM_VALUE"
    let randomValue := le2 randomBytes offset
    let threshold := Const.maxEffectiveBalanceElectra * randomValue
    if 2 ^ 64 ≤ threshold then
      throwArithmetic "compute_balance_weighted_selection: MAX_EFFECTIVE_BALANCE_ELECTRA * random_value"
    let selected := if weight ≥ threshold then selected.push (UInt64.ofNat (indices[nextIndex]!)) else selected
    let s ← checkedSucc i "compute_balance_weighted_selection: i += 1 past 2**64 - 1"
    cbwsAux indices effBals perm seed total size shuffle s.val randomBytes selected
termination_by counterBudgetUInt64 i

/-- `compute_balance_weighted_selection(state, indices, seed, size, shuffle)`
(`gloas/beacon-chain.md:1198-1230`). An empty `indices` rejects on the spec's
`assert total > 0` (`:1213`). The spec then reads every candidate's effective balance up
front, so an index past the registry raises `IndexError` (`sszGetIdx`, `.outOfBounds`) before
the loop, whether or not the loop would reach it. With `shuffle_indices`, each iteration calls
`compute_shuffled_index`. So the shuffle runs, and can fault, only when the loop runs at
least once, which needs `size > 0`. -/
forkdef computeBalanceWeightedSelection (state : State) (indices : Array ValidatorIndex)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let total := indices.size
  assert (total > 0)
  let idxNat := indices.map (·.toNat)
  let validators := sszGet state validators
  let effBals ← indices.mapM (fun vi => do
    let v ← sszGetIdx validators vi.toNat
    pure v.effectiveBalance.toNat)
  let perm ← if shuffle && 0 < size then computeShuffledPermutation total seed else pure #[]
  cbwsAux idxNat effBals perm seed total size shuffle 0 ByteArray.empty #[]

/-- `compute_proposer_indices` (Gloas, `gloas/beacon-chain.md:1240-1262`): one
`compute_balance_weighted_selection(…, size=1, shuffle_indices=True)` per slot of `epoch`,
each on its own seed. An empty `indices` rejects through the selection's `assert total > 0`.
`start_slot + i` cannot wrap, as in Fulu's body. The loop stops at the first selection that
raises, as the pyspec list comprehension does. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  let startSlot ← computeStartSlotAtEpoch epoch
  (Array.range Const.slotsPerEpoch).mapM (fun i => do
    let sd := sha (seed ++ uint64ToBytes (startSlot + UInt64.ofNat i))
    return (← computeBalanceWeightedSelection state indices sd 1 true)[0]!)

/-- `get_next_sync_committee` (Gloas). The selection is `compute_balance_weighted_selection`
(`gloas/beacon-chain.md:1315-1325`). Its `assert total > 0` rejects an empty active set with
`.assert`. This declaration overrides Fulu's body, which raises Electra's
`ZeroDivisionError` for an empty active set. `get_current_epoch(state) + 1` is a checked
`uint64` add, and `get_seed` can raise, before the selection runs. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let epoch ← checkedAdd (currentEpochOf state) 1 "get_next_sync_committee_indices: get_current_epoch(state) + 1"
  let seed ← getSeed state epoch Const.domainSyncCommittee
  let indices ← computeBalanceWeightedSelection state (getActiveValidatorIndices state epoch)
    seed Const.syncCommitteeSize true

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toNat]?.getD default).pubkey)
  pure { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

/-- `get_beacon_proposer_indices` (Gloas, EIP-8045): the proposer lookahead is drawn
only from *unslashed* active validators. This overrides the inherited Fulu version
(which has no slashed filter); the inherited `process_proposer_lookahead` below
late-binds its `getBeaconProposerIndices` call to this Gloas copy. When every active
validator is slashed, the candidate set is empty, and `compute_balance_weighted_selection`'s
`assert total > 0` rejects. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let validators := sszGet state validators
  let indices := (getActiveValidatorIndices state epoch).filter (fun vi => !(validators[vi.toNat]!).slashed)
  computeProposerIndices state epoch (← getSeed state epoch Const.domainBeaconProposer) indices

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
-- with two differences. The churn budget is `get_activation_churn_limit` (Gloas) rather than
-- the activation-exit one, and the Electra eth1-bridge stop (`deposit.slot > GENESIS_SLOT and
-- state.eth1_deposit_index < state.deposit_requests_start_index`) is gone; the Gloas text has
-- no such check at either alpha.12 or beta.4. `DepositScan` (the scan's record state and
-- result) is the Fulu one, replayed here.
inherit DepositScan

forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei) (nextEpoch : Epoch) :
    StateTransition DepositScan :=
  -- Fuel rather than a measure, for the reason Fulu's `ppdLoop` records (§7.2): the scan
  -- stops on a data-dependent guard rather than on a decreasing quantity.
  -- Fuel is `deposits.size + 1`: the `ndi ≥ deposits.size` guard returns `.done` one step
  -- before exhaustion, so `fuelLoop`'s `exhausted` value is unreachable.
  fuelLoop (deposits.size + 1) ({} : DepositScan) ({} : DepositScan) fun s => do
    if s.ndi ≥ deposits.size then return .done s
    let state ← get
    let deposit := deposits[s.ndi]!

    -- Stop the scan early: the deposit is not finalized, or this epoch's deposit cap is
    -- reached.
    if deposit.slot > finalizedSlot then return .done s
    if s.ndi ≥ Const.maxPendingDepositsPerEpoch then return .done s

    -- Advance past this deposit, carrying the running churn and postpone list forward.
    let advance (processed : Gwei) (postpone : Array PendingDeposit) : Step DepositScan DepositScan :=
      .next { s with ndi := s.ndi + 1, processed, postpone }

    -- Read the deposit's validator once, if its pubkey is known, and derive the two flags
    -- the spec branches on. An unknown pubkey leaves both false, so it falls through to the
    -- churn check.
    let (isWithdrawn, isExited) := match validatorIndexByPubkey? state deposit.pubkey with
      | some vi =>
        let v := sszGet state validators[vi]!
        (decide (v.withdrawableEpoch < nextEpoch), decide (v.exitEpoch < Const.farFutureEpoch))
      | none => (false, false)

    if isWithdrawn then applyPendingDeposit deposit; return advance s.processed s.postpone
    else if isExited then return advance s.processed (s.postpone.push deposit)
    else
      -- `processed_amount + deposit.amount` adds `Gwei` values, a checked `uint64` add.
      let total ← checkedAdd s.processed deposit.amount
        "process_pending_deposits: processed_amount + deposit.amount"
      if total > avail then return .done { s with churnReached := true }
      else applyPendingDeposit deposit; return advance total s.postpone

/-- `process_pending_deposits` (Gloas, EIP-8061). `deposit_balance_to_consume + churn` is a
checked `uint64` add, as in Fulu. -/
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let churn ← liftErr (getActivationChurnLimit state)
  let avail ← checkedAdd (sszGet state depositBalanceToConsume) churn
    "process_pending_deposits: deposit_balance_to_consume + get_activation_churn_limit"
  let finalizedSlot ← liftErr (computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch)
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  -- `pendingDeposits` is a progressive list at alpha.12, so the leftover array goes in
  -- whole: no `PENDING_DEPOSITS_LIMIT` cap, no `.listFull` raise to mirror.
  let remaining : ProgressiveList PendingDeposit :=
    ⟨deposits.extract scan.ndi deposits.size ++ scan.postpone⟩
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := if scan.churnReached then avail - scan.processed else 0

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

  -- Quorum threshold (`get_builder_payment_quorum_threshold`): `get_total_active_balance //
  -- SLOTS_PER_EPOCH * NUMERATOR // DENOMINATOR`. The total read and the product can raise.
  -- The product overflows when `SLOTS_PER_EPOCH` is small next to the total.
  let perSlotBalance := (← liftErr (getTotalActiveBalance state)) / UInt64.ofNat Const.slotsPerEpoch
  let quorumNumerator ← checkedMul perSlotBalance Const.builderPaymentThresholdNumerator
    "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR"
  let quorum := quorumNumerator / Const.builderPaymentThresholdDenominator

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
`compute_balance_weighted_selection`'s `assert total > 0`. Each `get_beacon_committee` can
raise, in committee order. -/
forkdef computePtc (state : State) (slot : Slot) :
    Except StateTransitionError (Vector ValidatorIndex Const.ptcSize) := do
  let epoch := computeEpochAtSlot slot
  let seed := sha ((← getSeed state epoch Const.domainPtcAttester) ++ uint64ToBytes slot)
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices ← (Array.range committeesPerSlot).foldlM
    (fun acc i => do pure (acc ++ (← getBeaconCommittee state slot i))) (#[] : Array ValidatorIndex)
  let sel ← computeBalanceWeightedSelection state indices seed Const.ptcSize false
  return Vector.ofFn (fun i : Fin Const.ptcSize => sel[i.val]!)

/-- `process_ptc_window` (EIP-7732, `gloas/beacon-chain.md:1737-1748`): shift the cached PTC window down
by `SLOTS_PER_EPOCH` and recompute the last epoch's per-slot PTCs from the snapshot
state. The window length is `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH = 3 *
SLOTS_PER_EPOCH` (MIN_SEED_LOOKAHEAD = 1). The per-slot PTCs are computed in slot order,
so the run surfaces the first slot whose `compute_ptc` rejects.

The body writes twice. The pyspec shifts the window in place before
`compute_start_slot_at_epoch`, the range end and `compute_ptc` can raise. So when one of them
raises, the state keeps the shifted window with the old last epoch, in the pyspec and here. -/
forkdef processPtcWindow : StateTransition Unit := do
  let state ← get
  let old := sszGet state ptcWindow
  set (sszUpdate state with ptcWindow :=
    shiftWindow old Const.slotsPerEpoch (2 * Const.slotsPerEpoch)
      (fun k => vget old (2 * Const.slotsPerEpoch + k)))

  let state ← get
  let nextEpoch := currentEpochOf state + Const.minSeedLookahead + 1
  let startSlot ← liftErr (computeStartSlotAtEpoch nextEpoch)
  -- pyspec forms the range end `start_slot + SLOTS_PER_EPOCH` as a `Slot` before the first
  -- `compute_ptc` call. A range end of `2^64` raises here.
  let _ ← checkedAdd startSlot (UInt64.ofNat Const.slotsPerEpoch)
    "process_ptc_window: start_slot + SLOTS_PER_EPOCH"
  let fresh : Array (Vector ValidatorIndex Const.ptcSize) ← liftErr <|
    (Array.range Const.slotsPerEpoch).mapM (fun i => computePtc state (startSlot + UInt64.ofNat i))

  modifyState fun state =>
    sszUpdate state with ptcWindow :=
      shiftWindow (sszGet state ptcWindow) 0 (2 * Const.slotsPerEpoch) (fun k => fresh[k]!)

end

end EthCLSpecs.Gloas
