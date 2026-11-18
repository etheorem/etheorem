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
/-- `get_exit_churn_limit` (`gloas/mainnet.py:7889-7898`): the Gloas quotient in
place of Fulu's, the checked `Gwei` chain as `getBalanceChurnLimit` ports it. -/
forkdef getExitChurnLimit (state : State) : Checked Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.churnLimitQuotientGloasC
  let churn := max Const.minPerEpochChurnLimitElectra scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  churn - rounded

/-- `get_activation_churn_limit` (`gloas/mainnet.py:7876-7887`): the rounded
churn capped at `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. -/
forkdef getActivationChurnLimit (state : State) : Checked Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.churnLimitQuotientGloasC
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
  let validator ← sszGetIdx (sszGet state validators) i.toNat
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
/-- `get_consolidation_churn_limit` (`gloas/mainnet.py:6678-6687`): the
EIP-7732 quotient, the checked `Gwei` chain as `getBalanceChurnLimit` ports it. -/
forkdef getConsolidationChurnLimit (state : State) : Checked Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.consolidationChurnLimitQuotientC
  let churn := scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  churn - rounded

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
  let indices := (getActiveValidatorIndices state epoch).filter (fun vi => !(validators[vi.toNat]!).slashed)
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
-- with two differences. The churn budget is `get_activation_churn_limit` (Gloas) rather than
-- the activation-exit one, and the Electra eth1-bridge stop (`deposit.slot > GENESIS_SLOT and
-- state.eth1_deposit_index < state.deposit_requests_start_index`) is gone; the Gloas text has
-- no such check at either alpha.12 or beta.4. `DepositScan` (the scan's record state and
-- result) is the Fulu one, replayed here.
inherit DepositScan

/-- F1 signature repair (inventory §2.5): `finalizedSlot` is the spec's
`compute_start_slot_at_epoch(...)` value, a `Slot`; it keeps the raw `Slot` type
until Stage 5. -/
forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot : Slot) (avail : Gwei)
    (nextEpoch : Epoch) : StateTransition DepositScan :=
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
      -- `is_churn_limit_reached = processed_amount + deposit.amount >
      -- available_for_processing`: the sum is the checked `Gwei` add, bound inside
      -- the branch that forms it.
      let running ← s.processed + deposit.amount
      if running > avail then return .done { s with churnReached := true }
      else
        applyPendingDeposit deposit
        return advance running s.postpone

forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  let churn ← getActivationChurnLimit state
  let avail ← (sszGet state depositBalanceToConsume) + churn
  let finalizedSlot ← computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  -- `pendingDeposits` is a progressive list at alpha.12, so the leftover array goes in
  -- whole: no `PENDING_DEPOSITS_LIMIT` cap, no `.listFull` raise to mirror.
  let remaining : ProgressiveList PendingDeposit :=
    ⟨deposits.extract scan.ndi deposits.size ++ scan.postpone⟩
  -- `available_for_processing - processed_amount` forms only in the churn-hit
  -- branch (the reset arm stores `Gwei(0)`), so the bind sits in its branch.
  let remainingChurn ← if scan.churnReached then avail - scan.processed else pure (0 : Gwei)
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := if scan.churnReached then remainingChurn else 0

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

/-- `get_builder_payment_quorum_threshold` (`gloas/mainnet.py:7867-7874`):
`get_total_active_balance(state) // Uint64(SLOTS_PER_EPOCH) *
BUILDER_PAYMENT_THRESHOLD_NUMERATOR // BUILDER_PAYMENT_THRESHOLD_DENOMINATOR`. The
per-slot division takes the proved-total `PositiveDivisor` view; the product and
the fraction are the checked `Gwei` chain over the `Uint64` threshold constants,
each bound where the pyspec forms it. -/
forkdef getBuilderPaymentQuorumThreshold (state : State) : Checked Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let perSlotBalance := totalActiveBalance / Const.slotsPerEpochDiv
  let scaled ← perSlotBalance * Const.builderPaymentThresholdNumerator
  scaled / Const.builderPaymentThresholdDenominator

/-- `process_builder_pending_payments` (`gloas/beacon-chain.md:1719-1731`): for each of the previous
epoch's pending payments whose weight clears the quorum threshold, queue its
withdrawal directly; then shift the payment window down by `SLOTS_PER_EPOCH` and
pad with empties. No churn reservation. -/
forkdef processBuilderPendingPayments : StateTransition Unit := do
  let state ← get

  let quorum ← getBuilderPaymentQuorumThreshold state

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
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  -- The committees concatenate in slot order, each `get_beacon_committee` bound as it
  -- forms; the first rejecting slot surfaces (§4.3).
  let indices ← (Array.range committeesPerSlot).foldlM
    (fun acc i => do
      let committee ← getBeaconCommittee state slot i
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
      shiftWindow (sszGet state ptcWindow) Const.slotsPerEpoch (2 * Const.slotsPerEpoch)
        (fun k => fresh[k]!)

end

end EthCLSpecs.Gloas
