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
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

state_section

-- Time / RANDAO accessors.
inherit computeEpochAtSlot
inherit computeStartSlotAtEpoch
inherit getCurrentEpoch
inherit getPreviousEpoch
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

-- Gloas (EIP-8061) churn: `get_exit_churn_limit` / `get_activation_churn_limit`
-- use `CHURN_LIMIT_QUOTIENT_GLOAS`, and `compute_exit_epoch_and_update_churn` uses
-- `get_exit_churn_limit` rather than Fulu's `get_activation_exit_churn_limit`. These
-- override the inherited Fulu versions; `initiateValidatorExit`/`slashValidator`
-- (inherited below) bind to this `computeExitEpochAndUpdateChurn`.
forkdef getExitChurnLimit (state : State) : Gwei :=
  let churn := umax Const.minPerEpochChurnLimitElectra
    ((getTotalActiveBalance state) / Const.churnLimitQuotientGloas)
  churn - churn % Const.effectiveBalanceIncrementG

forkdef getActivationChurnLimit (state : State) : Gwei :=
  let churn := umax Const.minPerEpochChurnLimitElectra
    ((getTotalActiveBalance state) / Const.churnLimitQuotientGloas)
  umin Const.maxPerEpochActivationChurnLimitGloas (churn - churn % Const.effectiveBalanceIncrementG)

forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let earliest := umax (sszGet state earliestExitEpoch) (computeActivationExitEpoch currentEpoch)
  let perEpochChurn := getExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)
  let (ee, ebtc) := reserveChurn exitBalance consume perEpochChurn earliest

  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := ebtc - exitBalance, earliestExitEpoch := ee
  return ee

inherit initiateValidatorExit
inherit slashValidator
inherit getDomain
inherit getPendingBalanceToWithdraw

-- Gloas (EIP-8061) consolidation churn: `total_active // CONSOLIDATION_CHURN_LIMIT_QUOTIENT`
-- (no `MIN` floor, no balance-churn subtraction). Overrides the inherited Fulu
-- version; the inherited `computeConsolidationEpochAndUpdateChurn` below binds to it.
forkdef getConsolidationChurnLimit (state : State) : Gwei :=
  let churn := (getTotalActiveBalance state) / Const.consolidationChurnLimitQuotient
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
late-binds its `getBeaconProposerIndices` call to this Gloas copy. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) : Array ValidatorIndex :=
  let validators := sszGet state validators
  let indices := (getActiveValidatorIndices state epoch).filter (fun vi => !(validators[vi.toNat]!).slashed)
  computeProposerIndices state epoch (getSeed state epoch Const.domainBeaconProposer) indices

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

-- Gloas (EIP-8061) `process_pending_deposits`: identical to Fulu except the churn
-- budget is `get_activation_churn_limit` (Gloas) rather than the activation-exit one.
-- `DepositScan` (the scan's record state and result) is the Fulu one, replayed here.
inherit DepositScan

forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei) (nextEpoch : Epoch) :
    StateTransition DepositScan :=
  -- Fuel is `deposits.size + 1`: the `ndi ≥ deposits.size` guard returns `.done` one step
  -- before exhaustion, so `fuelLoop`'s `exhausted` value is unreachable.
  fuelLoop (deposits.size + 1) ({} : DepositScan) ({} : DepositScan) fun s => do
    if s.ndi ≥ deposits.size then return .done s
    let state ← get
    let deposit := deposits[s.ndi]!

    -- Stop the scan early: the eth1-bridge deposits are not yet applied, the deposit is
    -- not finalized, or this epoch's deposit cap is reached.
    if deposit.slot > Const.genesisSlot
        && (sszGet state eth1DepositIndex) < (sszGet state depositRequestsStartIndex) then return .done s
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
    else if s.processed + deposit.amount > avail then return .done { s with churnReached := true }
    else applyPendingDeposit deposit; return advance (s.processed + deposit.amount) s.postpone

forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let avail := (sszGet state depositBalanceToConsume) + getActivationChurnLimit state
  let finalizedSlot := computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  modifyState fun state => sszUpdate state with
    pendingDeposits := sszOfArray (deposits.extract scan.ndi deposits.size ++ scan.postpone),
    depositBalanceToConsume := if scan.churnReached then avail - scan.processed else 0

inherit pcLoop
inherit processPendingConsolidations
inherit processEffectiveBalanceUpdates
inherit processSlashingsReset
inherit processRandaoMixesReset
inherit processEth1DataReset
inherit processHistoricalSummariesUpdate
inherit processParticipationFlagUpdates

-- Shuffle-dependent substeps: now inheritable since the committee layer is in the
-- Gloas namespace. `processProposerLookahead`'s `getBeaconProposerIndices` call binds
-- to the Gloas EIP-8045 override above.
inherit processSyncCommitteeUpdates
inherit processProposerLookahead

/-! ## Gloas-new epoch substep (EIP-7732) -/

/-- `process_builder_pending_payments` (v1.7.0-alpha.10): for each of the previous
epoch's pending payments whose weight clears the quorum threshold
(`get_total_active_balance / SLOTS_PER_EPOCH * NUMERATOR / DENOMINATOR`, `>=`),
queue its withdrawal directly; then shift the payment window down by
`SLOTS_PER_EPOCH` and pad with empties. No churn reservation. -/
forkdef processBuilderPendingPayments : StateTransition Unit := do
  let state ← get

  -- Quorum threshold: `get_total_active_balance / SLOTS_PER_EPOCH * NUMERATOR / DENOMINATOR`.
  let quorum := (getTotalActiveBalance state / UInt64.ofNat Const.slotsPerEpoch)
    * Const.builderPaymentThresholdNumerator / Const.builderPaymentThresholdDenominator

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

/-- `compute_ptc` (v1.7.0-alpha.10, EIP-7732): the payload-timeliness committee for
`slot`, with possible duplicates. Concatenate every beacon committee for the slot in
order, then take a `PTC_SIZE` balance-weighted selection with no shuffle. The seed
mixes `DOMAIN_PTC_ATTESTER` and the slot. -/
forkdef computePtc (state : State) (slot : Slot) : Vector ValidatorIndex Const.ptcSize :=
  let epoch := computeEpochAtSlot slot
  let seed := sha ((getSeed state epoch Const.domainPtcAttester) ++ uint64ToBytes slot)
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices := (Array.range committeesPerSlot).foldl
    (fun acc i => acc ++ getBeaconCommittee state slot i) (#[] : Array ValidatorIndex)
  let sel := computeBalanceWeightedSelection state indices seed Const.ptcSize false
  Vector.ofFn (fun i : Fin Const.ptcSize => sel[i.val]!)

/-- `process_ptc_window` (v1.7.0-alpha.10, EIP-7732): shift the cached PTC window down
by `SLOTS_PER_EPOCH` and recompute the last epoch's per-slot PTCs from the snapshot
state. The window length is `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH = 3 *
SLOTS_PER_EPOCH` (MIN_SEED_LOOKAHEAD = 1). -/
forkdef processPtcWindow : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + Const.minSeedLookahead + 1
  let startSlot := computeStartSlotAtEpoch nextEpoch
  let fresh : Array (Vector ValidatorIndex Const.ptcSize) :=
    (Array.range Const.slotsPerEpoch).map (fun i => computePtc state (startSlot + UInt64.ofNat i))

  modifyState fun state =>
    sszUpdate state with ptcWindow :=
      shiftWindow (sszGet state ptcWindow) Const.slotsPerEpoch (2 * Const.slotsPerEpoch)
        (fun k => fresh[k]!)

end

end EthCLSpecs.Gloas
