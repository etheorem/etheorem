import EthCLSpecs.Gloas.Containers
import EthCLSpecs.Fulu.Committees

/-!
# `EthCLSpecs.Gloas.Upgrade`: the Fulu → Gloas fork upgrade (load order, lifecycle)

`upgradeToGloas` is the single sanctioned cross-fork reference
(`SPECS_ARCHITECTURE.md` §6.2): it reads a finished Fulu state and constructs the
Gloas one, so it lives in Gloas and names both forks. It is the `fork` vector
format's entry point.

Ported verbatim from the v1.7.0-alpha.10 `specs/gloas/fork.md`: common fields carry
across (the unchanged component containers are reused, so the copies are
direct, no conversion); the fork version bumps (`previous := pre.fork.current`,
`current := GLOAS_FORK_VERSION`, `epoch := get_current_epoch(pre)`);
`latest_block_hash` comes from the dropped payload header's block hash; and the
ePBS fields initialize to their fork-transition values (`execution_payload_availability`
all-ones, `builder_pending_payments` a vector of empties, the rest empty/zero).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu
open SizzLean.Cache

namespace EthCLSpecs.Gloas

/-- `compute_ptc(state, slot)` evaluated over the Fulu pre-state at the fork
boundary: the seed mixes `DOMAIN_PTC_ATTESTER`, the candidate set is every beacon
committee for the slot concatenated in order, and the payload-timeliness committee
is the unshuffled balance-weighted selection of `PTC_SIZE` of them. The committee
machinery is Fulu's (the pre-state is a Fulu state), so the helpers are called
directly rather than inherited. -/
def computePtcFromFulu [Preset] [HasherTag] (state : Fulu.State) (slot : Slot) :
    Vector ValidatorIndex Const.ptcSize :=
  let epoch := Fulu.computeEpochAtSlot slot
  let seed := sha ((Fulu.getSeed state epoch Const.domainPtcAttester) ++ uint64ToBytes slot)
  let committeesPerSlot := Fulu.getCommitteeCountPerSlot state epoch
  let indices := (Array.range committeesPerSlot).foldl
    (fun acc i => acc ++ Fulu.getBeaconCommittee state slot i) #[]
  let sel := Fulu.computeBalanceWeightedSelection state indices seed Const.ptcSize false
  Vector.ofFn (fun i : Fin Const.ptcSize => sel[i.val]!)

/-- `initialize_ptc_window(pre)`: the cached PTC window seeding the Gloas state.
The first `SLOTS_PER_EPOCH` slots (the empty previous epoch) hold zeroed
committees; the next `(1 + MIN_SEED_LOOKAHEAD)` epochs hold `compute_ptc` for each
slot. `MIN_SEED_LOOKAHEAD` is `1`, so the window is `3 * SLOTS_PER_EPOCH` long,
matching the `ptcWindow` field's declared length. -/
def initializePtcWindow [Preset] [HasherTag] (state : Fulu.State) :
    Vector (Vector ValidatorIndex Const.ptcSize) (3 * Const.slotsPerEpoch) :=
  let currentEpoch := Fulu.currentEpochOf state
  let emptyCommittee : Vector ValidatorIndex Const.ptcSize := Vector.replicate Const.ptcSize 0
  Vector.ofFn fun i : Fin (3 * Const.slotsPerEpoch) =>
    if i.val < Const.slotsPerEpoch then emptyCommittee
    else
      let j := i.val - Const.slotsPerEpoch
      let epoch := currentEpoch + UInt64.ofNat (j / Const.slotsPerEpoch)
      let startSlot := Fulu.computeStartSlotAtEpoch epoch
      computePtcFromFulu state (startSlot + UInt64.ofNat (j % Const.slotsPerEpoch))

/-! ## Component-container conversion at the fork boundary

Each EIP-7732-unchanged container is its own type in both forks (`Gloas.Inherited`),
SSZ-identical but not defeq, so `upgrade_to_gloas` copies a Fulu value into its Gloas
twin field-by-field. List fields map the element converter under the cap proof
with `SSZList.mapCap`. This per-field copy is the price of the fork's flat namespace. -/

private def cvBeaconBlockHeader [Preset] (v : Fulu.BeaconBlockHeader) : BeaconBlockHeader :=
  { slot := v.slot, proposerIndex := v.proposerIndex, parentRoot := v.parentRoot,
    stateRoot := v.stateRoot, bodyRoot := v.bodyRoot }
private def cvEth1Data [Preset] (v : Fulu.Eth1Data) : Eth1Data :=
  { depositRoot := v.depositRoot, depositCount := v.depositCount, blockHash := v.blockHash }
private def cvCheckpoint [Preset] (v : Fulu.Checkpoint) : Checkpoint :=
  { epoch := v.epoch, root := v.root }
private def cvValidator [Preset] (v : Fulu.Validator) : Validator :=
  { pubkey := v.pubkey, withdrawalCredentials := v.withdrawalCredentials,
    effectiveBalance := v.effectiveBalance, slashed := v.slashed,
    activationEligibilityEpoch := v.activationEligibilityEpoch,
    activationEpoch := v.activationEpoch, exitEpoch := v.exitEpoch,
    withdrawableEpoch := v.withdrawableEpoch }
private def cvSyncCommittee [Preset] (v : Fulu.SyncCommittee) : SyncCommittee :=
  { pubkeys := v.pubkeys, aggregatePubkey := v.aggregatePubkey }
private def cvHistoricalSummary [Preset] (v : Fulu.HistoricalSummary) : HistoricalSummary :=
  { blockSummaryRoot := v.blockSummaryRoot, stateSummaryRoot := v.stateSummaryRoot }
private def cvPendingDeposit [Preset] (v : Fulu.PendingDeposit) : PendingDeposit :=
  { pubkey := v.pubkey, withdrawalCredentials := v.withdrawalCredentials, amount := v.amount,
    signature := v.signature, slot := v.slot }
private def cvPendingPartialWithdrawal [Preset] (v : Fulu.PendingPartialWithdrawal) :
    PendingPartialWithdrawal :=
  { validatorIndex := v.validatorIndex, amount := v.amount, withdrawableEpoch := v.withdrawableEpoch }
private def cvPendingConsolidation [Preset] (v : Fulu.PendingConsolidation) : PendingConsolidation :=
  { sourceIndex := v.sourceIndex, targetIndex := v.targetIndex }

/-- The fork upgrade `upgrade_to_gloas(pre)`: builds the Gloas state from a finished
Fulu one. `gloasForkVersion` is the config's `GLOAS_FORK_VERSION`
(`0x07000001` minimal, `0x07000000` mainnet), passed in by the runner since the
fork version is a config value, not a preset one. The builder onboarding step
(`onboard_builders_from_pending_deposits`) runs after this in the runner, since it
needs the Gloas builder-registry helpers. -/
def upgradeToGloas [Preset] [HasherTag] (gloasForkVersion : Version) (pre : Fulu.BeaconState) :
    Gloas.BeaconState :=
  let epoch : Epoch := pre.slot / UInt64.ofNat Const.slotsPerEpoch
  { genesisTime                   := pre.genesisTime
    genesisValidatorsRoot         := pre.genesisValidatorsRoot
    slot                          := pre.slot
    forkData                      :=
      { previousVersion := pre.forkData.currentVersion
        currentVersion  := gloasForkVersion
        epoch           := epoch }
    latestBlockHeader             := cvBeaconBlockHeader pre.latestBlockHeader
    blockRoots                    := pre.blockRoots
    stateRoots                    := pre.stateRoots
    historicalRoots               := pre.historicalRoots
    eth1Data                      := cvEth1Data pre.eth1Data
    eth1DataVotes                 := pre.eth1DataVotes.mapCap cvEth1Data
    eth1DepositIndex              := pre.eth1DepositIndex
    validators                    := pre.validators.mapCap cvValidator
    balances                      := pre.balances
    randaoMixes                   := pre.randaoMixes
    slashings                     := pre.slashings
    previousEpochParticipation    := pre.previousEpochParticipation
    currentEpochParticipation     := pre.currentEpochParticipation
    justificationBits             := pre.justificationBits
    previousJustifiedCheckpoint   := cvCheckpoint pre.previousJustifiedCheckpoint
    currentJustifiedCheckpoint    := cvCheckpoint pre.currentJustifiedCheckpoint
    finalizedCheckpoint           := cvCheckpoint pre.finalizedCheckpoint
    inactivityScores              := pre.inactivityScores
    currentSyncCommittee          := cvSyncCommittee pre.currentSyncCommittee
    nextSyncCommittee             := cvSyncCommittee pre.nextSyncCommittee
    latestExecutionPayloadBid     :=
      { (default : Gloas.ExecutionPayloadBid) with
          blockHash             := pre.latestExecutionPayloadHeader.blockHash
          gasLimit              := pre.latestExecutionPayloadHeader.gasLimit
          executionRequestsRoot := htr (default : Fulu.ExecutionRequests) }
    nextWithdrawalIndex           := pre.nextWithdrawalIndex
    nextWithdrawalValidatorIndex  := pre.nextWithdrawalValidatorIndex
    historicalSummaries           := pre.historicalSummaries.mapCap cvHistoricalSummary
    depositRequestsStartIndex     := pre.depositRequestsStartIndex
    depositBalanceToConsume       := pre.depositBalanceToConsume
    exitBalanceToConsume          := pre.exitBalanceToConsume
    earliestExitEpoch             := pre.earliestExitEpoch
    consolidationBalanceToConsume := pre.consolidationBalanceToConsume
    earliestConsolidationEpoch    := pre.earliestConsolidationEpoch
    pendingDeposits               := pre.pendingDeposits.mapCap cvPendingDeposit
    pendingPartialWithdrawals     := pre.pendingPartialWithdrawals.mapCap cvPendingPartialWithdrawal
    pendingConsolidations         := pre.pendingConsolidations.mapCap cvPendingConsolidation
    proposerLookahead             := pre.proposerLookahead
    builders                      := default
    nextWithdrawalBuilderIndex    := 0
    executionPayloadAvailability  := ⟨BitVec.allOnes _⟩
    builderPendingPayments        := Vector.replicate (2 * Const.slotsPerEpoch) default
    builderPendingWithdrawals     := default
    latestBlockHash               := pre.latestExecutionPayloadHeader.blockHash
    payloadExpectedWithdrawals    := default
    ptcWindow                     := initializePtcWindow (SSZ.CachedBox HasherTag.H pre) }

end EthCLSpecs.Gloas
