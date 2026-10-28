import EthCLSpecs.Gloas.Containers

/-!
# `EthCLSpecs.Gloas.Upgrade`: the Fulu → Gloas fork upgrade (load order, lifecycle)

`upgradeToGloas` is one of the two sanctioned cross-fork references
(`SPECS_ARCHITECTURE.md` §6.2, `Interface.lean` being the other): it reads a
finished Fulu state and constructs the Gloas one, so it lives in Gloas and names
both forks. It is the `fork` vector format's entry point.

Ported from the v1.7.0-beta.4 `specs/gloas/fork.md`: common fields carry
across through the per-container `cv*` converters below, since a Gloas component
container is this fork's own replayed copy and so a distinct type from Fulu's;
the fork version bumps (`previous := pre.fork.current`,
`current := GLOAS_FORK_VERSION`, `epoch := get_current_epoch(pre)`);
`latest_block_hash` comes from the dropped payload header's block hash; the cached
`latest_execution_payload_bid` is a self-build bid for the pre-state's head (its parent
hash and root, block hash, RANDAO, gas limit, and slot); and the other ePBS fields
initialize to their fork-transition values (`execution_payload_availability` all-ones,
`builder_pending_payments` a vector of empties, the rest empty/zero).

The spec then sets `post.ptc_window = initialize_ptc_window(post)` and runs
`onboard_builders_from_pending_deposits(post)`. Both read and write the Gloas state, so they
are the Gloas state-side step `completeUpgradeToGloas` (`Gloas/Operations.lean`), which the
runner applies to the state built here. Until then `ptc_window` holds the spec's empty
`PayloadTimelinessCommitteeWindow()`, all zeros.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Cache

namespace EthCLSpecs.Gloas

-- The fork-upgrade boundary: this file names both forks by definition, so it is
-- one of the two sanctioned places that reach into the parent
-- (`SPECS_ARCHITECTURE.md` §6.2). `open scoped Downgrade` activates the
-- generated bridge from `Gloas.Preset` to `Fulu.Preset`, which is what lets the
-- conversions below run under a single `[Preset]` binder with the preset still
-- symbolic. Nothing else in Gloas opens it.
open scoped Downgrade

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
fork version is a config value, not a preset one. The two closing steps (the PTC window
and the builder onboarding) run after this through `completeUpgradeToGloas`, since they
need the Gloas state-side helpers. -/
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
    validators                    := ⟨pre.validators.val.map cvValidator⟩
    balances                      := ⟨pre.balances.val⟩
    randaoMixes                   := pre.randaoMixes
    slashings                     := pre.slashings
    previousEpochParticipation    := ⟨pre.previousEpochParticipation.val⟩
    currentEpochParticipation     := ⟨pre.currentEpochParticipation.val⟩
    justificationBits             := pre.justificationBits
    previousJustifiedCheckpoint   := cvCheckpoint pre.previousJustifiedCheckpoint
    currentJustifiedCheckpoint    := cvCheckpoint pre.currentJustifiedCheckpoint
    finalizedCheckpoint           := cvCheckpoint pre.finalizedCheckpoint
    inactivityScores              := ⟨pre.inactivityScores.val⟩
    currentSyncCommittee          := cvSyncCommittee pre.currentSyncCommittee
    nextSyncCommittee             := cvSyncCommittee pre.nextSyncCommittee
    -- The self-build bid for the pre-state's head (fields in the spec's order; the value,
    -- execution payment, fee recipient, and commitments start empty).
    latestExecutionPayloadBid     :=
      { parentBlockHash       := pre.latestExecutionPayloadHeader.parentHash
        parentBlockRoot       := pre.latestBlockHeader.parentRoot
        blockHash             := pre.latestExecutionPayloadHeader.blockHash
        prevRandao            := pre.latestExecutionPayloadHeader.prevRandao
        feeRecipient          := Vector.replicate 20 0
        gasLimit              := pre.latestExecutionPayloadHeader.gasLimit
        builderIndex          := Const.builderIndexSelfBuild
        slot                  := pre.latestBlockHeader.slot
        value                 := 0
        executionPayment      := 0
        blobKzgCommitments    := default
        executionRequestsRoot := htr (default : Gloas.ExecutionRequests) }
    nextWithdrawalIndex           := pre.nextWithdrawalIndex
    nextWithdrawalValidatorIndex  := pre.nextWithdrawalValidatorIndex
    historicalSummaries           := pre.historicalSummaries.mapCap cvHistoricalSummary
    depositRequestsStartIndex     := pre.depositRequestsStartIndex
    depositBalanceToConsume       := pre.depositBalanceToConsume
    exitBalanceToConsume          := pre.exitBalanceToConsume
    earliestExitEpoch             := pre.earliestExitEpoch
    consolidationBalanceToConsume := pre.consolidationBalanceToConsume
    earliestConsolidationEpoch    := pre.earliestConsolidationEpoch
    pendingDeposits               := ⟨pre.pendingDeposits.val.map cvPendingDeposit⟩
    pendingPartialWithdrawals     := ⟨pre.pendingPartialWithdrawals.val.map cvPendingPartialWithdrawal⟩
    pendingConsolidations         := ⟨pre.pendingConsolidations.val.map cvPendingConsolidation⟩
    proposerLookahead             := pre.proposerLookahead
    builders                      := default
    nextWithdrawalBuilderIndex    := 0
    executionPayloadAvailability  := ⟨BitVec.allOnes _⟩
    builderPendingPayments        := Vector.replicate (2 * Const.slotsPerEpoch) default
    builderPendingWithdrawals     := default
    latestBlockHash               := pre.latestExecutionPayloadHeader.blockHash
    payloadExpectedWithdrawals    := default
    -- `PayloadTimelinessCommitteeWindow()`: all zeros until `completeUpgradeToGloas` fills it.
    ptcWindow                     := Vector.replicate _ (Vector.replicate _ 0) }

end EthCLSpecs.Gloas
