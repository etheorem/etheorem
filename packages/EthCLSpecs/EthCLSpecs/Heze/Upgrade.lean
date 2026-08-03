import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Upgrade`: the Gloas → Heze fork upgrade (EIP-7805)

`upgradeToHeze` reads a finished Gloas state and constructs the Heze one, the single
sanctioned cross-fork reference. At alpha.11 it is a near-passthrough: every
`BeaconState` field carries across and only the fork version bumps. Because Heze's
containers are fresh namespace twins of Gloas's, each container field is copied through
a field-by-field `cv*` converter, the mechanical price of the flat namespace. No builder
onboarding and no PTC recompute: builders were onboarded and the PTC window built at the
Gloas fork, and EIP-7805 adds no `BeaconState` field, so the upgrade is a pure copy.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-! ## Component-container conversion at the fork boundary -/

private def cvBeaconBlockHeader [Preset] (v : Gloas.BeaconBlockHeader) : BeaconBlockHeader :=
  { slot := v.slot, proposerIndex := v.proposerIndex, parentRoot := v.parentRoot,
    stateRoot := v.stateRoot, bodyRoot := v.bodyRoot }
private def cvEth1Data [Preset] (v : Gloas.Eth1Data) : Eth1Data :=
  { depositRoot := v.depositRoot, depositCount := v.depositCount, blockHash := v.blockHash }
private def cvCheckpoint [Preset] (v : Gloas.Checkpoint) : Checkpoint :=
  { epoch := v.epoch, root := v.root }
private def cvValidator [Preset] (v : Gloas.Validator) : Validator :=
  { pubkey := v.pubkey, withdrawalCredentials := v.withdrawalCredentials,
    effectiveBalance := v.effectiveBalance, slashed := v.slashed,
    activationEligibilityEpoch := v.activationEligibilityEpoch,
    activationEpoch := v.activationEpoch, exitEpoch := v.exitEpoch,
    withdrawableEpoch := v.withdrawableEpoch }
private def cvSyncCommittee [Preset] (v : Gloas.SyncCommittee) : SyncCommittee :=
  { pubkeys := v.pubkeys, aggregatePubkey := v.aggregatePubkey }
private def cvHistoricalSummary [Preset] (v : Gloas.HistoricalSummary) : HistoricalSummary :=
  { blockSummaryRoot := v.blockSummaryRoot, stateSummaryRoot := v.stateSummaryRoot }
private def cvPendingDeposit [Preset] (v : Gloas.PendingDeposit) : PendingDeposit :=
  { pubkey := v.pubkey, withdrawalCredentials := v.withdrawalCredentials, amount := v.amount,
    signature := v.signature, slot := v.slot }
private def cvPendingPartialWithdrawal [Preset] (v : Gloas.PendingPartialWithdrawal) :
    PendingPartialWithdrawal :=
  { validatorIndex := v.validatorIndex, amount := v.amount, withdrawableEpoch := v.withdrawableEpoch }
private def cvPendingConsolidation [Preset] (v : Gloas.PendingConsolidation) : PendingConsolidation :=
  { sourceIndex := v.sourceIndex, targetIndex := v.targetIndex }
private def cvBuilder [Preset] (v : Gloas.Builder) : Builder :=
  { pubkey := v.pubkey, version := v.version, executionAddress := v.executionAddress,
    balance := v.balance, depositEpoch := v.depositEpoch, withdrawableEpoch := v.withdrawableEpoch }
private def cvBuilderPendingWithdrawal [Preset] (v : Gloas.BuilderPendingWithdrawal) :
    BuilderPendingWithdrawal :=
  { feeRecipient := v.feeRecipient, amount := v.amount, builderIndex := v.builderIndex }
private def cvBuilderPendingPayment [Preset] (v : Gloas.BuilderPendingPayment) : BuilderPendingPayment :=
  { weight := v.weight, withdrawal := cvBuilderPendingWithdrawal v.withdrawal,
    proposerIndex := v.proposerIndex }
private def cvWithdrawal [Preset] (v : Gloas.Withdrawal) : Withdrawal :=
  { index := v.index, validatorIndex := v.validatorIndex, address := v.address, amount := v.amount }

/-- Convert the Gloas bid to the Heze bid. At alpha.11 the bid is unchanged, so this is a
plain 12-field copy. -/
private def cvExecutionPayloadBid [Preset] (v : Gloas.ExecutionPayloadBid) : ExecutionPayloadBid :=
  { parentBlockHash := v.parentBlockHash, parentBlockRoot := v.parentBlockRoot,
    blockHash := v.blockHash, prevRandao := v.prevRandao, feeRecipient := v.feeRecipient,
    gasLimit := v.gasLimit, builderIndex := v.builderIndex, slot := v.slot, value := v.value,
    executionPayment := v.executionPayment, blobKzgCommitments := v.blobKzgCommitments,
    executionRequestsRoot := v.executionRequestsRoot }

/-- The fork upgrade `upgrade_to_heze(pre)`: builds the Heze state from a finished Gloas
one. At alpha.11 every field carries across; only the fork version changes
(`previous := pre.fork.current`, `current := HEZE_FORK_VERSION`, `epoch := get_current_epoch(pre)`).
No builder onboarding or PTC recompute is needed: both already happened at the Gloas fork
and live in the pre-state. `hezeForkVersion` is the config's `HEZE_FORK_VERSION`, passed by
the runner. -/
def upgradeToHeze [Preset] (hezeForkVersion : Version) (pre : Gloas.BeaconState) :
    Heze.BeaconState :=
  let epoch : Epoch := pre.slot / UInt64.ofNat Const.slotsPerEpoch
  { genesisTime                   := pre.genesisTime
    genesisValidatorsRoot         := pre.genesisValidatorsRoot
    slot                          := pre.slot
    forkData                      :=
      { previousVersion := pre.forkData.currentVersion
        currentVersion  := hezeForkVersion
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
    latestBlockHash               := pre.latestBlockHash
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
    builders                      := pre.builders.mapCap cvBuilder
    nextWithdrawalBuilderIndex    := pre.nextWithdrawalBuilderIndex
    executionPayloadAvailability  := pre.executionPayloadAvailability
    builderPendingPayments        := pre.builderPendingPayments.map cvBuilderPendingPayment
    builderPendingWithdrawals     := pre.builderPendingWithdrawals.mapCap cvBuilderPendingWithdrawal
    latestExecutionPayloadBid     := cvExecutionPayloadBid pre.latestExecutionPayloadBid
    payloadExpectedWithdrawals    := pre.payloadExpectedWithdrawals.mapCap cvWithdrawal
    ptcWindow                     := pre.ptcWindow }

end EthCLSpecs.Heze
