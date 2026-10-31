import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Upgrade`: the Gloas → Heze fork upgrade (EIP-7805)

`upgradeToHeze` reads a finished Gloas state and constructs the Heze one, the single
allowed cross-fork reference. It first asserts that the old deposit mechanism has been
disabled (`eth1_deposit_index == deposit_requests_start_index`, EIP-8015), then the fork
version bumps, the bid gains an empty `inclusion_list_bits`, and the four eth1 deposit fields
are dropped (EIP-8015). Because Heze's containers are fresh namespace twins of Gloas's, each
container field is copied through a field-by-field `cv*` converter, the mechanical price of
the flat namespace. No builder onboarding and no PTC recompute: builders were onboarded and
the PTC window built at the Gloas fork.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

-- The fork-upgrade boundary: this file converts a Gloas pre-state into a Heze
-- state, so it names both forks by definition and is one of the two sanctioned
-- places that reach into the parent (`SPECS_ARCHITECTURE.md` §6.2).
-- `open scoped Downgrade` activates the generated bridge from `Heze.Preset` to
-- `Gloas.Preset`, which lets the conversions below run under a single `[Preset]`
-- binder with the preset still symbolic. Nothing else in Heze opens it.
open scoped Downgrade

/-! ## Component-container conversion at the fork boundary -/

private def cvBeaconBlockHeader [Preset] (v : Gloas.BeaconBlockHeader) : BeaconBlockHeader :=
  { slot := v.slot, proposerIndex := v.proposerIndex, parentRoot := v.parentRoot,
    stateRoot := v.stateRoot, bodyRoot := v.bodyRoot }
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

/-- Convert the Gloas bid to the Heze bid. EIP-7805 adds `inclusion_list_bits`,
empty at the fork boundary. -/
private def cvExecutionPayloadBid [Preset] (v : Gloas.ExecutionPayloadBid) : ExecutionPayloadBid :=
  { parentBlockHash := v.parentBlockHash, parentBlockRoot := v.parentBlockRoot,
    blockHash := v.blockHash, prevRandao := v.prevRandao, feeRecipient := v.feeRecipient,
    gasLimit := v.gasLimit, builderIndex := v.builderIndex, slot := v.slot, value := v.value,
    executionPayment := v.executionPayment, blobKzgCommitments := ⟨v.blobKzgCommitments.val⟩,
    executionRequestsRoot := v.executionRequestsRoot,
    inclusionListBits := default }

/-- The fork upgrade `upgrade_to_heze(pre)` (`heze/fork.md:41-123`): builds the Heze state
from a finished Gloas one. It opens with `assert pre.eth1_deposit_index ==
pre.deposit_requests_start_index` (EIP-8015, new at v1.7.0-beta.4): the eth1 bridge must have
delivered every deposit before the fields that track it are dropped. A failed assert is the
`.assert` reject, so the upgrade returns `Except StateTransitionError`. Then the fork version
changes (`previous := pre.fork.current`, `current := HEZE_FORK_VERSION`,
`epoch := get_current_epoch(pre)`), the bid gains an empty `inclusion_list_bits`, and
`eth1_data`, `eth1_data_votes`, `eth1_deposit_index`, and `deposit_requests_start_index` are
not carried. No builder onboarding or PTC recompute is needed: both already happened at the
Gloas fork and live in the pre-state. `hezeForkVersion` is the config's `HEZE_FORK_VERSION`,
passed by the runner. -/
def upgradeToHeze [Preset] (hezeForkVersion : Version) (pre : Gloas.BeaconState) :
    Except StateTransitionError Heze.BeaconState := do
  -- [New in Heze:EIP8015] the old deposit mechanism has been disabled.
  assert (pre.eth1DepositIndex == pre.depositRequestsStartIndex)
  let epoch : Epoch := pre.slot / UInt64.ofNat Const.slotsPerEpoch
  pure
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
      latestBlockHash               := pre.latestBlockHash
      nextWithdrawalIndex           := pre.nextWithdrawalIndex
      nextWithdrawalValidatorIndex  := pre.nextWithdrawalValidatorIndex
      historicalSummaries           := pre.historicalSummaries.mapCap cvHistoricalSummary
      depositBalanceToConsume       := pre.depositBalanceToConsume
      exitBalanceToConsume          := pre.exitBalanceToConsume
      earliestExitEpoch             := pre.earliestExitEpoch
      consolidationBalanceToConsume := pre.consolidationBalanceToConsume
      earliestConsolidationEpoch    := pre.earliestConsolidationEpoch
      pendingDeposits               := ⟨pre.pendingDeposits.val.map cvPendingDeposit⟩
      pendingPartialWithdrawals     := ⟨pre.pendingPartialWithdrawals.val.map cvPendingPartialWithdrawal⟩
      pendingConsolidations         := ⟨pre.pendingConsolidations.val.map cvPendingConsolidation⟩
      proposerLookahead             := pre.proposerLookahead
      builders                      := ⟨pre.builders.val.map cvBuilder⟩
      nextWithdrawalBuilderIndex    := pre.nextWithdrawalBuilderIndex
      executionPayloadAvailability  := pre.executionPayloadAvailability
      builderPendingPayments        := pre.builderPendingPayments.map cvBuilderPendingPayment
      builderPendingWithdrawals     := ⟨pre.builderPendingWithdrawals.val.map cvBuilderPendingWithdrawal⟩
      latestExecutionPayloadBid     := cvExecutionPayloadBid pre.latestExecutionPayloadBid
      payloadExpectedWithdrawals    := ⟨pre.payloadExpectedWithdrawals.val.map cvWithdrawal⟩
      ptcWindow                     := pre.ptcWindow }

end EthCLSpecs.Heze
