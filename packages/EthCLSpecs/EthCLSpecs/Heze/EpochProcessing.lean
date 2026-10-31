import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.EpochProcessing`: the epoch substeps (Gloas over Heze state)

EIP-7805 (FOCIL) changes no epoch processing. EIP-8015 and EIP-8365 (new at v1.7.0-beta.4)
change two pieces: `process_eth1_data_reset` is gone with the eth1 votes it reset, and
`apply_pending_deposit` drops a deposit that would create a `0x00`-credential validator. Every
other Gloas epoch substep and accessor is `inherit`ed here verbatim: each captured Gloas/Fulu `forkdef` (the DSL stores every
`forkdef`'s source for inheritance; `SPEC_AUTHORING_MODEL.md` §8) re-elaborates in the Heze
namespace against `Heze.State` (`= SSZ.Box _ Heze.BeaconState`), its sibling calls
rebinding to the Heze copies. The order matches Gloas's so each callee is declared before
its caller.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

state_section

inherit computeEpochAtSlot
inherit reserveChurn
inherit computeStartSlotAtEpoch
inherit getCurrentEpoch
inherit getPreviousEpoch
inherit secondsToMilliseconds millisecondsToSeconds
inherit computeTimeAtSlotMs computeSlotAtTimeMs
inherit computeTimeAtSlot computeSlotAtTime
inherit BlobParameters getBlobParameters
inherit getRandaoMix
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
inherit getExitChurnLimit
inherit getActivationChurnLimit
inherit computeExitEpochAndUpdateChurn
inherit initiateValidatorExit
inherit slashValidator
inherit getDomain
inherit getPendingBalanceToWithdraw
inherit getConsolidationChurnLimit
inherit computeConsolidationEpochAndUpdateChurn
inherit queueExcessActiveBalance
inherit switchToCompoundingValidator
inherit getValidatorFromDeposit
inherit addValidatorToRegistry
inherit isValidDepositSignature

/-- `apply_pending_deposit` (Heze, EIP-8365, `heze/beacon-chain.md:291-310`): Fulu's, except
that a deposit that would create a new validator with BLS (`0x00`) withdrawal credentials is
dropped, with no refund. That covers deposits submitted before Heze too. A top-up to an
existing validator is unaffected, whatever the deposit's credentials. -/
forkdef applyPendingDeposit (deposit : PendingDeposit) : StateTransition Unit := do
  let state ← get
  match validatorIndexByPubkey? state deposit.pubkey with
  | some vi => set (← increaseBalance state (UInt64.ofNat vi) deposit.amount)
  | none    =>
      -- [New in Heze:EIP8365] do not create validators with BLS withdrawal credentials.
      if credPrefix deposit.withdrawalCredentials == Const.blsWithdrawalPrefix then return
      if isValidDepositSignature deposit.pubkey deposit.withdrawalCredentials deposit.amount deposit.signature then
        addValidatorToRegistry deposit.pubkey deposit.withdrawalCredentials deposit.amount
      else pure ()
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
inherit getBeaconProposerIndices
inherit weighJustificationAndFinalization
inherit processJustificationAndFinalization
inherit processInactivityUpdates
inherit getFlagIndexDeltas
inherit getInactivityPenaltyDeltas
inherit applyDeltas
inherit processRewardsAndPenalties
inherit processRegistryUpdates
inherit processSlashings
inherit DepositScan
inherit ppdLoop
inherit processPendingDeposits
inherit pcLoop
inherit processPendingConsolidations
inherit processEffectiveBalanceUpdates
inherit processSlashingsReset
inherit processRandaoMixesReset
-- [Modified in Heze:EIP8015] `process_eth1_data_reset` is gone with the eth1 votes it reset.
inherit processHistoricalSummariesUpdate
inherit processParticipationFlagUpdates
inherit processSyncCommitteeUpdates
inherit processProposerLookahead
inherit processBuilderPendingPayments
inherit computePtc
inherit processPtcWindow

end

end EthCLSpecs.Heze
