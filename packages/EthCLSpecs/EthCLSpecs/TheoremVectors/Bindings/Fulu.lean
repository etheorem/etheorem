import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Fulu.Interface
import EthCLSpecs.TheoremVectors.Builders.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Fulu`: the Fulu fork binding

The one `ForkBinding` value through which the generator's framework half
sees Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. Fulu's catalog is `genesis` and
`advanced`. The base fork has no parent to upgrade from, so §9.9's
`upgraded` row has no Fulu analogue, and no `withQueue` either, Fulu
predating the builder registry. `handlerOf` carries one row so far:
`processConsolidationRequest` as the `operations/consolidation_request`
handler. The theorems that write through it come in the following stage.

The `pyspecNames` table carries the pyspec spelling of every
function the fork owns, beside `handlerOf` and `builders`; the
statement reader looks a discovered target up in it (§6).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Fulu

/-- The Fulu binding. -/
def fulu : ForkBinding where
  fork       := `EthCLSpecs.Fulu
  tag        := "fulu"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Fulu.minimal,
                              `EthCLSpecs.Fulu.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Fulu.mainnet,
                              `EthCLSpecs.Fulu.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Fulu.BeaconState
  -- §1.2: the block types put a theorem out of scope. Fulu predates the
  -- execution-payload envelope, so its list carries no envelope type.
  blockTypes := #[`EthCLSpecs.Fulu.BeaconBlock,
                  `EthCLSpecs.Fulu.SignedBeaconBlock,
                  `EthCLSpecs.Fulu.BeaconBlockBody,
                  `EthCLSpecs.Fulu.ExecutionPayload,
                  `EthCLSpecs.Fulu.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Fulu, `EthCLSpecs.Proofs.Fulu]
  -- §9.9: the builder catalog, cheapest first. The `built` searcher walks
  -- the display names through the grid.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Fulu.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Fulu.advanced)]
  -- §6: the pyspec spelling of the fork's spec functions, one row per
  -- function the fork owns. The statement reader looks a discovered
  -- target up in the table, and a target with no row answers `none`.
  pyspecNames :=
    #[
      (`EthCLSpecs.Fulu.processEth1Data, "process_eth1_data"),
      (`EthCLSpecs.Fulu.getWeight, "get_weight"),
      (`EthCLSpecs.Fulu.getEligibleValidatorIndices, "get_eligible_validator_indices"),
      (`EthCLSpecs.Fulu.stateTransition, "state_transition"),
      (`EthCLSpecs.Fulu.getFlagIndexDeltas, "get_flag_index_deltas"),
      (`EthCLSpecs.Fulu.processProposerLookahead, "process_proposer_lookahead"),
      (`EthCLSpecs.Fulu.processEpoch, "process_epoch"),
      (`EthCLSpecs.Fulu.getPendingBalanceToWithdraw, "get_pending_balance_to_withdraw"),
      (`EthCLSpecs.Fulu.addValidatorToRegistry, "add_validator_to_registry"),
      (`EthCLSpecs.Fulu.verifyDataColumnSidecarKzgProofs, "verify_data_column_sidecar_kzg_proofs"),
      (`EthCLSpecs.Fulu.processAttestation, "process_attestation"),
      (`EthCLSpecs.Fulu.processOperations, "process_operations"),
      (`EthCLSpecs.Fulu.computeShuffledPermutation, "compute_shuffled_permutation"),
      (`EthCLSpecs.Fulu.getBlockRootAtSlot, "get_block_root_at_slot"),
      (`EthCLSpecs.Fulu.getPreviousEpoch, "get_previous_epoch"),
      (`EthCLSpecs.Fulu.processWithdrawals, "process_withdrawals"),
      (`EthCLSpecs.Fulu.getRandaoMix, "get_randao_mix"),
      (`EthCLSpecs.Fulu.onAttesterSlashing, "on_attester_slashing"),
      (`EthCLSpecs.Fulu.getTotalActiveBalance, "get_total_active_balance"),
      (`EthCLSpecs.Fulu.processWithdrawalRequest, "process_withdrawal_request"),
      (`EthCLSpecs.Fulu.isPartiallyWithdrawable, "is_partially_withdrawable_validator"),
      (`EthCLSpecs.Fulu.isEligibleForActivation, "is_eligible_for_activation"),
      (`EthCLSpecs.Fulu.getBeaconCommittee, "get_beacon_committee"),
      (`EthCLSpecs.Fulu.getActiveValidatorIndices, "get_active_validator_indices"),
      (`EthCLSpecs.Fulu.getCommitteeCountPerSlot, "get_committee_count_per_slot"),
      (`EthCLSpecs.Fulu.processParticipationFlagUpdates, "process_participation_flag_updates"),
      (`EthCLSpecs.Fulu.computeBalanceWeightedSelection, "compute_balance_weighted_selection"),
      (`EthCLSpecs.Fulu.isDataAvailable, "is_data_available"),
      (`EthCLSpecs.Fulu.getForkchoiceStore, "get_forkchoice_store"),
      (`EthCLSpecs.Fulu.applyDeposit, "apply_deposit"),
      (`EthCLSpecs.Fulu.isSlashableAttestationData, "is_slashable_attestation_data"),
      (`EthCLSpecs.Fulu.isEligibleForPartialWithdrawals, "is_eligible_for_partial_withdrawals"),
      (`EthCLSpecs.Fulu.processSlashings, "process_slashings"),
      (`EthCLSpecs.Fulu.getSeed, "get_seed"),
      (`EthCLSpecs.Fulu.getNextSyncCommittee, "get_next_sync_committee"),
      (`EthCLSpecs.Fulu.isHeadWeak, "is_head_weak"),
      (`EthCLSpecs.Fulu.getSlotsSinceGenesis, "get_slots_since_genesis"),
      (`EthCLSpecs.Fulu.onBlock, "on_block"),
      (`EthCLSpecs.Fulu.updateLatestMessages, "update_latest_messages"),
      (`EthCLSpecs.Fulu.processRewardsAndPenalties, "process_rewards_and_penalties"),
      (`EthCLSpecs.Fulu.processBlock, "process_block"),
      (`EthCLSpecs.Fulu.queueExcessActiveBalance, "queue_excess_active_balance"),
      (`EthCLSpecs.Fulu.filterBlockTree.getVotingSource, "get_voting_source"),
      (`EthCLSpecs.Fulu.processVoluntaryExit, "process_voluntary_exit"),
      (`EthCLSpecs.Fulu.getCommitteeIndices, "get_committee_indices"),
      (`EthCLSpecs.Fulu.getAttestationParticipationFlagIndices, "get_attestation_participation_flag_indices"),
      (`EthCLSpecs.Fulu.getBalanceChurnLimit, "get_balance_churn_limit"),
      (`EthCLSpecs.Fulu.processRandao, "process_randao"),
      (`EthCLSpecs.Fulu.processConsolidationRequest, "process_consolidation_request"),
      (`EthCLSpecs.Fulu.isValidIndexedAttestation, "is_valid_indexed_attestation"),
      (`EthCLSpecs.Fulu.verifyBlockSignature, "verify_block_signature"),
      (`EthCLSpecs.Fulu.processRegistryUpdates, "process_registry_updates"),
      (`EthCLSpecs.Fulu.filterBlockTree, "filter_block_tree"),
      (`EthCLSpecs.Fulu.processInactivityUpdates, "process_inactivity_updates"),
      (`EthCLSpecs.Fulu.getBaseRewardPerIncrement, "get_base_reward_per_increment"),
      (`EthCLSpecs.Fulu.processJustificationAndFinalization, "process_justification_and_finalization"),
      (`EthCLSpecs.Fulu.validateOnAttestation, "validate_on_attestation"),
      (`EthCLSpecs.Fulu.getUnslashedParticipatingIndices, "get_unslashed_participating_indices"),
      (`EthCLSpecs.Fulu.isFinalizationOk, "is_finalization_ok"),
      (`EthCLSpecs.Fulu.initiateValidatorExit, "initiate_validator_exit"),
      (`EthCLSpecs.Fulu.isFfgCompetitive, "is_ffg_competitive"),
      (`EthCLSpecs.Fulu.isInInactivityLeak, "is_in_inactivity_leak"),
      (`EthCLSpecs.Fulu.computeExitEpochAndUpdateChurn, "compute_exit_epoch_and_update_churn"),
      (`EthCLSpecs.Fulu.isHeadLate, "is_head_late"),
      (`EthCLSpecs.Fulu.getExpectedWithdrawals, "get_expected_withdrawals"),
      (`EthCLSpecs.Fulu.timeIntoSlotMs, "time_into_slot"),
      (`EthCLSpecs.Fulu.switchToCompoundingValidator, "switch_to_compounding_validator"),
      (`EthCLSpecs.Fulu.processExecutionPayload, "process_execution_payload"),
      (`EthCLSpecs.Fulu.computeEpochAtSlot, "compute_epoch_at_slot"),
      (`EthCLSpecs.Fulu.processHistoricalSummariesUpdate, "process_historical_summaries_update"),
      (`EthCLSpecs.Fulu.computeConsolidationEpochAndUpdateChurn, "compute_consolidation_epoch_and_update_churn"),
      (`EthCLSpecs.Fulu.processSlots, "process_slots"),
      (`EthCLSpecs.Fulu.computeTimeAtSlot, "compute_time_at_slot"),
      (`EthCLSpecs.Fulu.getConsolidationChurnLimit, "get_consolidation_churn_limit"),
      (`EthCLSpecs.Fulu.getHead, "get_head"),
      (`EthCLSpecs.Fulu.isFullyWithdrawable, "is_fully_withdrawable_validator"),
      (`EthCLSpecs.Fulu.processProposerSlashing, "process_proposer_slashing"),
      (`EthCLSpecs.Fulu.isProposingOnTime, "is_proposing_on_time"),
      (`EthCLSpecs.Fulu.processSyncAggregate, "process_sync_aggregate"),
      (`EthCLSpecs.Fulu.processSlot, "process_slot"),
      (`EthCLSpecs.Fulu.processPendingConsolidations, "process_pending_consolidations"),
      (`EthCLSpecs.Fulu.processSyncCommitteeUpdates, "process_sync_committee_updates"),
      (`EthCLSpecs.Fulu.previousEpochOf, "get_previous_epoch"),
      (`EthCLSpecs.Fulu.getBeaconProposerIndex, "get_beacon_proposer_index"),
      (`EthCLSpecs.Fulu.getActivationExitChurnLimit, "get_activation_exit_churn_limit"),
      (`EthCLSpecs.Fulu.calculateCommitteeFraction, "calculate_committee_fraction"),
      (`EthCLSpecs.Fulu.onAttestation, "on_attestation"),
      (`EthCLSpecs.Fulu.processSlashingsReset, "process_slashings_reset"),
      (`EthCLSpecs.Fulu.secondsToMilliseconds, "seconds_to_milliseconds"),
      (`EthCLSpecs.Fulu.getBeaconProposerIndices, "get_beacon_proposer_indices"),
      (`EthCLSpecs.Fulu.getProposerScore, "get_proposer_score"),
      (`EthCLSpecs.Fulu.getBlockRoot, "get_block_root"),
      (`EthCLSpecs.Fulu.isValidDepositSignature, "is_valid_deposit_signature"),
      (`EthCLSpecs.Fulu.getFinalityDelay, "get_finality_delay"),
      (`EthCLSpecs.Fulu.getTotalBalance, "get_total_balance"),
      (`EthCLSpecs.Fulu.getInactivityPenaltyDeltas, "get_inactivity_penalty_deltas"),
      (`EthCLSpecs.Fulu.computeCommittee, "compute_committee"),
      (`EthCLSpecs.Fulu.getCurrentEpoch, "get_current_epoch"),
      (`EthCLSpecs.Fulu.processEffectiveBalanceUpdates, "process_effective_balance_updates"),
      (`EthCLSpecs.Fulu.getValidatorFromDeposit, "get_validator_from_deposit"),
      (`EthCLSpecs.Fulu.verifyDataColumnSidecar, "verify_data_column_sidecar"),
      (`EthCLSpecs.Fulu.computeProposerIndices, "compute_proposer_indices"),
      (`EthCLSpecs.Fulu.processEth1DataReset, "process_eth1_data_reset"),
      (`EthCLSpecs.Fulu.increaseBalance, "increase_balance"),
      (`EthCLSpecs.Fulu.isValidSwitchToCompoundingRequest, "is_valid_switch_to_compounding_request"),
      (`EthCLSpecs.Fulu.processDeposit, "process_deposit"),
      (`EthCLSpecs.Fulu.processAttesterSlashing, "process_attester_slashing"),
      (`EthCLSpecs.Fulu.decreaseBalance, "decrease_balance"),
      (`EthCLSpecs.Fulu.processBlockHeader, "process_block_header"),
      (`EthCLSpecs.Fulu.applyPendingDeposit, "apply_pending_deposit"),
      (`EthCLSpecs.Fulu.getDomain, "get_domain"),
      (`EthCLSpecs.Fulu.balanceAfterWithdrawals, "get_balance_after_withdrawals"),
      (`EthCLSpecs.Fulu.getProposerHead, "get_proposer_head"),
      (`EthCLSpecs.Fulu.processRandaoMixesReset, "process_randao_mixes_reset"),
      (`EthCLSpecs.Fulu.computeActivationExitEpoch, "compute_activation_exit_epoch"),
      (`EthCLSpecs.Fulu.getBaseReward, "get_base_reward"),
      (`EthCLSpecs.Fulu.getAncestor, "get_ancestor"),
      (`EthCLSpecs.Fulu.processPendingDeposits, "process_pending_deposits"),
      (`EthCLSpecs.Fulu.isParentStrong, "is_parent_strong"),
      (`EthCLSpecs.Fulu.getDependentRoot, "get_dependent_root"),
      (`EthCLSpecs.Fulu.computeStartSlotAtEpoch, "compute_start_slot_at_epoch"),
      (`EthCLSpecs.Fulu.getAttestingIndices, "get_attesting_indices"),
      (`EthCLSpecs.Fulu.currentEpochOf, "get_current_epoch"),
      (`EthCLSpecs.Fulu.processDepositRequest, "process_deposit_request"),
      (`EthCLSpecs.Fulu.cbwsAux, "compute_balance_weighted_selection"),
      (`EthCLSpecs.Fulu.isShufflingStable, "is_shuffling_stable"),
      (`EthCLSpecs.Fulu.slashValidator, "slash_validator"),
      (`EthCLSpecs.Fulu.computePulledUpTip, "compute_pulled_up_tip"),
      (`EthCLSpecs.Fulu.getCurrentSlot, "get_current_slot"),
      (`EthCLSpecs.Fulu.storeTargetCheckpointState, "store_target_checkpoint_state"),
      (`EthCLSpecs.Fulu.isProposerEquivocation, "is_proposer_equivocation"),
      (`EthCLSpecs.Fulu.onTick, "on_tick"),
      (`EthCLSpecs.Fulu.getCheckpointBlock, "get_checkpoint_block"),
      (`EthCLSpecs.Fulu.processBlsToExecutionChange, "process_bls_to_execution_change")
    ]
  handlerOf  := fun
    | ``EthCLSpecs.Fulu.processConsolidationRequest =>
        some ("operations", "consolidation_request")
    | _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Fulu.Interface.fuluInterface
    | .mainnet => some EthCLSpecs.Fulu.Interface.fuluInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Fulu
