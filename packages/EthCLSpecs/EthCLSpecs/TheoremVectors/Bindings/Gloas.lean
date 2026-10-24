import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Gloas.Interface
import EthCLSpecs.TheoremVectors.Builders.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Gloas`: the Gloas fork binding

The one `ForkBinding` value through which the generator's framework half
sees Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. The `handlerOf` map names the pyspec
runner and handler for each epoch-processing substep the fork drives
(§6, §13.4). Every other function answers `none`, so the epoch_processing
format accepts no record that targets it.

The `pyspecNames` table carries the pyspec spelling of every
function the fork owns, beside `handlerOf` and `builders`; the
statement reader looks a discovered target up in it (§6).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Gloas

/-- The Gloas binding. -/
def gloas : ForkBinding where
  fork       := `EthCLSpecs.Gloas
  tag        := "gloas"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Gloas.minimal,
                              `EthCLSpecs.Gloas.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Gloas.mainnet,
                              `EthCLSpecs.Gloas.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Gloas.BeaconState
  -- §1.2: the block types put a theorem out of scope. Gloas adds the
  -- execution-payload envelope to Fulu's list.
  blockTypes := #[`EthCLSpecs.Gloas.BeaconBlock,
                  `EthCLSpecs.Gloas.SignedBeaconBlock,
                  `EthCLSpecs.Gloas.BeaconBlockBody,
                  `EthCLSpecs.Gloas.ExecutionPayload,
                  `EthCLSpecs.Gloas.SignedExecutionPayloadEnvelope,
                  `EthCLSpecs.Gloas.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Gloas, `EthCLSpecs.Proofs.Gloas]
  -- §9.9: the builder catalog, cheapest first. The `built` searcher walks
  -- the display names through the grid.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Gloas.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Gloas.advanced),
                  ("upgraded", `EthCLSpecs.TheoremVectors.Builders.Gloas.upgraded),
                  ("withQueue", `EthCLSpecs.TheoremVectors.Builders.Gloas.withQueue)]
  -- §6, §13.4: the epoch-processing substeps the pyspec `epoch_processing`
  -- runner drives, each mapped to `(runner, handler)`. The arms follow the
  -- dispatch order of `EthCLSpecs.Gloas.Interface.runEpochSubstepImpl`, so a
  -- reader can diff the two side by side. The map stops at the
  -- `epoch_processing` substeps; every other function gets no entry. The
  -- `pending_deposits_churn` handler runs the same substep body, so
  -- `pending_deposits` stays the one canonical entry for it.
  handlerOf  := fun
    | `EthCLSpecs.Gloas.processSlashingsReset               =>
        some ("epoch_processing", "slashings_reset")
    | `EthCLSpecs.Gloas.processRandaoMixesReset             =>
        some ("epoch_processing", "randao_mixes_reset")
    | `EthCLSpecs.Gloas.processEth1DataReset                =>
        some ("epoch_processing", "eth1_data_reset")
    | `EthCLSpecs.Gloas.processHistoricalSummariesUpdate    =>
        some ("epoch_processing", "historical_summaries_update")
    | `EthCLSpecs.Gloas.processParticipationFlagUpdates     =>
        some ("epoch_processing", "participation_flag_updates")
    | `EthCLSpecs.Gloas.processJustificationAndFinalization =>
        some ("epoch_processing", "justification_and_finalization")
    | `EthCLSpecs.Gloas.processInactivityUpdates            =>
        some ("epoch_processing", "inactivity_updates")
    | `EthCLSpecs.Gloas.processRewardsAndPenalties          =>
        some ("epoch_processing", "rewards_and_penalties")
    | `EthCLSpecs.Gloas.processRegistryUpdates              =>
        some ("epoch_processing", "registry_updates")
    | `EthCLSpecs.Gloas.processSlashings                    =>
        some ("epoch_processing", "slashings")
    | `EthCLSpecs.Gloas.processEffectiveBalanceUpdates      =>
        some ("epoch_processing", "effective_balance_updates")
    | `EthCLSpecs.Gloas.processPendingDeposits              =>
        some ("epoch_processing", "pending_deposits")
    | `EthCLSpecs.Gloas.processPendingConsolidations        =>
        some ("epoch_processing", "pending_consolidations")
    | `EthCLSpecs.Gloas.processBuilderPendingPayments       =>
        some ("epoch_processing", "builder_pending_payments")
    | `EthCLSpecs.Gloas.processSyncCommitteeUpdates         =>
        some ("epoch_processing", "sync_committee_updates")
    | `EthCLSpecs.Gloas.processProposerLookahead            =>
        some ("epoch_processing", "proposer_lookahead")
    | `EthCLSpecs.Gloas.processPtcWindow                    =>
        some ("epoch_processing", "ptc_window")
    | _ => none
  -- §6: the pyspec spelling of the fork's spec functions, one row per
  -- function the fork owns. The statement reader looks a discovered
  -- target up in the table, and a target with no row answers `none`.
  pyspecNames :=
    #[
      (`EthCLSpecs.Gloas.getPendingPartialWithdrawals, "get_pending_partial_withdrawals"),
      (`EthCLSpecs.Gloas.computePtcFromFulu, "compute_ptc"),
      (`EthCLSpecs.Gloas.initiateBuilderExit, "initiate_builder_exit"),
      (`EthCLSpecs.Gloas.notifyPtcMessages, "notify_ptc_messages"),
      (`EthCLSpecs.Gloas.getCheckpointBlock, "get_checkpoint_block"),
      (`EthCLSpecs.Gloas.shouldExtendPayload, "should_extend_payload"),
      (`EthCLSpecs.Gloas.onPayloadAttestationMessage, "on_payload_attestation_message"),
      (`EthCLSpecs.Gloas.getAttestationParticipationFlagIndices, "get_attestation_participation_flag_indices"),
      (`EthCLSpecs.Gloas.getProposerScore, "get_proposer_score"),
      (`EthCLSpecs.Gloas.isPendingValidator, "is_pending_validator"),
      (`EthCLSpecs.Gloas.onTick, "on_tick"),
      (`EthCLSpecs.Gloas.addBuilderToRegistry, "add_builder_to_registry"),
      (`EthCLSpecs.Gloas.getBeaconProposerIndices, "get_beacon_proposer_indices"),
      (`EthCLSpecs.Gloas.onAttesterSlashing, "on_attester_slashing"),
      (`EthCLSpecs.Gloas.payloadTimeliness, "payload_timeliness"),
      (`EthCLSpecs.Gloas.getIndexedPayloadAttestation, "get_indexed_payload_attestation"),
      (`EthCLSpecs.Gloas.stateTransition, "state_transition"),
      (`EthCLSpecs.Gloas.balanceAfterWithdrawals, "get_balance_after_withdrawals"),
      (`EthCLSpecs.Gloas.processBuilderExitRequest, "process_builder_exit_request"),
      (`EthCLSpecs.Gloas.getNodeChildren, "get_node_children"),
      (`EthCLSpecs.Gloas.validateOnAttestation, "validate_on_attestation"),
      (`EthCLSpecs.Gloas.processOperations, "process_operations"),
      (`EthCLSpecs.Gloas.getCurrentStoreEpoch, "get_current_store_epoch"),
      (`EthCLSpecs.Gloas.isActiveBuilder, "is_active_builder"),
      (`EthCLSpecs.Gloas.onboardBuildersFromPendingDeposits, "onboard_builders_from_pending_deposits"),
      (`EthCLSpecs.Gloas.isBuilderIndex, "is_builder_index"),
      (`EthCLSpecs.Gloas.getPayloadStatusTiebreaker, "get_payload_status_tiebreaker"),
      (`EthCLSpecs.Gloas.getCurrentSlot, "get_current_slot"),
      (`EthCLSpecs.Gloas.updateProposerBoostRoot, "update_proposer_boost_root"),
      (`EthCLSpecs.Gloas.onBlock, "on_block"),
      (`EthCLSpecs.Gloas.processSlots, "process_slots"),
      (`EthCLSpecs.Gloas.isValidBuilderDepositSignature, "is_valid_builder_deposit_signature"),
      (`EthCLSpecs.Gloas.getFilteredBlockTree, "get_filtered_block_tree"),
      (`EthCLSpecs.Gloas.recordBlockTimeliness, "record_block_timeliness"),
      (`EthCLSpecs.Gloas.updateUnrealizedCheckpoints, "update_unrealized_checkpoints"),
      (`EthCLSpecs.Gloas.isParentNodeFull, "is_parent_node_full"),
      (`EthCLSpecs.Gloas.processEpoch, "process_epoch"),
      (`EthCLSpecs.Gloas.isHeadWeak, "is_head_weak"),
      (`EthCLSpecs.Gloas.applyParentExecutionPayload, "apply_parent_execution_payload"),
      (`EthCLSpecs.Gloas.processPayloadAttestation, "process_payload_attestation"),
      (`EthCLSpecs.Gloas.updateCheckpoints, "update_checkpoints"),
      (`EthCLSpecs.Gloas.applyWithdrawals, "apply_withdrawals"),
      (`EthCLSpecs.Gloas.onAttestation, "on_attestation"),
      (`EthCLSpecs.Gloas.isValidIndexedPayloadAttestation, "is_valid_indexed_payload_attestation"),
      (`EthCLSpecs.Gloas.getDependentRoot, "get_dependent_root"),
      (`EthCLSpecs.Gloas.settleBuilderPayment, "settle_builder_payment"),
      (`EthCLSpecs.Gloas.calculateCommitteeFraction, "calculate_committee_fraction"),
      (`EthCLSpecs.Gloas.getExpectedWithdrawals, "get_expected_withdrawals"),
      (`EthCLSpecs.Gloas.getParentPayloadStatus, "get_parent_payload_status"),
      (`EthCLSpecs.Gloas.computePtc, "compute_ptc"),
      (`EthCLSpecs.Gloas.getSupportedNode, "get_supported_node"),
      (`EthCLSpecs.Gloas.initializePtcWindow, "initialize_ptc_window"),
      (`EthCLSpecs.Gloas.processAttestation, "process_attestation"),
      (`EthCLSpecs.Gloas.storeTargetCheckpointState, "store_target_checkpoint_state"),
      (`EthCLSpecs.Gloas.getForkchoiceStore, "get_forkchoice_store"),
      (`EthCLSpecs.Gloas.getWeight, "get_weight"),
      (`EthCLSpecs.Gloas.isDataAvailable, "is_data_available"),
      (`EthCLSpecs.Gloas.timeIntoSlotMs, "time_into_slot"),
      (`EthCLSpecs.Gloas.applyDepositForBuilder, "apply_deposit_for_builder"),
      (`EthCLSpecs.Gloas.updateLatestMessages, "update_latest_messages"),
      (`EthCLSpecs.Gloas.processBuilderDepositRequest, "process_builder_deposit_request"),
      (`EthCLSpecs.Gloas.processWithdrawals, "process_withdrawals"),
      (`EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex, "convert_builder_index_to_validator_index"),
      (`EthCLSpecs.Gloas.getHead, "get_head"),
      (`EthCLSpecs.Gloas.Const.attestationTimelinessIndex, "block_timeliness"),
      (`EthCLSpecs.Gloas.verifyExecutionPayloadBidSignature, "verify_execution_payload_bid_signature"),
      (`EthCLSpecs.Gloas.getPendingBalanceToWithdrawForBuilder, "get_pending_balance_to_withdraw_for_builder"),
      (`EthCLSpecs.Gloas.getAncestor, "get_ancestor"),
      (`EthCLSpecs.Gloas.isPayloadVerified, "is_payload_verified"),
      (`EthCLSpecs.Gloas.payloadDataAvailability, "payload_data_availability"),
      (`EthCLSpecs.Gloas.getBuildersSweepWithdrawals, "get_builders_sweep_withdrawals"),
      (`EthCLSpecs.Gloas.processProposerSlashing, "process_proposer_slashing"),
      (`EthCLSpecs.Gloas.getIndexForNewBuilder, "get_index_for_new_builder"),
      (`EthCLSpecs.Gloas.processParentExecutionPayload, "process_parent_execution_payload"),
      (`EthCLSpecs.Gloas.verifyAndNotifyNewPayload, "verify_and_notify_new_payload"),
      (`EthCLSpecs.Gloas.onTickPerSlot, "on_tick_per_slot"),
      (`EthCLSpecs.Gloas.onExecutionPayloadEnvelope, "on_execution_payload_envelope"),
      (`EthCLSpecs.Gloas.shouldApplyProposerBoost, "should_apply_proposer_boost"),
      (`EthCLSpecs.Gloas.processExecutionPayloadBid, "process_execution_payload_bid"),
      (`EthCLSpecs.Gloas.computePulledUpTip, "compute_pulled_up_tip"),
      (`EthCLSpecs.Gloas.getPtc, "get_ptc"),
      (`EthCLSpecs.Gloas.getValidatorsSweepWithdrawals, "get_validators_sweep_withdrawals"),
      (`EthCLSpecs.Gloas.isAncestor, "is_ancestor"),
      (`EthCLSpecs.Gloas.isPreviousSlotPayloadDecision, "is_previous_slot_payload_decision"),
      (`EthCLSpecs.Gloas.isParentStrong, "is_parent_strong"),
      (`EthCLSpecs.Gloas.filterBlockTree, "filter_block_tree"),
      (`EthCLSpecs.Gloas.getAttestationScore, "get_attestation_score"),
      (`EthCLSpecs.Gloas.processPtcWindow, "process_ptc_window"),
      (`EthCLSpecs.Gloas.processBlock, "process_block"),
      (`EthCLSpecs.Gloas.getBuilderWithdrawals, "get_builder_withdrawals"),
      (`EthCLSpecs.Gloas.isAttestationSameSlot, "is_attestation_same_slot"),
      (`EthCLSpecs.Gloas.isBuilderWithdrawalCredential, "is_builder_withdrawal_credential"),
      (`EthCLSpecs.Gloas.getSlotsSinceGenesis, "get_slots_since_genesis"),
      (`EthCLSpecs.Gloas.processSlot, "process_slot"),
      (`EthCLSpecs.Gloas.toBuilderIndex, "convert_validator_index_to_builder_index"),
      (`EthCLSpecs.Gloas.canBuilderCoverBid, "can_builder_cover_bid"),
      (`EthCLSpecs.Gloas.verifyExecutionPayloadEnvelopeSignature, "verify_execution_payload_envelope_signature"),
      (`EthCLSpecs.Gloas.getVotingSource, "get_voting_source"),
      (`EthCLSpecs.Gloas.processBuilderPendingPayments, "process_builder_pending_payments"),
      (`EthCLSpecs.Gloas.verifyExecutionPayloadEnvelope, "verify_execution_payload_envelope")
    ]
  interface  := fun
    | .minimal => some EthCLSpecs.Gloas.Interface.gloasInterface
    | .mainnet => some EthCLSpecs.Gloas.Interface.gloasInterfaceMainnet

-- The exhaustive guard over all seventeen pairs exists because a
-- single-backtick name literal falls back to the raw name when the
-- constant does not exist. A misspelled arm name in `handlerOf` would
-- answer `none` for the real constant and the build would stay green,
-- so only this list catches it. The targeted guards below keep the
-- entries the recipes rely on named at the read site.
#guard [(`EthCLSpecs.Gloas.processSlashingsReset, "slashings_reset"),
        (`EthCLSpecs.Gloas.processRandaoMixesReset, "randao_mixes_reset"),
        (`EthCLSpecs.Gloas.processEth1DataReset, "eth1_data_reset"),
        (`EthCLSpecs.Gloas.processHistoricalSummariesUpdate,
          "historical_summaries_update"),
        (`EthCLSpecs.Gloas.processParticipationFlagUpdates,
          "participation_flag_updates"),
        (`EthCLSpecs.Gloas.processJustificationAndFinalization,
          "justification_and_finalization"),
        (`EthCLSpecs.Gloas.processInactivityUpdates, "inactivity_updates"),
        (`EthCLSpecs.Gloas.processRewardsAndPenalties,
          "rewards_and_penalties"),
        (`EthCLSpecs.Gloas.processRegistryUpdates, "registry_updates"),
        (`EthCLSpecs.Gloas.processSlashings, "slashings"),
        (`EthCLSpecs.Gloas.processEffectiveBalanceUpdates,
          "effective_balance_updates"),
        (`EthCLSpecs.Gloas.processPendingDeposits, "pending_deposits"),
        (`EthCLSpecs.Gloas.processPendingConsolidations,
          "pending_consolidations"),
        (`EthCLSpecs.Gloas.processBuilderPendingPayments,
          "builder_pending_payments"),
        (`EthCLSpecs.Gloas.processSyncCommitteeUpdates,
          "sync_committee_updates"),
        (`EthCLSpecs.Gloas.processProposerLookahead, "proposer_lookahead"),
        (`EthCLSpecs.Gloas.processPtcWindow, "ptc_window")].all
  fun (n, h) => gloas.handlerOf n == some ("epoch_processing", h)

-- The `builder_pending_payments` entry, the one a vector needs now.
#guard gloas.handlerOf `EthCLSpecs.Gloas.processBuilderPendingPayments ==
  some ("epoch_processing", "builder_pending_payments")

-- The `justification_and_finalization` entry.
#guard gloas.handlerOf `EthCLSpecs.Gloas.processJustificationAndFinalization ==
  some ("epoch_processing", "justification_and_finalization")

-- The `ptc_window` entry, the last arm of the interface dispatch.
#guard gloas.handlerOf `EthCLSpecs.Gloas.processPtcWindow ==
  some ("epoch_processing", "ptc_window")

-- An operation helper no pyspec runner drives gets no handler.
#guard gloas.handlerOf `EthCLSpecs.Gloas.initiateBuilderExit == none

end EthCLSpecs.TheoremVectors.Bindings.Gloas
