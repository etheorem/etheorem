import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Gloas.Interface
import EthCLSpecs.TheoremVectors.Builders.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Gloas`: the Gloas fork binding

The one `ForkBinding` value through which the generator's framework half
sees Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. The `handlerOf` map names the pyspec
runner and handler for each epoch-processing substep the fork drives
(§6, §13.4). Every other function answers `none`, so the pyspec format
accepts no record that targets it.
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
