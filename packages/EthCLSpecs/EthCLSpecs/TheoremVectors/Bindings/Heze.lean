import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Heze.Interface
import EthCLSpecs.TheoremVectors.Builders.Heze

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Heze`: the Heze fork binding

The one `ForkBinding` value through which the generator's framework half
sees Heze (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. The catalog's four rows walk
`genesis`, `advanced`, `upgraded`, and `withQueue`, the same grid Gloas
walks. The fork-version seam is what lets the `[Config]`-generic bodies
write the fork record: `Heze/Constants.lean` carries `hezeForkVersion`
in the config tier, beside its pinned plain defs. `handlerOf` answers
`none`: no Heze theorem has a pyspec-driven handler in scope yet.

The `pyspecNames` table carries the pyspec spelling of every
function the fork owns, beside `handlerOf` and `builders`; the
statement reader looks a discovered target up in it (§6).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Heze

/-- The Heze binding. -/
def heze : ForkBinding where
  fork       := `EthCLSpecs.Heze
  tag        := "heze"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Heze.minimal,
                              `EthCLSpecs.Heze.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Heze.mainnet,
                              `EthCLSpecs.Heze.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Heze.BeaconState
  -- §1.2: the block types put a theorem out of scope. Heze keeps Gloas's
  -- list, the envelope included.
  blockTypes := #[`EthCLSpecs.Heze.BeaconBlock,
                  `EthCLSpecs.Heze.SignedBeaconBlock,
                  `EthCLSpecs.Heze.BeaconBlockBody,
                  `EthCLSpecs.Heze.ExecutionPayload,
                  `EthCLSpecs.Heze.SignedExecutionPayloadEnvelope,
                  `EthCLSpecs.Heze.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Heze, `EthCLSpecs.Proofs.Heze]
  -- §9.9: the builder catalog, cheapest first. The display names match
  -- Gloas's, because the built grid walks display names and the two
  -- forks walk the same four steps.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Heze.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Heze.advanced),
                  ("upgraded", `EthCLSpecs.TheoremVectors.Builders.Heze.upgraded),
                  ("withQueue", `EthCLSpecs.TheoremVectors.Builders.Heze.withQueue)]
  -- §6: the pyspec spelling of the fork's spec functions, one row per
  -- function the fork owns. The statement reader looks a discovered
  -- target up in the table, and a target with no row answers `none`.
  pyspecNames :=
    #[
      (`EthCLSpecs.Heze.processInclusionList, "process_inclusion_list"),
      (`EthCLSpecs.Heze.getInclusionListDueMs, "get_inclusion_list_due_ms"),
      (`EthCLSpecs.Heze.onInclusionList, "on_inclusion_list"),
      (`EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction, "record_payload_inclusion_list_satisfaction"),
      (`EthCLSpecs.Heze.onExecutionPayloadEnvelope, "on_execution_payload_envelope"),
      (`EthCLSpecs.Heze.getInclusionListTransactions, "get_inclusion_list_transactions"),
      (`EthCLSpecs.Heze.isPayloadInclusionListSatisfied, "is_payload_inclusion_list_satisfied"),
      (`EthCLSpecs.Heze.getForkchoiceStore, "get_forkchoice_store"),
      (`EthCLSpecs.Heze.isInclusionListSatisfied, "is_inclusion_list_satisfied"),
      (`EthCLSpecs.Heze.getInclusionListCommittee, "get_inclusion_list_committee"),
      (`EthCLSpecs.Heze.shouldExtendPayload, "should_extend_payload"),
      (`EthCLSpecs.Heze.balanceAfterWithdrawals, "get_balance_after_withdrawals")
      -- No row for `isValidInclusionListSignature`: its `def` lives in
      -- `EthCLSpecs.Heze.Signing`, which no generator module imports, so
      -- the constant is not in the header's environment and no target
      -- the generator reads can name it.
    ]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Heze.Interface.hezeInterface
    | .mainnet => some EthCLSpecs.Heze.Interface.hezeInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Heze
