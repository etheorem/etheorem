import EthCLSpecs.Heze.Containers
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.Interface
import EthCLSpecs.Heze.Focil
import EthCLSpecs.Heze.InclusionList

/-!
# `EthCLSpecs.Heze`: the Heze fork (EIP-7805 FOCIL), a thin diff over Gloas

At alpha.11 Heze adds the `InclusionList` family (PR #5371 reverted the bid change) and the
`upgradeToHeze` near-passthrough. EIP-7805 changes no state transition, so the spine is the
Gloas spine re-instantiated over Heze types (`EpochProcessing` / `Operations` / `Withdrawals` /
`Transition`, pulled in via `Interface`); the fork-interface drives every tested runner.

The fork choice (`ForkChoice`) is Gloas's with the EIP-7805 inclusion-list layer added: the
`InclusionListStore` and its three helpers (`InclusionList`), folded into the fork-choice
`Store`, the `is_payload_inclusion_list_satisfied` /
`record_payload_inclusion_list_satisfaction` / `get_inclusion_list_due_ms` helpers, the
`should_extend_payload` and `on_execution_payload_envelope` overrides, and the new
`on_inclusion_list` handler. FOCIL has no conformance vector, so that layer is pinned to the
spec by the `InclusionList` module's `#guard`s rather than exercised by a runner. Pinned to
v1.7.0-alpha.11.
-/
