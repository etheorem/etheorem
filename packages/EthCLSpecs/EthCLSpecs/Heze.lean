import EthCLSpecs.Heze.Containers
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.Interface
import EthCLSpecs.Heze.Committees
-- Load-bearing: `isValidInclusionListSignature` has no in-model caller, so this import is the
-- only path that pulls `Signing` into the build. Do not drop it as a "redundant" sibling.
import EthCLSpecs.Heze.Signing

/-!
# `EthCLSpecs.Heze`: the Heze fork (EIP-7805 FOCIL), a thin diff over Gloas

At alpha.11 Heze adds the `InclusionList`
family (PR #5371 reverted the bid change) and the `upgradeToHeze` near-passthrough. EIP-7805
changes no state transition, so the spine (the `process_slots` / `process_block` /
`process_epoch` pipeline) is the Gloas one re-instantiated over Heze types.
`EpochProcessing` / `Operations` / `Withdrawals` / `Transition` carry that
re-instantiation, pulled in via `Interface`, and the fork-interface drives every tested
runner. The as-built divergence catalogue is `IMPLEMENTATION_NOTES.md`, "Heze diff".

The FOCIL functions land in concern files, following the ePBS shape rather than a per-feature
file. `get_inclusion_list_committee` sits in the store-throwing fork-choice block
(`ForkChoice`, beside its sole caller; `Committees` keeps its unit-checkable `cyclicSample`
core); `is_valid_inclusion_list_signature` with the signing surface (`Signing`); the
`InclusionListStore` and its three helpers with fork choice (`ForkChoice`), folded into the
fork-choice `Store`.

The fork choice (`ForkChoice`) is Gloas's with the EIP-7805 inclusion-list layer added: the
`InclusionListStore` and its three helpers, folded into the fork-choice `Store`, the
`is_payload_inclusion_list_satisfied` / `record_payload_inclusion_list_satisfaction` /
`get_inclusion_list_due_ms` helpers, the `should_extend_payload` and
`on_execution_payload_envelope` overrides, and the new `on_inclusion_list` handler. FOCIL has no
behavioral conformance vector (the two new containers do pass their `ssz_static` suites), so that
layer is pinned to the spec by the build-enforced pins in `ForkChoice`, kernel `#guard`s plus
`native_decide` examples, rather than exercised by a runner. Pinned to v1.7.0-alpha.11.
-/
