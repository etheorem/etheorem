import EthCLSpecs.Heze.Fork
import EthCLSpecs.Heze.Types
import EthCLSpecs.Heze.Constants
import EthCLSpecs.Heze.Containers
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.Interface
import EthCLSpecs.Heze.Committees
import EthCLSpecs.Heze.Signing

/-!
# `EthCLSpecs.Heze`: the Heze fork (EIP-7805 FOCIL), a thin diff over Gloas

At v1.7.0-beta.4 Heze adds the `InclusionList` family and an `inclusion_list_bits` field on
`ExecutionPayloadBid` (EIP-7805), removes the eth1 deposit machinery (EIP-8015: four
`BeaconState` fields, two `BeaconBlockBody` fields, `process_eth1_data` and its reset), and stops
new validators with BLS withdrawal credentials (EIP-8365). `upgradeToHeze` asserts the old
deposit mechanism is drained, carries the Gloas state across, and leaves the bitvector empty.
The spine (the `process_slots` / `process_block` / `process_epoch` pipeline) is the Gloas one
re-instantiated over Heze types, with the EIP-8015 steps removed.
`EpochProcessing` / `Operations` / `Withdrawals` / `Transition` carry that
re-instantiation, pulled in via `Interface`, and the fork-interface drives every tested
runner. The as-built divergence catalogue is `IMPLEMENTATION_NOTES.md`, "Heze diff".

The FOCIL functions land in concern files, following the ePBS shape rather than a per-feature
file. `get_inclusion_list_committee` sits in the store-throwing fork-choice block
(`ForkChoice`, beside its sole caller; `Committees` keeps its unit-checkable `cyclicSample`
core); `is_valid_inclusion_list_signature` with the signing surface (`Signing`); the
`InclusionListStore` and its four helpers with fork choice (`ForkChoice`), folded into the
fork-choice `Store`.

The fork choice (`ForkChoice`) is Gloas's with the EIP-7805 inclusion-list layer added: the
`InclusionListStore` and its four helpers (`process_inclusion_list`,
`get_inclusion_list_transactions`, `get_inclusion_list_bits`, `is_inclusion_list_bits_inclusive`),
folded into the fork-choice `Store` and keyed by `(slot, dependent_root)`, the
`is_payload_inclusion_list_satisfied` / `record_payload_inclusion_list_satisfaction` /
`get_inclusion_list_due_ms` helpers, the `should_extend_payload` and
`on_execution_payload_envelope` overrides, and the new `on_inclusion_list` handler. FOCIL has no
behavioral conformance vector (the two new containers do pass their `ssz_static` suites), so that
layer is pinned to the spec by the build-enforced pins in `EthCLSpecs.Tests.HezeForkChoicePins`,
kernel `#guard`s plus `native_decide` examples, rather than exercised by a runner. Pinned to
v1.7.0-beta.4.
-/
