import EthCLSpecs.Heze.Containers
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.Interface
import EthCLSpecs.Heze.Focil

/-!
# `EthCLSpecs.Heze`: the Heze fork (EIP-7805 FOCIL), a thin diff over Gloas

At alpha.11 Heze adds only the `InclusionList` family (PR #5371 reverted the bid change)
and the `upgradeToHeze` near-passthrough. EIP-7805 changes no state transition or fork
choice, so the spine is the Gloas spine re-instantiated over Heze types
(`EpochProcessing` / `Operations` / `Withdrawals` / `Transition` / `ForkChoice`, pulled in
via `Interface`); the fork-interface drives every tested runner. The spec-complete FOCIL
machinery (`on_inclusion_list`, the IL store) is an untested parked follow-up. Pinned to
v1.7.0-alpha.11.
-/
