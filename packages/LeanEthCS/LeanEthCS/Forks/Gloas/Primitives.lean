import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.Primitives`: Gloas / EIP-7732 (ePBS) primitives

Gloas introduces Enshrined Proposer-Builder Separation (EIP-7732).
The protocol tracks a separate `Builder` registry alongside the
validator registry; this file defines the `BuilderIndex` primitive
that indexes into it.

Other Gloas constants (`PTC_SIZE`, `MAX_PAYLOAD_ATTESTATIONS`,
`BUILDER_REGISTRY_LIMIT`, `BUILDER_PENDING_WITHDRAWALS_LIMIT`,
`MAX_BUILDERS_PER_WITHDRAWALS_SWEEP`) live in `LeanEthCS.Preset`.
-/

set_option autoImplicit false

namespace LeanEthCS

open SizzLean

/-- Index into the builder registry (EIP-7732 ePBS). `uint64`. -/
abbrev BuilderIndex := UInt64

end LeanEthCS
