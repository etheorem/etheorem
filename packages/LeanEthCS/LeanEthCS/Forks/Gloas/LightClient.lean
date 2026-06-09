import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.LightClient`: Gloas / EIP-7732 light-client header

EIP-7732 strips the `ExecutionPayloadHeader` from the light-client
header (since ePBS moves the payload outside the beacon block) and
replaces it with a bare `execution_block_hash : Hash32`. The
inclusion proof depth shrinks accordingly. `ExecutionBranch`
covers the now-shallower Merkle path from the block hash to the
beacon-block root.

The remaining light-client containers (`LightClientBootstrap`,
`LightClientUpdate`, `LightClientFinalityUpdate`,
`LightClientOptimisticUpdate`, `LightClientStore`) carry this
modified `LightClientHeader` but are otherwise unchanged structurally.
Port them as a follow-up.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0 (BeaconBlockHeader)

/-- Depth of the Merkle inclusion proof from `execution_block_hash`
to the beacon-block root. Gloas value: 4 (preset-invariant). -/
def EXECUTION_PROOF_DEPTH : Nat := 4

/-- Inclusion proof for `execution_block_hash` in the beacon-block
root. EIP-7732 keeps this preset-invariant. -/
abbrev ExecutionBranch := Vector Root 4

/-- Gloas `LightClientHeader`: execution-side data is now just the
execution block hash plus its inclusion proof. -/
structure LightClientHeader where
  beacon              : BeaconBlockHeader
  executionBlockHash  : Hash32
  executionBranch     : ExecutionBranch
  deriving SSZRepr

end LeanEthCS.Forks.Gloas
