import EthCLSpecs.Gloas.Inherited

/-!
# `EthCLSpecs.Gloas.Containers.Builder`: the builder-registry entry (EIP-7732)

The `Builder` record the ePBS builder registry holds (`SPECS_ARCHITECTURE.md`
§3.1, §4.1). The first Gloas ePBS container.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- A builder-registry entry. -/
forkcontainer Builder where
  pubkey            : BLSPubkey
  version           : UInt8
  executionAddress  : ExecutionAddress
  balance           : Gwei
  depositEpoch      : Epoch
  withdrawableEpoch : Epoch

end EthCLSpecs.Gloas
