import EthCLSpecs.Fulu.Containers.Execution

/-!
# `EthCLSpecs.Fulu.Containers.Deposit`: the deposit message (load order row 10)

The `DepositMessage` whose signing root the deposit signature covers
(`is_valid_deposit_signature`'s proof-of-possession). The full `Deposit` and
`DepositData` a block carries live with the block containers.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The deposit message whose signing root the deposit signature covers
(`is_valid_deposit_signature`'s proof-of-possession). -/
forkcontainer DepositMessage where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei

end EthCLSpecs.Fulu
