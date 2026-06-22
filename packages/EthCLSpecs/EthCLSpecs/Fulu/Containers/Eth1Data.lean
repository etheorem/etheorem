import EthCLSpecs.Fulu.Containers.Validator

/-!
# `EthCLSpecs.Fulu.Containers.Eth1Data`: the eth1 deposit-contract view (load order row 6)
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The eth1 deposit-contract view. -/
forkcontainer Eth1Data where
  depositRoot  : Root
  depositCount : UInt64
  blockHash    : Hash32

end EthCLSpecs.Fulu
