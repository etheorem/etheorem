import EthCLSpecs.Fulu.Containers.Validator

/-!
# `EthCLSpecs.Fulu.Containers.Eth1Data`: the eth1 deposit-contract view (load order row 6)
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The eth1 deposit-contract view. `deposit_count` is a `uint64` in the pinned container, so
it is the checked kind. No modeled function computes with it: the fork bodies copy it and the
codec reads and writes it. -/
forkcontainer Eth1Data where
  depositRoot  : Root
  depositCount : CLUint64
  blockHash    : Hash32

end EthCLSpecs.Fulu
