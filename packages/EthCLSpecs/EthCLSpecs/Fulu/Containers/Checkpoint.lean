import EthCLSpecs.Fulu.Containers.Fork

/-!
# `EthCLSpecs.Fulu.Containers.Checkpoint`: the checkpoint container (load order row 4)

A justified / finalized checkpoint, referenced by the attestation data and the
state's justification / finalization fields (`SPECS_ARCHITECTURE.md` §3.1).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- A justified / finalized checkpoint: an epoch and the block root it names. -/
forkcontainer Checkpoint where
  epoch : Epoch
  root  : Root

end EthCLSpecs.Fulu
