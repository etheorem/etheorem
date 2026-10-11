import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Fulu.Interface

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Fulu`: the Fulu fork binding

The one `ForkBinding` value through which the generator's framework half
sees Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §6). Stage 1 carries an empty builder catalog
and a `handlerOf` that answers `none`, per the plan's step 6; stages 6 and
7 fill both.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Fulu

/-- The Fulu binding. -/
def fulu : ForkBinding where
  fork       := `EthCLSpecs.Fulu
  tag        := "fulu"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Fulu.minimal,
                              `EthCLSpecs.Fulu.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Fulu.mainnet,
                              `EthCLSpecs.Fulu.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Fulu.BeaconState
  -- §1.2: the block types put a theorem out of scope. Fulu predates the
  -- execution-payload envelope, so its list carries no envelope type.
  blockTypes := #[`EthCLSpecs.Fulu.BeaconBlock,
                  `EthCLSpecs.Fulu.SignedBeaconBlock,
                  `EthCLSpecs.Fulu.BeaconBlockBody,
                  `EthCLSpecs.Fulu.ExecutionPayload,
                  `EthCLSpecs.Fulu.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Fulu, `EthCLSpecs.Proofs.Fulu]
  builders   := #[]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Fulu.Interface.fuluInterface
    | .mainnet => some EthCLSpecs.Fulu.Interface.fuluInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Fulu
