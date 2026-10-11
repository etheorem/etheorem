import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Gloas.Interface

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Gloas`: the Gloas fork binding

The one `ForkBinding` value through which the generator's framework half
sees Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §6). Stage 1 carries an empty builder catalog
and a `handlerOf` that answers `none`, per the plan's step 6; stages 6 and
7 fill both.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Gloas

/-- The Gloas binding. -/
def gloas : ForkBinding where
  fork       := `EthCLSpecs.Gloas
  tag        := "gloas"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Gloas.minimal,
                              `EthCLSpecs.Gloas.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Gloas.mainnet,
                              `EthCLSpecs.Gloas.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Gloas.BeaconState
  -- §1.2: the block types put a theorem out of scope. Gloas adds the
  -- execution-payload envelope to Fulu's list.
  blockTypes := #[`EthCLSpecs.Gloas.BeaconBlock,
                  `EthCLSpecs.Gloas.SignedBeaconBlock,
                  `EthCLSpecs.Gloas.BeaconBlockBody,
                  `EthCLSpecs.Gloas.ExecutionPayload,
                  `EthCLSpecs.Gloas.SignedExecutionPayloadEnvelope,
                  `EthCLSpecs.Gloas.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Gloas, `EthCLSpecs.Proofs.Gloas]
  builders   := #[]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Gloas.Interface.gloasInterface
    | .mainnet => some EthCLSpecs.Gloas.Interface.gloasInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Gloas
