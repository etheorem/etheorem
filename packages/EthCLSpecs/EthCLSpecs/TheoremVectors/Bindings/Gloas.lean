import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Gloas.Interface
import EthCLSpecs.TheoremVectors.Builders.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Gloas`: the Gloas fork binding

The one `ForkBinding` value through which the generator's framework half
sees Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types, and a `handlerOf` that answers
`none` until the pyspec format's stage fills it.
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
  -- §9.9: the builder catalog, cheapest first. The `built` source walks
  -- the display names through the grid.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Gloas.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Gloas.advanced),
                  ("upgraded", `EthCLSpecs.TheoremVectors.Builders.Gloas.upgraded),
                  ("withQueue", `EthCLSpecs.TheoremVectors.Builders.Gloas.withQueue)]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Gloas.Interface.gloasInterface
    | .mainnet => some EthCLSpecs.Gloas.Interface.gloasInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Gloas
