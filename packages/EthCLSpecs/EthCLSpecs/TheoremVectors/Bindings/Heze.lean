import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Heze.Interface

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Heze`: the Heze fork binding

The one `ForkBinding` value through which the generator's framework half
sees Heze (`THEOREM_VECTORS_ARCHITECTURE.md` §6). Stage 1 carries an empty builder catalog
and a `handlerOf` that answers `none`, per the plan's step 6; stages 6 and
7 fill both.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings.Heze

/-- The Heze binding. -/
def heze : ForkBinding where
  fork       := `EthCLSpecs.Heze
  tag        := "heze"
  presets    := #[(.minimal, ⟨`EthCLSpecs.Heze.minimal,
                              `EthCLSpecs.Heze.minimalConfig⟩),
                  (.mainnet, ⟨`EthCLSpecs.Heze.mainnet,
                              `EthCLSpecs.Heze.mainnetConfig⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `EthCLSpecs.Heze.BeaconState
  -- §1.2: the block types put a theorem out of scope. Heze keeps Gloas's
  -- list, the envelope included.
  blockTypes := #[`EthCLSpecs.Heze.BeaconBlock,
                  `EthCLSpecs.Heze.SignedBeaconBlock,
                  `EthCLSpecs.Heze.BeaconBlockBody,
                  `EthCLSpecs.Heze.ExecutionPayload,
                  `EthCLSpecs.Heze.SignedExecutionPayloadEnvelope,
                  `EthCLSpecs.Heze.Store]
  opens      := #[`EthCLLib.Spec, `EthCLSpecs.Heze, `EthCLSpecs.Proofs.Heze]
  builders   := #[]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Heze.Interface.hezeInterface
    | .mainnet => some EthCLSpecs.Heze.Interface.hezeInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Heze
