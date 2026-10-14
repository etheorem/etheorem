import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Heze.Interface
import EthCLSpecs.TheoremVectors.Builders.Heze

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Heze`: the Heze fork binding

The one `ForkBinding` value through which the generator's framework half
sees Heze (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. The catalog's four rows walk
`genesis`, `advanced`, `upgraded`, and `withQueue`, the same grid Gloas
walks. The fork-version seam is what lets the `[Config]`-generic bodies
write the fork record: `Heze/Constants.lean` carries `hezeForkVersion`
in the config tier, beside its pinned plain defs. `handlerOf` answers
`none`: no Heze theorem has a pyspec-driven handler in scope yet.
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
  -- §9.9: the builder catalog, cheapest first. The display names match
  -- Gloas's, because the built grid walks display names and the two
  -- forks walk the same four steps.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Heze.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Heze.advanced),
                  ("upgraded", `EthCLSpecs.TheoremVectors.Builders.Heze.upgraded),
                  ("withQueue", `EthCLSpecs.TheoremVectors.Builders.Heze.withQueue)]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Heze.Interface.hezeInterface
    | .mainnet => some EthCLSpecs.Heze.Interface.hezeInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Heze
