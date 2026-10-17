import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.Fulu.Interface
import EthCLSpecs.TheoremVectors.Builders.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Bindings.Fulu`: the Fulu fork binding

The one `ForkBinding` value through which the generator's framework half
sees Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §6): the builder catalog (§9.9)
beside the presets and the scope types. Fulu's catalog is `genesis` and
`advanced`. The base fork has no parent to upgrade from, so §9.9's
`upgraded` row has no Fulu analogue, and no `withQueue` either, Fulu
predating the builder registry. `handlerOf` answers `none`: no Fulu
theorem has a pyspec-driven handler in scope yet.
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
  -- §9.9: the builder catalog, cheapest first. The `built` searcher walks
  -- the display names through the grid.
  builders   := #[("genesis",  `EthCLSpecs.TheoremVectors.Builders.Fulu.genesis),
                  ("advanced", `EthCLSpecs.TheoremVectors.Builders.Fulu.advanced)]
  handlerOf  := fun _ => none
  interface  := fun
    | .minimal => some EthCLSpecs.Fulu.Interface.fuluInterface
    | .mainnet => some EthCLSpecs.Fulu.Interface.fuluInterfaceMainnet

end EthCLSpecs.TheoremVectors.Bindings.Fulu
