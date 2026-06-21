import EthCLSpecs.Fulu.Time

/-!
# `EthCLSpecs.Fulu.Signing`: the domain accessor (load order row 21)

`get_domain(state, domain_type, epoch)` (`SPECS_ARCHITECTURE.md` §3.1 row 21).
The spec owns this, it reads `state.fork`; the framework owns the version-free
`compute_domain`. A pure read of the boxed state.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_domain(state, domain_type, epoch)`: the fork version is the previous one
before `state.fork.epoch`, the current one after, combined with the domain tag and
`genesis_validators_root`. -/
forkdef getDomain (state : State) (domainType : ByteArray) (epoch : Epoch) : Vector UInt8 32 :=
  let fk := sszGet state forkData
  let forkVersion := if epoch < fk.epoch then fk.previousVersion else fk.currentVersion
  computeDomain domainType forkVersion (sszGet state genesisValidatorsRoot)

end

end EthCLSpecs.Fulu
