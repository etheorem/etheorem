import EthCLSpecs.Fulu.Signing

/-!
# `EthCLSpecs.Fulu.Randao`: the RANDAO mix accessor (load order row 22)

`get_randao_mix(state, epoch)` = `state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR]`.
A monadic accessor over the threaded state.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_randao_mix(state, epoch)`. The index is always in range
(`< EPOCHS_PER_HISTORICAL_VECTOR`), so the total `vget` read suffices. The modulo is the
pyspec's checked `Epoch` operation, so it binds (`SPEC_ARITHMETIC.md` §4.3); the
underlying-value projection feeds the total read, the use the mod bound permits (§4.5). -/
forkdef getRandaoMix (epoch : Epoch) : StateTransition Bytes32 := do
  let state ← get
  let idx ← epoch % Const.epochsPerHistoricalVectorC
  return vget (sszGet state randaoMixes) idx.toPlainNat

end

end EthCLSpecs.Fulu
