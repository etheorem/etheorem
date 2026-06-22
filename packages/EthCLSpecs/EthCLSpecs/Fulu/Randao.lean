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
(`< EPOCHS_PER_HISTORICAL_VECTOR`), so the total `vget` read suffices. -/
forkdef getRandaoMix (epoch : Epoch) : StateTransition Bytes32 := do
  let state ← get
  let idx := (epoch % UInt64.ofNat Const.epochsPerHistoricalVector).toNat
  return vget (sszGet state randaoMixes) idx

end

end EthCLSpecs.Fulu
