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

/-- `get_randao_mix(state, epoch)` (`fulu/mainnet.py:1455-1459`): the mix at
`epoch % EPOCHS_PER_HISTORICAL_VECTOR`. The modulo is total: the divisor is a positive preset
constant, so the site takes the `PositiveDivisor` route and no bind. The index is a remainder
of a positive divisor, so it is always in range (`< EPOCHS_PER_HISTORICAL_VECTOR`), and the
total `vget` read suffices. -/
forkdef getRandaoMix (epoch : Epoch) : StateTransition Bytes32 := do
  let state ← get
  let idx := (epoch % Const.epochsPerHistoricalVectorDiv).toPlainInt
  return vget (sszGet state randaoMixes) idx

end

end EthCLSpecs.Fulu
