import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. The
base-reward pair is the pyspec's checked `Gwei` chain, and the finality-delay pair is
the checked `Epoch` subtraction.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`
(`fulu/mainnet.py:4380-4385`): `EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR
// integer_squareroot(get_total_active_balance(state))`. The increment and the
total active balance are `Gwei`, so the product and the division are the
checked `Gwei` operators, each tested per operation (`SPEC_ARITHMETIC.md` §4.2).
`integer_squareroot(n: Uint64) -> Uint64` is total, with the pinned special case at
`UINT64_MAX` (`CLUint64.integerSquareroot`), so the root is a checked value and the
division is the checked `Uint64` operator, which raises on a zero root. Python
evaluates the left operand of `//` first, so the product binds before the total
active balance forms. -/
forkdef getBaseRewardPerIncrement (state : State) : Except StateTransitionError Gwei := do
  let numerator ← Const.effectiveBalanceIncrementG * Const.baseRewardFactor
  let total ← getTotalActiveBalance state
  let perIncrement ← numerator / total.integerSquareroot
  return perIncrement

/-- `get_base_reward` (`fulu/mainnet.py:1789-1794`): `increments *
get_base_reward_per_increment(state)` with
`increments = state.validators[index].effective_balance // EFFECTIVE_BALANCE_INCREMENT`.
Reads `validators[i]`, so it rejects with the `IndexError`-shaped `outOfBounds`
(`StateTransitionError`). The checked divide and product lift their `ArithFault` into
the same error type. A monadic caller binds it through `liftErr`; a same-error caller
binds directly. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) :
    Except StateTransitionError Gwei := do
  let v ← sszGetIdx state.validators i
  let increments ← v.effectiveBalance / Const.effectiveBalanceIncrementG
  let base ← getBaseRewardPerIncrement state
  let total ← increments * base
  return total

/-- `get_finality_delay` (`fulu/mainnet.py:1797-1798`):
`get_previous_epoch(state) - state.finalized_checkpoint.epoch`. The subtraction is the
pyspec's checked `Epoch` operation and raises on underflow, so it binds and the helper
carries the fault (`SPEC_ARITHMETIC.md` §4.3). -/
forkdef getFinalityDelay (state : State) : Checked Epoch := do
  let prevEpoch := previousEpochOf state
  prevEpoch - state.finalizedCheckpoint.epoch

/-- `is_in_inactivity_leak` (`fulu/mainnet.py:1801-1802`): the finality delay exceeds
`MIN_EPOCHS_TO_INACTIVITY_PENALTY`. The comparison never raises, so the fault is the
delay's own; it binds before the comparison. -/
forkdef isInInactivityLeak (state : State) : Checked Bool := do
  let finalityDelay ← getFinalityDelay state
  pure (finalityDelay > Const.minEpochsToInactivityPenalty)

end

end EthCLSpecs.Fulu
