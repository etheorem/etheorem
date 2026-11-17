import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. The
base-reward pair is the pyspec's checked `Gwei` chain; the finality-delay pair
runs in the raw `Epoch` until Stage 5.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`
(`fulu/mainnet.py:4380-4385`): `EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR
// integer_squareroot(get_total_active_balance(state))`. The increment and the
total active balance are `Gwei`, so the product and the division are the
checked `Gwei` operators, each tested per operation (`SPEC_ARITHMETIC.md` §4.2). -/
forkdef getBaseRewardPerIncrement (state : State) : Checked Gwei := do
  let total ← getTotalActiveBalance state
  -- TEMPORARY CROSSING (removed in Stage 6): `integer_squareroot` at the pin is
  -- a total helper over its `uint64` argument; the isqrt route stays the
  -- proved `Nat` helper, entered through the underlying-value projection.
  -- Stage 6 ports the isqrt route onto the checked surface and deletes this.
  Const.effectiveBalanceIncrementG * Const.baseRewardFactor / isqrt total.toPlainNat

/-- `get_base_reward` (`fulu/mainnet.py:1789-1795`): `increments *
get_base_reward_per_increment(state)` with
`increments = state.validators[index].effective_balance // EFFECTIVE_BALANCE_INCREMENT`.
Reads `validators[i]`, so it rejects with the `IndexError`-shaped `outOfBounds`
(`StateTransitionError`); the arithmetic rides the same channel as the typed
`ArithFault`. A monadic caller binds it through `liftErr`; a same-error caller
binds directly. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) :
    Except StateTransitionError Gwei := do
  let v ← sszGetIdx (sszGet state validators) i.toNat
  let increments ← v.effectiveBalance / Const.effectiveBalanceIncrementG
  let base ← getBaseRewardPerIncrement state
  let total ← increments * base
  return total

/-- `get_finality_delay`. -/
forkdef getFinalityDelay (state : State) : Epoch :=
  let prevEpoch := previousEpochOf state
  prevEpoch - (sszGet state finalizedCheckpoint).epoch

/-- `is_in_inactivity_leak`. -/
forkdef isInInactivityLeak (state : State) : Bool :=
  getFinalityDelay state > Const.minEpochsToInactivityPenalty

end

end EthCLSpecs.Fulu
