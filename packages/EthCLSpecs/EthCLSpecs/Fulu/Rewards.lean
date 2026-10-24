import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. The base-reward
arithmetic is `uint64` (`Gwei`), as in pyspec, and each product is checked.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`: `EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR //
integer_squareroot(get_total_active_balance(state))`. pyspec evaluates the product first, as a
checked `uint64` product, and then reads the total. So a large `BASE_REWARD_FACTOR` raises
before the total read, and the body keeps that order. The total is at least one increment,
so the square root is positive. -/
forkdef getBaseRewardPerIncrement (state : State) : Except StateTransitionError Gwei := do
  let numerator ← checkedMul Const.effectiveBalanceIncrementG (UInt64.ofNat Const.baseRewardFactor)
    "get_base_reward_per_increment: EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR"
  let total ← getTotalActiveBalance state
  pure (numerator / UInt64.ofNat (isqrt total.toNat))

/-- `get_base_reward`: `increments * get_base_reward_per_increment(state)`, with
`increments = effective_balance // EFFECTIVE_BALANCE_INCREMENT`. The pyspec reads
`validators[i]` first, so an out-of-range `i` raises `IndexError` before the total. The body
reads through `sszGetIdx` (`.outOfBounds`), where `[i]!` would mask the miss with a default.
The product is a checked `uint64` product (`.arithmetic`). -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) : Except StateTransitionError Gwei := do
  let v ← sszGetIdx (sszGet state validators) i.toNat
  let increments := v.effectiveBalance / Const.effectiveBalanceIncrementG
  let perIncrement ← getBaseRewardPerIncrement state
  checkedMul increments perIncrement "get_base_reward: increments * get_base_reward_per_increment"

/-- `get_finality_delay`. The pyspec subtracts two `uint64` epochs, so a finalized epoch past
the previous epoch raises `ValueError`. The body subtracts through `checkedSub`
(`.arithmetic`). -/
forkdef getFinalityDelay (state : State) : Except StateTransitionError Epoch :=
  checkedSub (previousEpochOf state) (sszGet state finalizedCheckpoint).epoch
    "get_finality_delay: previous_epoch - finalized_checkpoint.epoch"

/-- `is_in_inactivity_leak`. It fails only where `get_finality_delay` fails. -/
forkdef isInInactivityLeak (state : State) : Except StateTransitionError Bool := do
  pure ((← getFinalityDelay state) > Const.minEpochsToInactivityPenalty)

end

end EthCLSpecs.Fulu
