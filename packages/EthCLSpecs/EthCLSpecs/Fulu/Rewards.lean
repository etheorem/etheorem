import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. Reward
arithmetic runs in `Nat` (matching the pyspec's `int`).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`. It fails only where `get_total_active_balance` fails. The
total is at least one increment, so the square root is positive. -/
forkdef getBaseRewardPerIncrement (state : State) : Except StateTransitionError Nat := do
  let total ← getTotalActiveBalance state
  pure (Const.effectiveBalanceIncrement * Const.baseRewardFactor / isqrt total.toNat)

/-- `get_base_reward`. The pyspec reads `validators[i]` first, so an out-of-range `i` raises
`IndexError` before the total. The body reads through `sszGetIdx` (`.outOfBounds`), where
`[i]!` would mask the miss with a default. The product stays below `2 ^ 64`: at most
`2 ^ 64 / 10 ^ 9` increments times at most `64 * 10 ^ 9 / isqrt (10 ^ 9)` per increment. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) : Except StateTransitionError Nat := do
  let v ← sszGetIdx (sszGet state validators) i.toNat
  let perIncrement ← getBaseRewardPerIncrement state
  pure ((v.effectiveBalance.toNat / Const.effectiveBalanceIncrement) * perIncrement)

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
