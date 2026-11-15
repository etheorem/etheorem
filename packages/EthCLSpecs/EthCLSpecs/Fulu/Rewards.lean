import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. The
base-reward pair runs in `Nat` (matching the pyspec's `int`); the finality-delay pair
runs in the checked `Epoch`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`. -/
forkdef getBaseRewardPerIncrement (state : State) : Checked Gwei := do
  let total ← getTotalActiveBalance state
  Const.effectiveBalanceIncrementG * Const.baseRewardFactor / isqrt total.toPlainInt

/-- `get_base_reward`. Reads `validators[i]`, so it rejects with the `IndexError`-shaped
`outOfBounds` (`StateTransitionError`): an out-of-range `i` rejects, where `[i]!` would mask
it with a default. A monadic caller binds it through `liftErr`; a same-error caller binds directly. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) :
    Except StateTransitionError Gwei := do
  let v ← sszGetIdx (sszGet state validators) i
  v.effectiveBalance / Const.effectiveBalanceIncrementG * getBaseRewardPerIncrement state

/-- `get_finality_delay` (`fulu/mainnet.py:1797-1798`): the previous epoch minus the
finalized checkpoint's. The subtract is the checked `uint64` one, so the helper raises where
it raises, a finality delay that would underflow (`finalized epoch` past the previous epoch);
the body is the checked expression itself, no bind. -/
forkdef getFinalityDelay (state : State) : Checked Epoch :=
  previousEpochOf state - (sszGet state finalizedCheckpoint).epoch

/-- `is_in_inactivity_leak` (`fulu/mainnet.py:1801-1802`): the finality delay past
`MIN_EPOCHS_TO_INACTIVITY_PENALTY`. The delay binds above the comparison, so the helper
raises where the subtract raises. -/
forkdef isInInactivityLeak (state : State) : Checked Bool := do
  let finalityDelay ← getFinalityDelay state
  pure (finalityDelay > Const.minEpochsToInactivityPenalty)

end

end EthCLSpecs.Fulu
