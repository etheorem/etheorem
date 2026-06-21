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

/-- `get_base_reward_per_increment`. -/
forkdef getBaseRewardPerIncrement (state : State) : Nat :=
  Const.effectiveBalanceIncrement * Const.baseRewardFactor / isqrt (getTotalActiveBalance state).toNat

/-- `get_base_reward`. Reads `validators[i]`, so it returns `Except IndexError`: an
out-of-range `i` rejects (the pyspec's `IndexError`), where `[i]!` would mask it with a
default. A monadic caller binds it through `liftErr`; a same-error caller binds directly. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) : Except IndexError Nat := do
  let v ← sszGetIdx (sszGet state validators) i.toNat
  pure ((v.effectiveBalance.toNat / Const.effectiveBalanceIncrement) * getBaseRewardPerIncrement state)

/-- `get_finality_delay`. -/
forkdef getFinalityDelay (state : State) : Epoch :=
  let prevEpoch := previousEpochOf state
  prevEpoch - (sszGet state finalizedCheckpoint).epoch

/-- `is_in_inactivity_leak`. -/
forkdef isInInactivityLeak (state : State) : Bool :=
  getFinalityDelay state > Const.minEpochsToInactivityPenalty

end

end EthCLSpecs.Fulu
