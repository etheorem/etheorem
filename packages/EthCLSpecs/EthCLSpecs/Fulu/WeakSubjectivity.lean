import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.WeakSubjectivity`: the validator-guide concern

`compute_weak_subjectivity_period` (`fulu/mainnet.py:4281`), the validator-guide
helper the fork bodies did not model yet (`phase0/validator.md`, "Weak
subjectivity"). `SPECS_ARCHITECTURE.md` §3.2 rules out a catch-all file, so this
is its own concern file: the weak-subjectivity computation is the concern, and a
second validator-guide helper (`is_within_weak_subjectivity_period`, the `Store`-level
gate) would land here if the fork-choice side ever takes it. It reads the churn
helpers of `RegistryUpdates`, so it sits directly above that file in load order.

The arithmetic is all checked, so the whole body raises exactly where the pyspec
raises: the churn-limit reads, the `SAFETY_DECAY * t` product, the floor division,
and the closing delay sum each test their own result.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `compute_weak_subjectivity_period`: the weak-subjectivity period of the
current state, `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` plus the epochs of
validator-set churn the safety-decay budget (`SAFETY_DECAY`, 10%) buys at the
balance churn limit.

`fulu/mainnet.py:4291` writes `Epoch(SAFETY_DECAY * t // (2 * delta * 100))`; the
`Epoch(...)` narrowing tests a `uint64` against its own range, so it cannot fault
and the checked quotient is the `Epoch` directly. The floor division takes the
checked route (a computed divisor, not a preset constant), so its zero-divisor
raise stays reachable in form, as the pyspec's is. -/
forkdef computeWeakSubjectivityPeriod (state : State) : Checked Epoch := do
  let t ← getTotalActiveBalance state
  let delta ← getBalanceChurnLimit state
  let epochsForValidatorSetChurn : Epoch ← Const.safetyDecay * t / (2 * delta * 100)
  return (← epochsForValidatorSetChurn + Const.minValidatorWithdrawabilityDelay)

end

end EthCLSpecs.Fulu
