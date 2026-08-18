import EthCLSpecs.Heze.Operations

/-!
# `EthCLSpecs.Heze.Withdrawals`: the inherited builder-aware withdrawal sweep

EIP-7805 changes no withdrawal logic. Gloas's `process_withdrawals` and its sweep helpers
are `inherit`ed over Heze state. `addressOf` / `balanceAfterWithdrawals` are plain `def`s
in Gloas, which the capture does not cover (only `forkdef` / `forkcontainer` / `forkstruct`
replay, `SPEC_AUTHORING_MODEL.md` §8.5), so they are restated for the Heze validator /
state before the sweep helpers that use them.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

state_section

inherit isFullyWithdrawable
inherit isPartiallyWithdrawable
inherit isEligibleForPartialWithdrawals

/-- `addressOf` over `Heze.Validator`: the 20-byte execution address in the validator's
withdrawal credentials. Restated (a plain `def` rather than an inheritable `forkdef`). -/
def addressOf (v : Validator) : ExecutionAddress :=
  Vector.ofFn (fun i : Fin 20 => vget v.withdrawalCredentials (12 + i.val))

/-- `get_balance_after_withdrawals` over `Heze.State` (`capella/beacon-chain.md:378`): the
balance net of any already-queued withdrawals for `vi`. Restated (a plain `def` rather than a
`forkdef`). Throwing, mirroring the Gloas copy: `state.balances[validator_index]` is a bare list
index (`IndexError` → `sszGetIdx` → `outOfBounds`), and `- withdrawn` is a bare `uint64`
subtraction whose underflow raises `ValueError`, uncaught by the reference runner
(`context.py:424-435`), so it throws the uncaught `.arithmetic` reject, not a caught `.assert`.
See `Gloas.balanceAfterWithdrawals`.

The `withdrawn` accumulator folds through `checkedAdd`, as in Fulu and Gloas; pyspec's
`sum(...)` raises during its own accumulation. See the ancestors' twins of this
function, which the lineage replays unchanged. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then
      checkedAdd acc w.amount "get_balance_after_withdrawals: sum(withdrawal.amount)"
    else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi.toNat
  checkedSub bal withdrawn "get_balance_after_withdrawals: balances[i] - withdrawn"

inherit getBuilderWithdrawals
inherit getPendingPartialWithdrawals
inherit getBuildersSweepWithdrawals
inherit getValidatorsSweepWithdrawals
inherit getExpectedWithdrawals
inherit applyWithdrawals
inherit processWithdrawals

end

end EthCLSpecs.Heze
