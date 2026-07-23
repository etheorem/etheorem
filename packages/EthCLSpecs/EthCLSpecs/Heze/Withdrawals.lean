import EthCLSpecs.Heze.Operations
import EthCLSpecs.Gloas.Withdrawals

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
open EthCLSpecs.Fulu

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
(`context.py:429-433`), so it throws the uncaught `.arithmetic` reject, not a caught `.assert`.
See `Gloas.balanceAfterWithdrawals`. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn := ws.foldl (fun acc w => if w.validatorIndex == vi then acc + w.amount else acc) 0
  let bal ← sszGetIdx (sszGet state balances) vi.toNat
  if withdrawn > bal then
    throw (StateTransitionError.arithmetic "get_balance_after_withdrawals: balances[i] - withdrawn underflow")
  return bal - withdrawn

inherit getBuilderWithdrawals
inherit getPendingPartialWithdrawals
inherit getBuildersSweepWithdrawals
inherit getValidatorsSweepWithdrawals
inherit getExpectedWithdrawals
inherit applyWithdrawals
inherit processWithdrawals

end

end EthCLSpecs.Heze
