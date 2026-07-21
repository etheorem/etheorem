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

/-- `get_balance_after_withdrawals` over `Heze.State`: the balance net of any
already-queued withdrawals for `vi`. Restated (a plain `def` rather than a `forkdef`). -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) : Gwei :=
  let withdrawn := ws.foldl (fun acc w => if w.validatorIndex == vi then acc + w.amount else acc) 0
  let bal := sszGet state balances[vi.toNat]!
  if withdrawn > bal then 0 else bal - withdrawn

inherit getBuilderWithdrawals
inherit getPendingPartialWithdrawals
inherit getBuildersSweepWithdrawals
inherit getValidatorsSweepWithdrawals
inherit getExpectedWithdrawals
inherit applyWithdrawals
inherit processWithdrawals

end

end EthCLSpecs.Heze
