import EthCLSpecs.Fulu.Randao

/-!
# `EthCLSpecs.Fulu.Balances`: the balance mutators and total (load order row 23)

`increase_balance` / `decrease_balance` (over the primitive `modBalance`) and
`get_total_balance` (`SPECS_ARCHITECTURE.md` §3.1 row 23). These are the low,
read/write primitives on the balances field; `get_total_active_balance`, which
also reads the active set, floats up to `Accessors` (the read/write seam, §3.3).
Per-element writes use the infallible `[i]!` element index, total like the old
whole-field form but expressed as a single clause.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- Modify balance `i` via the infallible `[i]!` element write (total). `balances`
is a basic-packed `Gwei` field, so the write rebuilds the field's subtree, the same
cost as the old whole-field form. -/
forkdef modBalance (state : State) (i : ValidatorIndex) (f : Gwei → Gwei) : State :=
  sszModify state balances[i.toNat]! := f

/-- `increase_balance`. -/
forkdef increaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) : State :=
  modBalance state i (· + delta)

/-- `decrease_balance` (floored at 0). -/
forkdef decreaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) : State :=
  modBalance state i (fun balance => if delta > balance then 0 else balance - delta)

/-- `get_total_balance` (floored at one increment). -/
forkdef getTotalBalance (state : State) (indices : Array ValidatorIndex) : Gwei :=
  let validators := sszGet state validators
  let total := indices.foldl (fun acc i => acc + (validators[i.toNat]!).effectiveBalance) 0
  umax total Const.effectiveBalanceIncrementG

end

end EthCLSpecs.Fulu
