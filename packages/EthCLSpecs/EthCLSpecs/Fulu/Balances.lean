import EthCLSpecs.Fulu.Randao

/-!
# `EthCLSpecs.Fulu.Balances`: the balance mutators and total (load order row 23)

`increase_balance` / `decrease_balance` (over the primitive `modBalance`) and
`get_total_balance` (`SPECS_ARCHITECTURE.md` §3.1 row 23). These are the low,
read/write primitives on the balances field; `get_total_active_balance`, which
also reads the active set, floats up to `Accessors` (the read/write seam, §3.3).
`modBalance` writes one element through the infallible `[i]!` index, so it is total, like the
old whole-field form but expressed as a single clause. `increaseBalance` and `decreaseBalance`
read through `sszGetIdx` before that write. An out-of-range index therefore rejects with
`.outOfBounds`, where the pyspec's list read raises `IndexError`. The write runs only in range.
`increaseBalance` also adds through `checkedAdd`. It rejects with the `.arithmetic` fault when
the sum leaves the `uint64` range, where the pyspec's `+=` raises `ValueError`.
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

/-- `increase_balance`. The pyspec's `+=` is a bare `uint64` addition, and remerkleable re-runs
the bound check on the result, so an overflow raises `ValueError`. The reference runner lets that
raise escape. `checkedAdd` models the addition, and the action rejects with the `.arithmetic`
uncaught fault.

The read goes through `sszGetIdx`. The pyspec indexes a bare list here, and that read raises
`IndexError` past the end. An `[i]!` read answers with the `Gwei` default instead, and the write
past the end is a no-op. A caller holding an out-of-range index would then run clean, where the
pyspec rejects. Two callers can hold one. `pcLoop` passes a `target_index` read from
`pending_consolidations`. Every caller that indexes `balances` by a `validators` index holds one
when the two lengths disagree. -/
forkdef increaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) :
    StateTransition State := do
  let balance ← sszGetIdx (sszGet state balances) i.toNat
  let sum ← checkedAdd balance delta "increase_balance: balances[index] + delta"
  return modBalance state i (fun _ => sum)

/-- `decrease_balance`, floored at 0. The floor is the pyspec's own clamp, so the subtraction
raises nothing. The read goes through `sszGetIdx` for the reason `increaseBalance` gives. The
pyspec reads `state.balances[index]` before it writes, and that read raises `IndexError` past
the end. -/
forkdef decreaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) :
    StateTransition State := do
  let balance ← sszGetIdx (sszGet state balances) i.toNat
  return modBalance state i (fun _ => if delta > balance then 0 else balance - delta)

/-- `get_total_balance` (floored at one increment). -/
forkdef getTotalBalance (state : State) (indices : Array ValidatorIndex) : Gwei :=
  let validators := sszGet state validators
  let total := indices.foldl (fun acc i => acc + (validators[i.toNat]!).effectiveBalance) 0
  umax total Const.effectiveBalanceIncrementG

end

end EthCLSpecs.Fulu
