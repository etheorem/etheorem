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
`increaseBalance` also adds through the checked `+` on `Gwei` (`SPEC_ARITHMETIC.md` §4.1). It
rejects with the `.arithmetic` fault when the sum leaves the `uint64` range, where the pyspec's
`+=` raises `ValueError`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- Modify balance `i` via the infallible `[i]!` element write (total). `balances`
is a basic-packed `Gwei` field, so the write rebuilds the field's subtree, the same
cost as the old whole-field form. The helper has no pyspec twin: every caller reads
`balances[i]` through the raising `sszGetIdx` first, so the position is in range here. -/
forkdef modBalance (state : State) (i : ValidatorIndex) (f : Gwei → Gwei) : State :=
  -- `toPlainNat`: the caller's raising read already proved `i` in range (see above).
  sszModify state balances[i.toPlainNat]! := f

/-- `increase_balance`. The pyspec's `+=` uses `eth-ssz-specs`' checked `uint64` addition.
The result's bound check raises `SSZValueError`, a `ValueError` subclass. The reference runner lets that
raise escape. The checked `+` on `Gwei` models the addition, and the action rejects with the
`.arithmetic` uncaught fault.

The read goes through `sszGetIdx`. The pyspec indexes a bare list here, and that read raises
`IndexError` past the end. An `[i]!` read answers with the `Gwei` default instead, and the write
past the end is a no-op. A caller holding an out-of-range index would then run clean, where the
pyspec rejects. Two callers can hold one. `pcLoop` passes a `target_index` read from
`pending_consolidations`. Every caller that indexes `balances` by a `validators` index holds one
when the two lengths disagree. -/
forkdef increaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) :
    StateTransition State := do
  let balance ← sszGetIdx (sszGet state balances) i
  let sum ← balance + delta
  return modBalance state i (fun _ => sum)

/-- `decrease_balance` (`phase0/beacon-chain.md:1663-1667`):
`saturating_sub(state.balances[index], delta)`, floored at 0. The floor is the pyspec's own,
so the subtraction raises nothing. The read goes through `sszGetIdx` for the reason
`increaseBalance` gives. The pyspec reads `state.balances[index]` before it writes, and that
read raises `IndexError` past the end. -/
forkdef decreaseBalance (state : State) (i : ValidatorIndex) (delta : Gwei) :
    StateTransition State := do
  let balance ← sszGetIdx (sszGet state balances) i
  return modBalance state i (fun _ => balance.saturatingSub delta)

/-- `get_total_balance` (floored at one increment). The pyspec's `sum` over the
`effective_balance` values is a checked fold (`SPEC_ARITHMETIC.md` §3.2, the
`sum` row), so the result carries the fault; `max` picks an operand and never
raises. The comprehension `[state.validators[index].effective_balance for index in
indices]` (`fulu/minimal.py:1523-1534`) forms the whole list before `sum` runs, so every
read precedes the first add. Each read raises `IndexError` past the end of the registry,
and the body reads through `getAt` in the same order. -/
forkdef getTotalBalance (state : State) (indices : Array ValidatorIndex) :
    Except StateTransitionError Gwei := do
  let validators := sszGet state validators
  let balances ← indices.mapM fun i => do
    let validator ← liftErr (getAt validators i)
    pure validator.effectiveBalance
  let total ← (balances.foldlM (fun acc b => acc + b) (0 : Gwei) : Checked Gwei)
  return max total Const.effectiveBalanceIncrementG

end

end EthCLSpecs.Fulu
