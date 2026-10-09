import EthCLSpecs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Run
import EthCLSpecs.Proofs.Run
import SizzLean.Proofs.SSZListSet
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.Balances`: what the balance mutators reject, and what they store

The pyspec's `state.balances[index] += delta` reads a bare list, and remerkleable re-runs its
`uint64` bound check on the result. The read raises `IndexError` past the end. The addition
raises `ValueError` on overflow. `increaseBalance` reads through `sszGetIdx` and adds through
`checkedAdd`, so it rejects on exactly those two conditions. In range and below the bound, the
stored balance is the exact natural-number sum, with no wrap through `2 ^ 64`.

`decrease_balance` clamps at zero, so its subtraction raises nothing. `decreaseBalance`
therefore rejects on the read alone. Its stored balance is the truncating `Nat` difference, so
the `uint64` subtraction never wraps.

These theorems do not bound the total balance, and that bound does not follow from the spec.
`VALIDATOR_REGISTRY_LIMIT` times `MAX_EFFECTIVE_BALANCE_ELECTRA` is about `2 ^ 81`. The real
bound is the ETH supply, which the consensus spec never gives. `processDeposit` carries the
same gap.

`increaseBalance` takes the state it writes as an explicit argument and returns the new one as
its value. It never calls `set`, so a successful run leaves the threaded state untouched; the
whole-state equation states the returned state as a plain value through `pureState`.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The two contracts
state the run at the box, in `.run` form, because that is the shape the fork-choice bridge
consumes; the readings state the `runPure` form, which `runPure_of_run_ok` derives from the
contract. A `runPure` call on `pureState u` and a threaded `pureState v` names the two states
the mutator keeps apart: the one it writes, `u`, and the one it threads, `v`.

Scope is Fulu's two mutators. Gloas and Heze inherit them at their own `State`, as
`increaseBalance` (`Gloas/EpochProcessing.lean:42`) and `increaseBalance`
(`Heze/EpochProcessing.lean:30`), and likewise for `decreaseBalance`. Each is a separate
constant, and these theorems say nothing about those instantiations.

`SizzLean.Proofs.SSZListSet` supplies `sszListSet!_getElem!_self`, which reads back the element
`modBalance` writes.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag StateTransitionError checkedAdd sszGetIdx)
open EthCLSpecs.Fulu (Preset BeaconState State ValidatorIndex Gwei increaseBalance decreaseBalance
  modBalance)
open EthCLSpecs.Proofs (pureState runPure)
open SizzLean.Proofs (sszListSet!_getElem!_self view_uncachedBox)
open SizzLean.Repr
open SizzLean.Cache

/-- The diagnostic descriptor `increaseBalance` hands `checkedAdd`. Named once, so the reject
theorem below can state the exact error term. `abbrev` (reducible), so it unfolds against the
string literal in the elaborated body. -/
abbrev descr : String := "increase_balance: balances[index] + delta"

/-- In range, `sszGetIdx`'s `[i]?` read carries the same element as the total `[i]!` read. The
run equation matches on `[i]?`, and the theorems below state their balances through `[i]!`, so
each in-range theorem rewrites through this once. -/
private theorem sszList_getElem?_eq_getElem! {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (h : i < xs.size) :
    xs.val[i]? = some xs[i]! := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := h)]
  show xs.val[i]? = some (xs.val[i]'h)
  exact Array.getElem?_eq_getElem h

/-- `modBalance`'s whole contract at the pure box: the `sszModify state
balances[i.toNat]! := f` expansion writes `set!` with `f` applied to the old
element, so the writer lands as one plain record update. This is the shape the
two mutator contracts below close into, and the fact a proof that runs a
`State → State` writer on `pureState v` reaches for. -/
@[characterizes EthCLSpecs.Fulu.modBalance]
theorem modBalance_pureState [Preset] [HasherTag] :
    ∀ (v : BeaconState) (i : ValidatorIndex) (f : Gwei → Gwei),
      modBalance (pureState v) i f =
        pureState { v with balances := v.balances.set! i.toNat (f v.balances[i.toNat]!) } :=
  fun _ _ _ => rfl

/-! ## `increaseBalance` -/

/-- **Exact run equation.** The run is `sszGetIdx`'s range check, then `checkedAdd`'s carry
check, and nothing else. Past the end of `balances` it rejects with `.outOfBounds`, the
`IndexError` the pyspec's list read raises. In range it rejects with the `.arithmetic` fault
when the sum wraps below the balance, the unsigned carry test. Otherwise it returns the new
state, `modBalance (pureState u) i …`, the source's own write, and leaves the threaded state
`v` unchanged. Stated at the box level so the fork-choice bridge consumes it by application;
`modBalance_pureState` turns the written state into the plain record update
(`increaseBalance_run_no_wrap`). -/
@[characterizes EthCLSpecs.Fulu.increaseBalance]
theorem increaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (increaseBalance (StateTransition := FuluRun) (pureState u) i delta).run (pureState v)
        = (match u.balances.val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat u.balances.size)
          | some balance =>
            if balance + delta < balance then
              .error (.arithmetic descr)
            else
              .ok (modBalance (pureState u) i (fun _ => balance + delta),
                pureState v)) := by
  intro u v i delta
  unfold increaseBalance sszGetIdx checkedAdd
  -- Reduce the reads on `pureState u` to plain fields, so the read's `[i]?` decides the outer
  -- arm and the carry test the inner one. `cases` then substitutes the read on both sides, and
  -- the branch tactics need only the carry hypothesis.
  simp only [view_uncachedBox]
  cases u.balances.val[i.toNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    -- `liftErr` wraps the successful read, and it has to unfold before the carry test is the
    -- outermost step on this side.
    by_cases h : balance + delta < balance
    · simp [h, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl
    · simp [h, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl

/-- **Out of range.** Past the end of `balances` the run rejects with `.outOfBounds` and
produces no state. The pyspec reads `state.balances[index]` there and raises `IndexError`,
which the reference runner catches. `pcLoop` reaches this with a `target_index` read from
`pending_consolidations`. -/
theorem increaseBalance_run_outOfRange [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toNat < u.balances.size →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState u) i delta) v
        = .error (.outOfBounds i.toNat u.balances.size) := by
  intro u v i delta hidx
  rw [runPure_eq, increaseBalance_run_eq u v i delta]
  have hnone : u.balances.val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]
  rfl

/-- **In range, overflowing.** When the `uint64` sum would wrap, the run rejects with the
`.arithmetic` fault and produces no state. The pyspec raises `ValueError` at the same point. -/
theorem increaseBalance_run_overflow [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < u.balances.size →
      u.balances[i.toNat]!.toNat + delta.toNat ≥ 2 ^ 64 →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState u) i delta) v
        = .error (.arithmetic descr) := by
  intro u v i delta hidx hsum
  have hcarry : u.balances[i.toNat]! + delta < u.balances[i.toNat]! := by
    have hb := UInt64.toNat_lt u.balances[i.toNat]!
    have hd := UInt64.toNat_lt delta
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  rw [runPure_eq, increaseBalance_run_eq u v i delta, sszList_getElem?_eq_getElem! _ _ hidx]
  simp only
  rw [if_pos hcarry]
  rfl

/-- **In range, below the bound.** The run succeeds, and the whole-state equation writes the
sum into that one balance. `UInt64.toNat_add` gives the `% 2 ^ 64` unconditionally, and
`Nat.mod_eq_of_lt` drops it under the hypothesis, so the stored balance's `.toNat` reads back
as the exact natural-number sum: rewrite the equation, then read
`.balances[i.toNat]!.toNat` off the written value. -/
theorem increaseBalance_run_no_wrap [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < u.balances.size →
      u.balances[i.toNat]!.toNat + delta.toNat < 2 ^ 64 →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState u) i delta) v
        = .ok (pureState
            { u with balances := u.balances.set! i.toNat (u.balances[i.toNat]! + delta) },
          v) := by
  intro u v i delta hidx hsum
  have hcarry : ¬ (u.balances[i.toNat]! + delta < u.balances[i.toNat]!) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
    omega
  rw [runPure_eq, increaseBalance_run_eq u v i delta, sszList_getElem?_eq_getElem! _ _ hidx]
  simp only
  rw [if_neg hcarry, modBalance_pureState]
  rfl

/-! ## `decreaseBalance`

`decreaseBalance` reads `balances` through `sszGetIdx`, as `increaseBalance` does, and then
writes a clamped difference. The clamp is the pyspec's own
`0 if delta > balance else balance - delta`. The subtraction therefore raises nothing, and the
index read is the only reject. -/

/-- **Exact run equation.** Past the end of `balances` the run rejects with `.outOfBounds`. In
range it returns the new state, `modBalance (pureState u) i …`, the source's own write with
the clamped difference, and leaves the threaded state `v` unchanged. Stated at the box level
so the fork-choice bridge consumes it by application; `modBalance_pureState` turns the
written state into the plain record update (`decreaseBalance_run_no_underflow`). -/
@[characterizes EthCLSpecs.Fulu.decreaseBalance]
theorem decreaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (decreaseBalance (StateTransition := FuluRun) (pureState u) i delta).run (pureState v)
        = (match u.balances.val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat u.balances.size)
          | some balance =>
            .ok (modBalance (pureState u) i
                (fun _ => if delta > balance then 0 else balance - delta),
              pureState v)) := by
  intro u v i delta
  unfold decreaseBalance sszGetIdx
  simp only [view_uncachedBox]
  cases u.balances.val[i.toNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
    rfl

/-- **Out of range.** The mirror of `increaseBalance_run_outOfRange`. The pyspec reads
`state.balances[index]` before it writes, and that read raises `IndexError`. -/
theorem decreaseBalance_run_outOfRange [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toNat < u.balances.size →
      runPure (decreaseBalance (StateTransition := FuluRun) (pureState u) i delta) v
        = .error (.outOfBounds i.toNat u.balances.size) := by
  intro u v i delta hidx
  rw [runPure_eq, decreaseBalance_run_eq u v i delta]
  have hnone : u.balances.val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]
  rfl

/-- **In range, no underflow.** The whole-state equation writes the clamped difference into
that one balance. `Nat` subtraction truncates at zero, so one equation covers both arms of
the clamp: that truncation and the spec's `0 if delta > balance` agree. The stored balance's
`.toNat` reads back as the truncating `Nat` difference, and a bare `UInt64` subtraction
would wrap to a balance near `2 ^ 64` on the underflowing arm; this equation excludes that. -/
theorem decreaseBalance_run_no_underflow [Preset] [HasherTag] :
    ∀ (u v : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < u.balances.size →
      runPure (decreaseBalance (StateTransition := FuluRun) (pureState u) i delta) v
        = .ok (pureState
            { u with balances :=
                u.balances.set! i.toNat (if delta > u.balances[i.toNat]! then 0 else u.balances[i.toNat]! - delta) },
          v) := by
  intro u v i delta hidx
  rw [runPure_eq, decreaseBalance_run_eq u v i delta, sszList_getElem?_eq_getElem! _ _ hidx]
  simp only
  rw [modBalance_pureState]
  rfl

end EthCLSpecs.Proofs.Fulu
