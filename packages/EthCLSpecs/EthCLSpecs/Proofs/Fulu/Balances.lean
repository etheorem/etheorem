import EthCLSpecs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Run
import SizzLean.Proofs.SSZListSet

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
its value. It never calls `set`, so a successful run reads `.ok (state', s)` and leaves the
threaded state `s` untouched.

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
open EthCLSpecs.Fulu (Preset State ValidatorIndex Gwei increaseBalance decreaseBalance modBalance)
open SizzLean.Proofs (sszListSet!_getElem!_self)
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

/-- **Exact run equation.** The run is `sszGetIdx`'s range check, then `checkedAdd`'s carry
check, and nothing else. Past the end of `balances` it rejects with `.outOfBounds`, the
`IndexError` the pyspec's list read raises. In range it rejects with the `.arithmetic` fault
when the sum wraps below the balance, the unsigned carry test. Otherwise it returns the state
with that one balance written, and the threaded state `s` unchanged. -/
@[characterizes EthCLSpecs.Fulu.increaseBalance]
theorem increaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      (increaseBalance (StateTransition := FuluRun) state i delta).run s =
        (match (sszGet state balances).val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat (sszGet state balances).size)
          | some balance =>
            if balance + delta < balance then
              .error (.arithmetic descr)
            else
              .ok (modBalance state i (fun _ => balance + delta), s)) := by
  intro state i delta s
  unfold increaseBalance sszGetIdx checkedAdd
  -- The read's `[i]?` decides the outer arm, and the carry test decides the inner one. `cases`
  -- substitutes the read on both sides, so the branch tactics need only the carry hypothesis.
  cases (sszGet state balances).val[i.toNat]? with
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
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      ¬ i.toNat < (sszGet state balances).size →
      (increaseBalance (StateTransition := FuluRun) state i delta).run s
        = .error (.outOfBounds i.toNat (sszGet state balances).size) := by
  intro state i delta s hidx
  have hnone : (sszGet state balances).val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [increaseBalance_run_eq, hnone]

/-- **In range, overflowing.** When the `uint64` sum would wrap, the run rejects with the
`.arithmetic` fault and produces no state. The pyspec raises `ValueError` at the same point. -/
theorem increaseBalance_run_overflow [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      i.toNat < (sszGet state balances).size →
      (sszGet state balances)[i.toNat]!.toNat + delta.toNat ≥ 2 ^ 64 →
      (increaseBalance (StateTransition := FuluRun) state i delta).run s
        = .error (.arithmetic descr) := by
  intro state i delta s hidx hsum
  rw [increaseBalance_run_eq, sszList_getElem?_eq_getElem! _ _ hidx]
  have hcarry : (sszGet state balances)[i.toNat]! + delta < (sszGet state balances)[i.toNat]! := by
    have hb := UInt64.toNat_lt (sszGet state balances)[i.toNat]!
    have hd := UInt64.toNat_lt delta
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  simp [hcarry]

/-- **In range, below the bound.** The run succeeds, and the written balance's `.toNat` is the
exact natural-number sum. `UInt64.toNat_add` gives the `% 2 ^ 64` unconditionally, and
`Nat.mod_eq_of_lt` drops it under the hypothesis. -/
theorem increaseBalance_run_no_wrap [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      i.toNat < (sszGet state balances).size →
      (sszGet state balances)[i.toNat]!.toNat + delta.toNat < 2 ^ 64 →
      ∃ state' : State,
        (increaseBalance (StateTransition := FuluRun) state i delta).run s
            = .ok (state', s)
        ∧ (sszGet state' balances)[i.toNat]!.toNat
            = (sszGet state balances)[i.toNat]!.toNat + delta.toNat := by
  intro state i delta s hidx hsum
  have hcarry : ¬ ((sszGet state balances)[i.toNat]! + delta
      < (sszGet state balances)[i.toNat]!) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
    omega
  refine ⟨modBalance state i (fun _ => (sszGet state balances)[i.toNat]! + delta), ?_, ?_⟩
  · rw [increaseBalance_run_eq, sszList_getElem?_eq_getElem! _ _ hidx]
    simp [hcarry]
  · have hview : sszGet (modBalance state i (fun _ => (sszGet state balances)[i.toNat]! + delta))
        balances
        = (sszGet state balances).set! i.toNat ((sszGet state balances)[i.toNat]! + delta) := by
      rcases state with t | t <;> rfl
    rw [hview, sszListSet!_getElem!_self _ _ _ hidx, UInt64.toNat_add, Nat.mod_eq_of_lt hsum]

/-! ## `decreaseBalance`

`decreaseBalance` reads `balances` through `sszGetIdx`, as `increaseBalance` does, and then
writes a clamped difference. The clamp is the pyspec's own
`0 if delta > balance else balance - delta`. The subtraction therefore raises nothing, and the
index read is the only reject. -/

/-- **Exact run equation.** Past the end of `balances` the run rejects with `.outOfBounds`. In
range it returns the state with the clamped difference written, and the threaded state `s`
unchanged. -/
@[characterizes EthCLSpecs.Fulu.decreaseBalance]
theorem decreaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      (decreaseBalance (StateTransition := FuluRun) state i delta).run s =
        (match (sszGet state balances).val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat (sszGet state balances).size)
          | some balance =>
            .ok (modBalance state i (fun _ => if delta > balance then 0 else balance - delta),
              s)) := by
  intro state i delta s
  unfold decreaseBalance sszGetIdx
  cases (sszGet state balances).val[i.toNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
    rfl

/-- **Out of range.** The mirror of `increaseBalance_run_outOfRange`. The pyspec reads
`state.balances[index]` before it writes, and that read raises `IndexError`. -/
theorem decreaseBalance_run_outOfRange [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      ¬ i.toNat < (sszGet state balances).size →
      (decreaseBalance (StateTransition := FuluRun) state i delta).run s
        = .error (.outOfBounds i.toNat (sszGet state balances).size) := by
  intro state i delta s hidx
  have hnone : (sszGet state balances).val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [decreaseBalance_run_eq, hnone]

/-- **In range, no underflow.** The stored balance's `.toNat` is the `Nat` difference, and `Nat`
subtraction truncates at zero. One equation therefore covers both arms of the clamp, because
that truncation and the spec's `0 if delta > balance` agree. A bare `UInt64` subtraction wraps
to a balance near `2 ^ 64` on the underflowing arm. This theorem excludes that. -/
theorem decreaseBalance_run_no_underflow [Preset] [HasherTag] :
    ∀ (state : State) (i : ValidatorIndex) (delta : Gwei) (s : State),
      i.toNat < (sszGet state balances).size →
      ∃ state' : State,
        (decreaseBalance (StateTransition := FuluRun) state i delta).run s
            = .ok (state', s)
        ∧ (sszGet state' balances)[i.toNat]!.toNat
            = (sszGet state balances)[i.toNat]!.toNat - delta.toNat := by
  intro state i delta s hidx
  refine ⟨modBalance state i (fun _ =>
    if delta > (sszGet state balances)[i.toNat]! then 0
    else (sszGet state balances)[i.toNat]! - delta), ?_, ?_⟩
  · rw [decreaseBalance_run_eq, sszList_getElem?_eq_getElem! _ _ hidx]
  · have hview : sszGet (modBalance state i (fun _ =>
        if delta > (sszGet state balances)[i.toNat]! then 0
        else (sszGet state balances)[i.toNat]! - delta)) balances
        = (sszGet state balances).set! i.toNat
            (if delta > (sszGet state balances)[i.toNat]! then 0
             else (sszGet state balances)[i.toNat]! - delta) := by
      rcases state with t | t <;> rfl
    rw [hview, sszListSet!_getElem!_self _ _ _ hidx]
    -- Each arm of the clamp needs its own step. Above the balance the write is `0`, and
    -- `Nat.sub_eq_zero_of_le` truncates the difference to `0`. Below it,
    -- `UInt64.toNat_sub_of_le` carries the subtraction into `Nat`.
    by_cases h : delta > (sszGet state balances)[i.toNat]!
    · have hlt := UInt64.lt_iff_toNat_lt.mp h
      rw [if_pos h, UInt64.toNat_zero]
      exact (Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)).symm
    · rw [if_neg h, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp h)]

end EthCLSpecs.Proofs.Fulu
