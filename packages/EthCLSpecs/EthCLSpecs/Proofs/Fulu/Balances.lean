import EthCLSpecs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Arith
import EthCLLib.Proofs.IndexRead
import SizzLean.Proofs.CollectionModify

/-!
# `EthCLSpecs.Proofs.Fulu.Balances`: what the balance mutators reject, and what they store

The pyspec's `state.balances[index] += delta` reads a bare list, and the `uint64` addition of
`eth-ssz-specs` 0.1.0 checks the bound on the result. The read raises `IndexError` past the end.
The addition raises `SSZValueError`, a `ValueError` subclass, on overflow. `increaseBalance` reads
through `sszGetIdx` and adds through the checked `Gwei` `+` (`CLUint64.add`, `SPEC_ARITHMETIC.md`
§4.2), so it rejects on exactly those two conditions. In range and below the bound, the stored
balance is the exact natural-number sum, with no wrap through `2 ^ 64`. The success and value
readings go through the checked-chain laws (`SPEC_ARITHMETIC.md` §4.9): the range condition is
`add_ok_iff`'s success condition on the plain values, and the stored value is `add_value`'s
read-back.

`decrease_balance` floors at zero, so its subtraction raises nothing. `decreaseBalance`
therefore rejects on the read alone. Its stored balance is the truncating `Nat` difference, so
the `uint64` subtraction never wraps.

These theorems do not bound the total balance, and that bound does not follow from the spec.
`VALIDATOR_REGISTRY_LIMIT` times `MAX_EFFECTIVE_BALANCE_ELECTRA` is about `2 ^ 81`. The real
bound is the ETH supply, which the consensus spec never gives. Every caller of
`increaseBalance`, `applyPendingDeposit` among them, carries the same gap.

`increaseBalance` takes the state it writes as an explicit argument and returns the new one as
its value. It never calls `set`, so a successful run leaves the threaded state untouched.

The Fulu `State` is the plain `BeaconState` record, so every statement binds plain values and
states the run in `.run` form. That form is the value-level statement, and it is also the shape
the fork-choice bridge consumes by application. Each run names the two states the mutator keeps
apart: the one it writes, `state`, and the one it threads, `preState`.

Scope is Fulu's two mutators. Gloas and Heze inherit them at their own `State`, as
`increaseBalance` (`Gloas/EpochProcessing.lean:45`) and `increaseBalance`
(`Heze/EpochProcessing.lean:35`), and likewise for `decreaseBalance`. Each is a separate
constant, and these theorems say nothing about those instantiations.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (StateTransitionError Checked liftErr sszGetIdx IdxRead IndexError)
open EthCLSpecs.Fulu (Preset BeaconState ValidatorIndex Gwei increaseBalance decreaseBalance
  modBalance)
open EthCLLib.Proofs (getAt_sszList_clUint64 add_ok_iff add_value)
open SizzLean.Proofs (sszListModify_eq_set!)

/-- In range, `sszGetIdx`'s `[i]?` read carries the same element as the total `[i]!` read. The
run equation matches on `[i]?`, and the theorems below state their balances through `[i]!`, so
each in-range theorem rewrites through this once. -/
private theorem sszList_getElem?_eq_getElem! {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (h : i < xs.size) :
    xs.val[i]? = some xs[i]! := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := h)]
  show xs.val[i]? = some (xs.val[i]'h)
  exact Array.getElem?_eq_getElem h

/-- `modBalance`'s whole contract: the write stores `set!` with `f` applied to the old
element, so the writer is one plain record update. The body spells `SSZList.modify`
(`Array.modify` moves the element out so `f` updates it in place); the contract keeps the
`set!` reading through `sszListModify_eq_set!`, so it states the same shape as before the
native spelling and the two mutator readings below close into it unchanged. -/
@[characterizes EthCLSpecs.Fulu.modBalance]
theorem modBalance_eq [Preset] :
    ∀ (state : BeaconState) (i : ValidatorIndex) (f : Gwei → Gwei),
      modBalance state i f =
        { state with balances := state.balances.set! i.toPlainNat (f state.balances[i.toPlainNat]!) } := by
  intro state i f
  unfold modBalance
  rw [sszListModify_eq_set!]

/-! ## `increaseBalance` -/

/-- `sszGetIdx`'s in-range read is the identity action, so the body's bind on it substitutes
the element: the monad law `bind (pure v) k = k v` at the runner. `rfl`: every layer is an
instance projection, a definition, or a match on a constructor. This is the step that puts the
read's element and the equation's `some` arm on one variable, so the checked-sum branch
tactics below decide one `if` shared by both sides. -/
private theorem bind_liftErr_ok [Preset] {α β : Type} (v : α) (k : α → FuluRun β) :
    bind (liftErr (Except.ok v : Except IndexError α)) k = k v :=
  rfl

/-- The machine reject an arithmetic fault becomes, at the runner's own channel: `rfl` on
each `Except` arm. -/
private theorem liftChecked {m : Type → Type} {α : Type} [Monad m] [MonadExcept StateTransitionError m]
    (x : Checked α) :
    (liftM x : m α) = MonadExcept.ofExcept (x.mapError StateTransitionError.ofArithFault) := by
  cases x with
  | ok v => rfl
  | error e => rfl

/-- **Exact run equation.** The run is `sszGetIdx`'s range check, then the checked `Gwei`
`+` (`CLUint64.add`'s carry check), and nothing else. Past the end of `balances` it rejects
with `.outOfBounds`, the `IndexError` the pyspec's list read raises. In range it rejects with
the `.arithmetic` fault when the sum wraps below the balance, the unsigned carry test (the
fault shape the reject theorems below spell). Otherwise it returns the new state,
`modBalance state i …`, the source's own write, and leaves the threaded state `preState`
unchanged. `modBalance_eq` turns the written state into the plain record update
(`increaseBalance_run_no_wrap`). -/
@[characterizes EthCLSpecs.Fulu.increaseBalance]
theorem increaseBalance_run_eq [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (increaseBalance (StateTransition := FuluRun) state i delta).run preState
        = (match state.balances.val[i.toPlainNat]? with
          | none => .error (.outOfBounds i.toPlainNat state.balances.size)
          | some balance =>
            match balance + delta with
            | .error f => .error (StateTransitionError.ofArithFault f)
            | .ok sum => .ok (modBalance state i (fun _ => sum), preState)) := by
  intro state preState i delta
  unfold increaseBalance sszGetIdx
  rw [getAt_sszList_clUint64]
  -- The read's `[i]?` decides the outer arm and the checked sum the inner one. `cases` then
  -- substitutes the read on both sides, `bind_liftErr_ok` puts the read's element and the
  -- equation's `some` arm on one variable, and the branch tactics need only the sum's
  -- `Except` shape.
  cases state.balances.val[i.toPlainNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    rw [bind_liftErr_ok]
    have hlift : ∀ x : Checked Gwei, (liftM x : FuluRun Gwei)
        = MonadExcept.ofExcept (x.mapError StateTransitionError.ofArithFault) :=
      fun x => liftChecked x
    simp only [hlift]
    cases h : balance + delta with
    | error f => rw [h] at *; rfl
    | ok sum => rw [h] at *; rfl

/-- **Out of range.** Past the end of `balances` the run rejects with `.outOfBounds` and
produces no state. The pyspec reads `state.balances[index]` there and raises `IndexError`,
which the reference runner catches. `pcLoop` reaches this with a `target_index` read from
`pending_consolidations`. -/
theorem increaseBalance_run_outOfRange [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toPlainNat < state.balances.size →
      (increaseBalance (StateTransition := FuluRun) state i delta).run preState
        = .error (.outOfBounds i.toPlainNat state.balances.size) := by
  intro state preState i delta hidx
  rw [increaseBalance_run_eq state preState i delta]
  have hnone : state.balances.val[i.toPlainNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]

/-- **In range, overflowing.** When the `uint64` sum would wrap, the run rejects with the
`.arithmetic` fault and produces no state. The pyspec raises `ValueError` at the same point.
The fault payload is the add's own `ArithFault.range` `"+"`, diagnostic only. The hypothesis
is the real arithmetic obligation, the negation of `add_ok_iff`'s success condition on the
plain values. The proof stays a hand proof: the law set reaches the add's success and value,
but not the fault payload's identity, which the conclusion spells. -/
theorem increaseBalance_run_overflow [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toPlainNat < state.balances.size →
      state.balances[i.toPlainNat]!.toPlainNat + delta.toPlainNat ≥ 2 ^ 64 →
      (increaseBalance (StateTransition := FuluRun) state i delta).run preState
        = .error (.arithmetic "+") := by
  intro state preState i delta hidx hsum
  have hcarry : state.balances[i.toPlainNat]!.val + delta.val < state.balances[i.toPlainNat]!.val := by
    have hb := UInt64.toNat_lt state.balances[i.toPlainNat]!.val
    have hd := UInt64.toNat_lt delta.val
    -- `toPlainNat` is the word's `toNat`; restate the bound on the words, leaving the
    -- index `i.toPlainNat` folded so the element terms match.
    have hsum' : state.balances[i.toPlainNat]!.val.toNat + delta.val.toNat ≥ 2 ^ 64 := hsum
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  rw [increaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  have hinst : ∀ a b : Gwei, (a + b) = EthCLLib.Spec.CLUint64.add a b := fun _ _ => rfl
  simp only [hinst, EthCLLib.Spec.CLUint64.add]
  rw [ite_eq_left hcarry]
  rfl

/-- **In range, below the bound.** The run succeeds, and the whole-state equation writes the
addition's result into that one balance. The hypothesis is the real range condition,
`add_ok_iff`'s success condition on the plain values, so it names the arithmetic obligation
the run has to check and no intermediate `Except` value. The conclusion names the written
value and reads it back through `add_value`: the stored balance is the exact natural-number
sum of the old balance and `delta`, with no wrap through `2 ^ 64`. Laws: `add_ok_iff`,
`add_value` (both over the fused `add_eq_ok`). -/
theorem increaseBalance_run_no_wrap [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toPlainNat < state.balances.size →
      state.balances[i.toPlainNat]!.toPlainNat + delta.toPlainNat < 2 ^ 64 →
      ∃ sum : Gwei,
        EthCLLib.Spec.CLUint64.add state.balances[i.toPlainNat]! delta = .ok sum ∧
        sum.toPlainNat = state.balances[i.toPlainNat]!.toPlainNat + delta.toPlainNat ∧
        (increaseBalance (StateTransition := FuluRun) state i delta).run preState
          = .ok ({ state with balances := state.balances.set! i.toPlainNat sum }, preState) := by
  intro state preState i delta hidx hrange
  -- The range condition names a real sum: `add_ok_iff` produces it, and `add_value` reads
  -- its value back, so the whole-state equation writes a value the two laws pin.
  obtain ⟨sum, hadd⟩ := add_ok_iff _ _ |>.mpr hrange
  refine ⟨sum, hadd, add_value _ _ _ hadd, ?_⟩
  rw [increaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  have hinst : ∀ a b : Gwei, (a + b) = EthCLLib.Spec.CLUint64.add a b := fun _ _ => rfl
  simp only [hinst, hadd]
  rfl

/-! ## `decreaseBalance`

`decreaseBalance` reads `balances` through `sszGetIdx`, as `increaseBalance` does, and then
writes the floored difference. The floor is the pyspec's own `saturating_sub(balance, delta)`
(`fulu/minimal.py:1603`). The subtraction therefore raises nothing, and the index read is the
only reject. -/

/-- **Exact run equation.** Past the end of `balances` the run rejects with `.outOfBounds`. In
range it returns the new state, `modBalance state i …`, the source's own write with the floored
difference, and leaves the threaded state `preState` unchanged. `modBalance_eq` turns the written
state into the plain record update (`decreaseBalance_run_no_underflow`). -/
@[characterizes EthCLSpecs.Fulu.decreaseBalance]
theorem decreaseBalance_run_eq [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (decreaseBalance (StateTransition := FuluRun) state i delta).run preState
        = (match state.balances.val[i.toPlainNat]? with
          | none => .error (.outOfBounds i.toPlainNat state.balances.size)
          | some balance =>
            .ok (modBalance state i (fun _ => balance.saturatingSub delta), preState)) := by
  intro state preState i delta
  unfold decreaseBalance sszGetIdx
  rw [getAt_sszList_clUint64]
  cases state.balances.val[i.toPlainNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
    rfl

/-- **Out of range.** The mirror of `increaseBalance_run_outOfRange`. The pyspec reads
`state.balances[index]` before it writes, and that read raises `IndexError`. -/
theorem decreaseBalance_run_outOfRange [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toPlainNat < state.balances.size →
      (decreaseBalance (StateTransition := FuluRun) state i delta).run preState
        = .error (.outOfBounds i.toPlainNat state.balances.size) := by
  intro state preState i delta hidx
  rw [decreaseBalance_run_eq state preState i delta]
  have hnone : state.balances.val[i.toPlainNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]

/-- **In range, no underflow.** The whole-state equation writes the floored difference
`saturatingSub balance delta` into that one balance. `decreaseBalance_written_toNat` reads the
stored balance back as the truncating `Nat` difference, so a bare `UInt64` subtraction, which
would wrap to a balance near `2 ^ 64` on the underflowing arm, is excluded. -/
theorem decreaseBalance_run_no_underflow [Preset] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toPlainNat < state.balances.size →
      (decreaseBalance (StateTransition := FuluRun) state i delta).run preState
        = .ok ({ state with
                balances := state.balances.set! i.toPlainNat
                  (state.balances[i.toPlainNat]!.saturatingSub delta) },
          preState) := by
  intro state preState i delta hidx
  rw [decreaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  simp only
  rw [modBalance_eq]

/-- **The stored balance as a number.** The value `decreaseBalance_run_no_underflow` writes
reads back as the truncating `Nat` difference `balance - delta`: zero when `delta` exceeds the
balance, the exact difference otherwise. -/
theorem decreaseBalance_written_toNat (balance delta : Gwei) :
    (balance.saturatingSub delta).toPlainNat = balance.toPlainNat - delta.toPlainNat :=
  EthCLLib.Spec.CLUint64.saturatingSub_toPlainNat balance delta

end EthCLSpecs.Proofs.Fulu
