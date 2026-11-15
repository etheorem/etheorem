import EthCLSpecs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.CLUint
import SizzLean.Proofs.SSZListSet
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.Balances`: what the balance mutators reject, and what they store

The pyspec's `state.balances[index] += delta` reads a bare list, and remerkleable re-runs its
`uint64` bound check on the result. The read raises `IndexError` past the end. The addition
raises `ValueError` on overflow. `increaseBalance` reads through `sszGetIdx` and adds through
the checked `+` on `Gwei` (`CLUint64`), so it rejects on exactly those two conditions, and the
checked sum's own `ArithFault.range` is the payload of the `.arithmetic` fault the monad lift
throws. In range and below the bound, the stored balance is the checked sum's witness, and its
`.toPlainInt` reads back as the exact natural-number sum, with no wrap through `2 ^ 64`.

`decrease_balance` clamps at zero, so its subtraction raises nothing. `decreaseBalance`
therefore rejects on the read alone. Its stored balance is the truncating `Nat` difference,
so the floored subtraction never goes below zero.

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
contract. A `runPure` call on `pureState state` and a threaded `pureState preState` names the
two states the mutator keeps apart: the one it writes, `state`, and the one it threads,
`preState`.

Scope is Fulu's two mutators. Gloas and Heze inherit them at their own `State`, as
`increaseBalance` (`Gloas/EpochProcessing.lean:45`) and `increaseBalance`
(`Heze/EpochProcessing.lean:35`), and likewise for `decreaseBalance`. Each is a separate
constant, and these theorems say nothing about those instantiations.

`SizzLean.Proofs.UncachedBox` supplies `view_uncachedBox`, which reduces the reads on the pure
box to plain fields. `EthCLLib.Proofs.CLUint` supplies `add_eq_ok`, the success-and-value fact
for the checked `+` (`SPEC_ARITHMETIC.md` §4.5, §5.1, and open work item 2), which names the
witness `increaseBalance_run_no_wrap` stores.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag StateTransitionError Checked IndexError liftErr sszGetIdx IdxRead)
open EthCLSpecs.Fulu (Preset BeaconState State ValidatorIndex Gwei increaseBalance decreaseBalance
  modBalance)
open EthCLLib.Proofs (pureState runPure runPure_eq runPure_of_run_ok add_eq_ok)
open SizzLean.Proofs (view_uncachedBox)
open SizzLean.Repr
open SizzLean.Cache

/-- The `.arithmetic` payload the checked `+` raises when `balance + delta` overflows: the repr
of the `ArithFault.range` fault the monad lift receives from the `Except` layer. Named once, so
the two reject theorems below state the exact error term. -/
abbrev increaseFault (balance delta : Gwei) : String :=
  reprStr (EthCLLib.Spec.ArithFault.range "+" balance.toPlainInt delta.toPlainInt)

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
`State → State` writer on `pureState state` reaches for. -/
@[characterizes EthCLSpecs.Fulu.modBalance]
theorem modBalance_pureState [Preset] [HasherTag] :
    ∀ (state : BeaconState) (i : ValidatorIndex) (f : Gwei → Gwei),
      modBalance (pureState state) i f =
        pureState
          { state with balances := state.balances.set! i.toNat (f state.balances[i.toNat]!) } :=
  fun _ _ _ => rfl

/-! ## `increaseBalance` -/

/-- `sszGetIdx`'s in-range read is the identity action, so the body's bind on it substitutes
the element: the monad law `bind (pure v) k = k v` at the runner. `rfl`: every layer is an
instance projection, a definition, or a match on a constructor. This is the step that puts the
read's element and the equation's `some` arm on one variable, so the checked-sum branch
tactics below decide one `if` shared by both sides. -/
private theorem bind_liftErr_ok [Preset] [HasherTag] {α β : Type} (v : α) (k : α → FuluRun β) :
    bind (liftErr (Except.ok v : Except IndexError α)) k = k v :=
  rfl

/-- The checked sum of the two balances, exactly as the body computes it: `rfl` against
`CLUint64.add`, so the error arm is that operator's own `ArithFault.range`. The theorems below
state their hypotheses over `.toPlainInt`, and `add_eq_ok` carries the fit hypothesis to the
`Checked` value's witness arm. -/
private theorem increaseBalance_checkedSum (balance delta : Gwei) :
    (balance + delta : Checked Gwei) =
      if balance.val + delta.val < balance.val
      then .error (EthCLLib.Spec.ArithFault.range "+" balance.toPlainInt delta.toPlainInt)
      else .ok (EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + delta.val)) := by
  show (if balance.val + delta.val < balance.val then _ else _) = _
  split
  · rfl
  · rfl

/-- The witness arm of `increaseBalance_checkedSum`: under the fit hypothesis the checked sum
returns the wrapped native sum, and `add_eq_ok` names it. -/
private theorem increaseBalance_checkedSum_ok (balance delta : Gwei)
    (hsum : balance.toPlainInt + delta.toPlainInt < 2 ^ 64) :
    (balance + delta : Checked Gwei) =
      .ok (EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + delta.val)) := by
  have hsum' : balance.val.toNat + delta.val.toNat < 2 ^ 64 := hsum
  have hval : (EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + delta.val)).toPlainInt
      = balance.toPlainInt + delta.toPlainInt := by
    show (balance.val + delta.val).toNat = balance.val.toNat + delta.val.toNat
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum']
  exact (add_eq_ok balance delta _).mpr ⟨hsum, hval⟩

/-- **Exact run equation.** The run is `sszGetIdx`'s range check, then the checked `+`'s carry
check, and nothing else. Past the end of `balances` it rejects with `.outOfBounds`, the
`IndexError` the pyspec's list read raises. In range it rejects with the `.arithmetic` fault
carrying the checked sum's exact `ArithFault.range` payload when the sum wraps, the unsigned
carry test. Otherwise it returns the new state, `modBalance (pureState state) i …`, the
source's own write, and leaves the threaded state `preState` unchanged. Stated at the box level
so the fork-choice bridge consumes it by application; `modBalance_pureState` turns the written
state into the plain record update (`increaseBalance_run_no_wrap`). -/
@[characterizes EthCLSpecs.Fulu.increaseBalance]
theorem increaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (increaseBalance (StateTransition := FuluRun) (pureState state) i delta).run
          (pureState preState)
        = (match state.balances.val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat state.balances.size)
          | some balance =>
            match (balance + delta : Checked Gwei) with
            | .error _ => .error (.arithmetic (increaseFault balance delta))
            | .ok sum => .ok (modBalance (pureState state) i (fun _ => sum),
              pureState preState)) := by
  intro state preState i delta
  unfold increaseBalance sszGetIdx IdxRead.get? IdxRead.size
  -- Reduce the reads on `pureState state` to plain fields, so the read's `[i]?` decides the outer
  -- arm and the checked sum the inner one. `cases` then substitutes the read on both sides, and
  -- the branch tactics need only the sum's `Except` shape.
  simp only [view_uncachedBox]
  cases state.balances.val[i.toNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    rw [bind_liftErr_ok]
    simp only []
    simp only [increaseBalance_checkedSum]
    by_cases hcarry : balance.val + delta.val < balance.val
    · simp only [ite_eq_left hcarry]
      rfl
    · simp only [ite_eq_right hcarry]
      rfl

/-- **Out of range.** Past the end of `balances` the run rejects with `.outOfBounds` and
produces no state. The pyspec reads `state.balances[index]` there and raises `IndexError`,
which the reference runner catches. `pcLoop` reaches this with a `target_index` read from
`pending_consolidations`. -/
theorem increaseBalance_run_outOfRange [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toNat < state.balances.size →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState state) i delta) preState
        = .error (.outOfBounds i.toNat state.balances.size) := by
  intro state preState i delta hidx
  rw [runPure_eq, increaseBalance_run_eq state preState i delta]
  have hnone : state.balances.val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]
  rfl

/-- **In range, overflowing.** When the checked sum's plain-`int` value reaches `2 ^ 64`, the
carry test fires and the run rejects with the `.arithmetic` fault carrying the exact
`ArithFault.range` payload. The pyspec raises `ValueError` at the same point. -/
theorem increaseBalance_run_overflow [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < state.balances.size →
      state.balances[i.toNat]!.toPlainInt + delta.toPlainInt ≥ 2 ^ 64 →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState state) i delta) preState
        = .error (.arithmetic (increaseFault state.balances[i.toNat]! delta)) := by
  intro state preState i delta hidx hsum
  have hcarry : state.balances[i.toNat]!.val + delta.val < state.balances[i.toNat]!.val := by
    have hb : state.balances[i.toNat]!.val.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have hd : delta.val.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have hsum' : state.balances[i.toNat]!.val.toNat + delta.val.toNat ≥ 2 ^ 64 := hsum
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  rw [runPure_eq, increaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  simp only [increaseBalance_checkedSum, ite_eq_left hcarry]
  rfl

/-- **In range, below the bound.** The run succeeds, and the whole-state equation writes the
checked sum's witness into that one balance. `ite_eq_right` with the no-carry fact, derived
from the fit hypothesis by `omega` over the native widths, picks the witness arm, so the stored
balance's `.toPlainInt` reads back as the exact natural-number sum: rewrite the equation, then
read `.balances[i.toNat]!.toPlainInt` off the written value. -/
theorem increaseBalance_run_no_wrap [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < state.balances.size →
      state.balances[i.toNat]!.toPlainInt + delta.toPlainInt < 2 ^ 64 →
      runPure (increaseBalance (StateTransition := FuluRun) (pureState state) i delta) preState
        = .ok (pureState
            { state with
                balances := state.balances.set! i.toNat
                  (EthCLLib.Spec.CLUint64.trustedOfUInt64
                    (state.balances[i.toNat]!.val + delta.val)) },
          preState) := by
  intro state preState i delta hidx hsum
  have hnocarry : ¬ (state.balances[i.toNat]!.val + delta.val
      < state.balances[i.toNat]!.val) := by
    have hb : state.balances[i.toNat]!.val.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have hd : delta.val.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have hsum' : state.balances[i.toNat]!.val.toNat + delta.val.toNat < 2 ^ 64 := hsum
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  rw [runPure_eq, increaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  simp only [increaseBalance_checkedSum, ite_eq_right hnocarry]
  rw [modBalance_pureState]
  rfl

/-- The sum `increaseBalance_run_no_wrap` writes reads back as the exact natural-number sum.
This is `add_eq_ok`'s value equation at the written witness, the readback companion the
total-balance proofs need. -/
theorem increaseBalance_written_toPlainInt (balance delta : Gwei)
    (hsum : balance.toPlainInt + delta.toPlainInt < 2 ^ 64) :
    (EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + delta.val)).toPlainInt
      = balance.toPlainInt + delta.toPlainInt :=
  (add_eq_ok balance delta _).mp
    (increaseBalance_checkedSum_ok balance delta hsum) |>.2

/-! ## `decreaseBalance`

`decreaseBalance` reads `balances` through `sszGetIdx`, as `increaseBalance` does, and then
writes the floored difference. The floor is the pyspec's own `saturating_sub(balance, delta)`
(v1.7.0-beta.4; earlier pins spelled it `0 if delta > balance else balance - delta`). The
subtraction therefore raises nothing, and the index read is the only reject. -/

/-- **Exact run equation.** Past the end of `balances` the run rejects with `.outOfBounds`. In
range it returns the new state, `modBalance (pureState state) i …`, the source's own write with
the floored difference, and leaves the threaded state `preState` unchanged. Stated at the box level
so the fork-choice bridge consumes it by application; `modBalance_pureState` turns the
written state into the plain record update (`decreaseBalance_run_no_underflow`). -/
@[characterizes EthCLSpecs.Fulu.decreaseBalance]
theorem decreaseBalance_run_eq [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      (decreaseBalance (StateTransition := FuluRun) (pureState state) i delta).run
          (pureState preState)
        = (match state.balances.val[i.toNat]? with
          | none => .error (.outOfBounds i.toNat state.balances.size)
          | some balance =>
            .ok (modBalance (pureState state) i (fun _ => balance.saturatingSub delta),
              pureState preState)) := by
  intro state preState i delta
  unfold decreaseBalance sszGetIdx IdxRead.get? IdxRead.size
  simp only [view_uncachedBox]
  cases state.balances.val[i.toNat]? with
  | none =>
    simp
    rfl
  | some balance =>
    rw [bind_liftErr_ok]
    simp only []
    rfl

/-- **Out of range.** The mirror of `increaseBalance_run_outOfRange`. The pyspec reads
`state.balances[index]` before it writes, and that read raises `IndexError`. -/
theorem decreaseBalance_run_outOfRange [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      ¬ i.toNat < state.balances.size →
      runPure (decreaseBalance (StateTransition := FuluRun) (pureState state) i delta) preState
        = .error (.outOfBounds i.toNat state.balances.size) := by
  intro state preState i delta hidx
  rw [runPure_eq, decreaseBalance_run_eq state preState i delta]
  have hnone : state.balances.val[i.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]
  rfl

/-- **In range, no underflow.** The whole-state equation writes the floored difference
`balance.saturatingSub delta` into that one balance. `decreaseBalance_written_toPlainInt` reads
the stored balance back as the truncating `Nat` difference, so the write is exactly the
pyspec's `saturating_sub`: the floor, and nothing else. -/
theorem decreaseBalance_run_no_underflow [Preset] [HasherTag] :
    ∀ (state preState : BeaconState) (i : ValidatorIndex) (delta : Gwei),
      i.toNat < state.balances.size →
      runPure (decreaseBalance (StateTransition := FuluRun) (pureState state) i delta) preState
        = .ok (pureState
            { state with
                balances := state.balances.set! i.toNat
                  (state.balances[i.toNat]!.saturatingSub delta) },
          preState) := by
  intro state preState i delta hidx
  rw [runPure_eq, decreaseBalance_run_eq state preState i delta,
    sszList_getElem?_eq_getElem! _ _ hidx]
  simp only
  rw [modBalance_pureState]
  rfl

/-- **The stored balance as a number.** The value `decreaseBalance_run_no_underflow` writes
reads back as the truncating `Nat` difference `balance - delta`: zero when `delta` exceeds the
balance, the exact difference otherwise. -/
theorem decreaseBalance_written_toPlainInt (balance delta : Gwei) :
    (balance.saturatingSub delta).toPlainInt = balance.toPlainInt - delta.toPlainInt := by
  simp only [EthCLLib.Spec.CLUint64.toPlainInt]
  unfold EthCLLib.Spec.CLUint64.saturatingSub
  split
  · rename_i h
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
  · rename_i h
    have hle : balance.val.toNat ≤ delta.val.toNat := by
      have h' : ¬ (delta.val < balance.val) := by
        intro hlt
        apply h
        show delta.val < balance.val
        exact hlt
      rw [UInt64.lt_iff_toNat_lt] at h'
      omega
    rw [Nat.sub_eq_zero_of_le hle]
    rfl

end EthCLSpecs.Proofs.Fulu
