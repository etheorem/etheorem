import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.SSZListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:234-253`)
modifies two fields sequentially within one state transition. This file characterizes the
whole transition as one value: the run on `pureState preState` returns `pureState` of
`preState` with `builderPendingWithdrawals` and `builderPendingPayments` written, and
nothing else. When
invoked by the epoch substep, it feeds every qualifying previous-epoch payment's
withdrawal, in slot order, through the bounded `SSZList.push`; under an explicit capacity
hypothesis, every qualifying withdrawal is appended. It then shifts the payment window
down by `SLOTS_PER_EPOCH`, padding the vacated half with empties.

The withdrawals side rests on two pieces: a pure fact about `SSZList.push`'s clamp
(iterating it over a list of values ends at the original list plus the clamped prefix that
fits, unconditionally, proved generically in `SizzLean.Proofs.SSZListPush`), and the loop's
own reduction to that list, in iteration order. No capacity-headroom invariant is assumed
or proved here; the "every qualifying withdrawal is appended" statement above is a
corollary of the unconditional clamp fact under an explicit
`preState.builderPendingWithdrawals.val.size + qualifying.length ≤ builderPendingWithdrawalsLimit`
hypothesis, not an unconditional theorem.

The window side is a direct instance of `shiftWindow`'s general behavior:
`expectedPaymentWindow_get_lt` / `expectedPaymentWindow_get_upper` state the two
index-region facts (old upper half moves down; new upper half is empty).
`processBuilderPendingPayments` reads `builderPendingPayments` once, before the
withdrawals loop runs, and the loop never writes that field, so the window
transformation's input is unaffected by whatever the withdrawals loop did.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The contract
`processBuilderPendingPayments_run` states the run at the box, in `.run` form, because
that is the shape the fork-choice bridge consumes; the readings state the `runPure` form,
which `runPure_of_run_ok` derives from the contract.

This file proves only the local before/after behavior of one call, for an arbitrary
input value. It does not prove protocol-wide exactly-once settlement, and says nothing
about how this substep's effect interacts with `settleBuilderPayment` or
`processProposerSlashing`, the other paths that clear a `BuilderPendingPayment` before
this substep ever runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Safety and invariant preservation".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind run_pure
  except_bind_ok except_bind_error)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (Preset Gwei BeaconState)
open EthCLSpecs.Gloas.Const (slotsPerEpoch builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
open SizzLean.Proofs (sszListFoldlPush_val sszListFoldlPush_val_of_fits view_uncachedBox)

/-- `do x` for a lone `for`-loop `x` elaborates as `x >>= fun _ => pure ()`, not as `x`
itself. Peels that wrapper so a fact about the bare loop run connects to a use site that
runs the bare `forIn` before more code: the wrapper succeeds with the same post-state, and
discards the loop's own value. -/
private theorem run_of_run_seq_pure {ε σ β : Type} (x : StateT σ (Except ε) β) (s0 s1 : σ)
    (h : (x >>= fun _ => (pure () : StateT σ (Except ε) Unit)).run s0 = .ok ((), s1)) :
    ∃ a : β, x.run s0 = .ok (a, s1) := by
  rw [run_bind] at h
  cases hx : x.run s0 with
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hx] at h
    rw [except_bind_ok, run_pure] at h
    have h2 : s = s1 := congrArg Prod.snd (Except.ok.inj h)
    subst h2
    exact ⟨a, rfl⟩
  | error e =>
    rw [hx, except_bind_error] at h
    cases h

/-! ## The withdrawals loop

`builderPendingWithdrawalsLoop_run_eq` is the loop's whole-transition equation: the
conditional `appendState` loop always succeeds, and its effect reduces to a pure
`SSZList.push` fold over the qualifying indices (`sszListFoldlPush_val` characterizes the
clamp). `builderPendingPayments` is untouched, which the record-update form states by
leaving it out. `cond` is a `Prop` with a `Decidable` instance, matching the production
`p.weight ≥ quorum` guard. -/

/-- The loop's whole-transition equation over an arbitrary index list. Stated at the box
level, on `pureState preState`, so the composite contract below rewrites with it directly. -/
private theorem builderPendingWithdrawalsList_run_eq [Preset] [HasherTag]
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) (l : List Nat) :
    (do for i in l do
          if cond i then
            appendState builderPendingWithdrawals (val i)
        : GloasRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals :=
            ((l.filter fun i => decide (cond i)).map val).foldl
              (fun l w => l.push w) preState.builderPendingWithdrawals }) := by
  induction l generalizing preState with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : cond i
    · have hstep : (appendState builderPendingWithdrawals (val i) : GloasRun Unit).run
            (pureState preState)
          = .ok ((), pureState { preState with builderPendingWithdrawals :=
            preState.builderPendingWithdrawals.push (val i) }) := rfl
      have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = i :: List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_pos]; simpa using h
      simp only [List.forIn_cons, run_bind, if_pos h, hstep, except_bind_ok, run_pure]
      rw [hfilter, List.map_cons, List.foldl_cons]
      exact ih { preState with builderPendingWithdrawals :=
        preState.builderPendingWithdrawals.push (val i) }
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      simp only [List.forIn_cons, run_bind, if_neg h, run_pure, except_bind_ok]
      rw [hfilter]
      exact ih preState

/-- `processBuilderPendingPayments`'s withdrawals loop over `[0:n]`, the source's own
range: the list equation above at `List.range n`. -/
private theorem builderPendingWithdrawalsLoop_run_eq [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) :
    (do for i in [0:n] do
          if cond i then
            appendState builderPendingWithdrawals (val i)
        : GloasRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals :=
            (((List.range n).filter fun i => decide (cond i)).map val).foldl
              (fun l w => l.push w) preState.builderPendingWithdrawals }) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact builderPendingWithdrawalsList_run_eq cond val preState (List.range n)

/-! ## The named values the transition produces

`builderPaymentQuorum`, `qualifyingBuilderWithdrawals`, `expectedWithdrawals`, and
`expectedPaymentWindow` name the four values in `processBuilderPendingPayments_run`'s
conclusion, over plain `BeaconState` values. A spec accessor that takes the boxed `State`
reads `pureState state`, so the names stay free of any box of their own. -/

/-- `processBuilderPendingPayments`'s quorum threshold, factored out for reuse between
`qualifyingBuilderWithdrawals`, `expectedWithdrawals`, and their theorems. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) : Gwei :=
  (getTotalActiveBalance (pureState state) / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The previous-epoch payments whose weight clears `builderPaymentQuorum`, mapped to
their withdrawals, in slot order, before `SSZList.push`'s capacity clamp. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : BeaconState) :
    List BuilderPendingWithdrawal :=
  let payments := state.builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ builderPaymentQuorum state)).map
    fun i => (vget payments i).withdrawal

/-- The `builderPendingWithdrawals` value `processBuilderPendingPayments` produces:
`qualifyingBuilderWithdrawals`, folded through `SSZList.push` from the field's current
value. `sszListFoldlPush_val` and `sszListFoldlPush_val_of_fits` characterize this
fold's clamping behavior. -/
def expectedWithdrawals [Preset] [HasherTag] (state : BeaconState) :
    SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit :=
  (qualifyingBuilderWithdrawals state).foldl (fun l w => l.push w)
    state.builderPendingWithdrawals

/-- The `builderPendingPayments` value `processBuilderPendingPayments` produces: the
field's current value shifted down by `SLOTS_PER_EPOCH` and padded with empties. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : BeaconState) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow state.builderPendingPayments slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- Lower half of `expectedPaymentWindow`: each index `i < slotsPerEpoch` copies the
old upper half at `i + slotsPerEpoch`. -/
theorem expectedPaymentWindow_get_lt [Preset] [HasherTag] (state : BeaconState)
    (i : Nat) (hi : i < slotsPerEpoch) :
    vget (expectedPaymentWindow state) i =
      vget state.builderPendingPayments (i + slotsPerEpoch) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget state.builderPendingPayments (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, hi]

/-- Upper half of `expectedPaymentWindow`: each index in
`[slotsPerEpoch, 2 * slotsPerEpoch)` is the empty `BuilderPendingPayment`. -/
theorem expectedPaymentWindow_get_upper [Preset] [HasherTag] (state : BeaconState)
    (i : Nat) (hi : slotsPerEpoch ≤ i) (hi' : i < 2 * slotsPerEpoch) :
    vget (expectedPaymentWindow state) i = (default : BuilderPendingPayment) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget state.builderPendingPayments (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, Nat.not_lt.mpr hi]

/-! ## The whole-transition contract

`processBuilderPendingPayments_run` is the contract: the run returns `preState` with only
`builderPendingWithdrawals` and `builderPendingPayments` written, as one value. The
withdrawals half comes from `builderPendingWithdrawalsLoop_run_eq`; the payment-window
half is the final `modifyState`, whose read of the field is unaffected by the loop. -/

/-- Exact whole-transition contract for `processBuilderPendingPayments`, at the box the
pure configuration runs: the step on `pureState preState` returns the uncached box of the original
value with only the two fields written through the source-level writes. Stated at the box
level so the fork-choice bridge consumes it by application; `runPure_of_run_ok` derives
the `runPure` form (`processBuilderPendingPayments_run_of_fits` reads it under an explicit
capacity hypothesis). -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
        = .ok ((), pureState { preState with
            builderPendingWithdrawals := expectedWithdrawals preState,
            builderPendingPayments := expectedPaymentWindow preState }) := by
  intro preState
  have hloop := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
    (fun i => (vget preState.builderPendingPayments i).weight ≥ builderPaymentQuorum preState)
    (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
  -- Re-elaborate the source shape here so the loop term matches `hloop`'s left side and
  -- the final `sszUpdate` reduces against the record-update form on the right.
  show (do
      let quorum := builderPaymentQuorum preState
      let payments := preState.builderPendingPayments
      for i in [0:slotsPerEpoch] do
        if (vget payments i).weight ≥ quorum then
          appendState builderPendingWithdrawals (vget payments i).withdrawal
      modifyState fun state =>
        sszUpdate state with builderPendingPayments :=
          shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))
      : GloasRun Unit).run (pureState preState)
    = .ok ((), pureState { preState with
        builderPendingWithdrawals := expectedWithdrawals preState,
        builderPendingPayments := expectedPaymentWindow preState })
  obtain ⟨a, hbare⟩ := run_of_run_seq_pure _ _ _ hloop
  rw [run_bind, hbare, except_bind_ok]
  unfold expectedWithdrawals qualifyingBuilderWithdrawals builderPaymentQuorum
    expectedPaymentWindow
  rfl

/-- Capacity-guarded value-level reading of `processBuilderPendingPayments_run`: under an
explicit headroom hypothesis, every qualifying withdrawal is appended in slot order, with
no `SSZList.push` clamp. The payment-window half is unchanged from the contract. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (preState : BeaconState)
    (hfits : preState.builderPendingWithdrawals.val.size +
      (qualifyingBuilderWithdrawals preState).length ≤ builderPendingWithdrawalsLimit) :
    runPure (processBuilderPendingPayments (StateTransition := GloasRun)) preState
      = .ok ((), { preState with
          builderPendingWithdrawals :=
            ⟨preState.builderPendingWithdrawals.val ++ (qualifyingBuilderWithdrawals preState).toArray,
              by simp only [Array.size_append, List.size_toArray]; omega⟩,
          builderPendingPayments := expectedPaymentWindow preState }) := by
  rw [runPure_of_run_ok (processBuilderPendingPayments_run preState)]
  congr 1
  rw [show expectedWithdrawals preState
        = ⟨preState.builderPendingWithdrawals.val ++ (qualifyingBuilderWithdrawals preState).toArray,
            by simp only [Array.size_append, List.size_toArray]; omega⟩ from
      Subtype.ext (by
        unfold expectedWithdrawals
        rw [sszListFoldlPush_val_of_fits _ _ hfits])]

end EthCLSpecs.Proofs.Gloas
