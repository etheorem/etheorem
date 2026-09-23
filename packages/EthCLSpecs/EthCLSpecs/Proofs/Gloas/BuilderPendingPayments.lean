import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import SizzLean.Proofs.SSZListPush

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:236-255`)
changes two fields, one after the other, in one state transition. It appends the
withdrawal of each qualifying payment from the previous epoch to
`builderPendingWithdrawals`, in slot order, through `appendState`. Then it shifts the
payment window down by `SLOTS_PER_EPOCH` and fills the empty half with empty payments.
This file proves each change on its own, then joins them into one theorem about the
function.

`appendState` is the spec's `List.append`: at the list limit it raises `.listFull`, as
remerkleable's append does. So the substep has two outcomes, and
`processBuilderPendingPayments_run` states both. When the qualifying withdrawals fit under
`BUILDER_PENDING_WITHDRAWALS_LIMIT`, the substep succeeds, appends every one of them, and
shifts the window. When they do not fit, the substep raises `.listFull`. pyspec raises at
the same append. That raise is a bare `Exception`, a fault no reference wrapper catches, so
it is not a rejection of an invalid block.

The withdrawals side is the reduction of the loop, by induction over the slot indices.
Each step is one `appendState`, and `appendState_run_of_lt` / `appendState_run_of_le`
state its two outcomes.

The window side applies the general behavior of `shiftWindow`.
`expectedPaymentWindow_get_lt` and `expectedPaymentWindow_get_upper` state the two facts
about index regions: the old upper half moves down, and the new upper half is empty.
`processBuilderPendingPayments` reads `builderPendingPayments` twice: before the
withdrawals loop, and again from the state after the loop, as pyspec does. The loop
does not write that field, so both reads give the same value.

This file proves only the local effect of one call, for any input state. It does not
prove that each payment settles exactly once across the protocol. It does not relate
this substep to `settleBuilderPayment` or `processProposerSlashing`, the other paths that
clear a `BuilderPendingPayment` before this substep runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Safety and invariant preservation".

Every theorem below states its conclusions about the state through `sszGet`, never
through equality of whole `State` values: the cache overlay of `State` records one pending
write per `sszUpdate` call.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (Preset Gwei)
open EthCLSpecs.Gloas.Const (slotsPerEpoch builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
open SizzLean.Proofs (sszListPush_val sszListPush?_of_lt sszListPush?_of_le)

/-- One `appendState` to `builderPendingWithdrawals` with room: the run succeeds and writes
the longer list. -/
private theorem appendState_run_of_lt [Preset] [HasherTag] (state0 : State)
    (w : BuilderPendingWithdrawal)
    (h : (sszGet state0 builderPendingWithdrawals).val.size < builderPendingWithdrawalsLimit) :
    (appendState builderPendingWithdrawals w : GloasRun Unit).run state0 =
      .ok ((), sszUpdate state0 with
        builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push w h) := by
  simp only [run_bind, run_getThe, except_bind_ok, Option.map_some,
    sszListPush?_of_lt (sszGet state0 builderPendingWithdrawals) w h]
  cases state0 <;> rfl

/-- One `appendState` to a full `builderPendingWithdrawals`: the run raises `.listFull`, as
the spec's `List.append` raises. -/
private theorem appendState_run_of_le [Preset] [HasherTag] (state0 : State)
    (w : BuilderPendingWithdrawal)
    (h : builderPendingWithdrawalsLimit ≤ (sszGet state0 builderPendingWithdrawals).val.size) :
    (appendState builderPendingWithdrawals w : GloasRun Unit).run state0 =
      .error (.listFull "builderPendingWithdrawals") := by
  simp only [run_bind, run_getThe, except_bind_ok, Option.map_none,
    sszListPush?_of_le (sszGet state0 builderPendingWithdrawals) w h]
  rfl

/-- The reduction of the withdrawals loop. `cond` is a `Prop` with a `Decidable` instance,
the same as the guard `p.weight ≥ quorum` in the spec body. The loop appends `val i` for
each `i < n` that meets `cond`, in order.

- When those values fit under the list limit, the loop succeeds. The list becomes the old
  list followed by the values, and `builderPendingPayments` does not change.
- When they do not fit, the loop raises `.listFull` at the first append past the limit. -/
private theorem builderPendingWithdrawalsLoop_run [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (state0 : State) :
    ((sszGet state0 builderPendingWithdrawals).val.size +
        ((List.range n).filter fun i => decide (cond i)).length ≤ builderPendingWithdrawalsLimit →
      ∃ resultState : State,
        (do for i in [0:n] do
              if cond i then
                appendState builderPendingWithdrawals (val i)
            : GloasRun Unit).run state0 = .ok ((), resultState) ∧
        (sszGet resultState builderPendingWithdrawals).val =
          (sszGet state0 builderPendingWithdrawals).val ++
            (((List.range n).filter fun i => decide (cond i)).map val).toArray ∧
        sszGet resultState builderPendingPayments = sszGet state0 builderPendingPayments) ∧
    (builderPendingWithdrawalsLimit < (sszGet state0 builderPendingWithdrawals).val.size +
        ((List.range n).filter fun i => decide (cond i)).length →
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : GloasRun Unit).run state0 = .error (.listFull "builderPendingWithdrawals")) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  induction (List.range n) generalizing state0 with
  | nil =>
    have hcap := (sszGet state0 builderPendingWithdrawals).property
    exact ⟨fun _ => ⟨state0, rfl, by simp, rfl⟩, fun hover => by simp at hover; omega⟩
  | cons i rest ih =>
    by_cases h : cond i
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest)) =
          i :: List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_pos]; simpa using h
      rw [hfilter, List.length_cons, List.map_cons]
      by_cases hlt : (sszGet state0 builderPendingWithdrawals).val.size <
          builderPendingWithdrawalsLimit
      · -- The append has room: step to the state with the longer list, then use `ih`.
        have hstep := appendState_run_of_lt state0 (val i) hlt
        have hgetW : sszGet (sszUpdate state0 with builderPendingWithdrawals :=
            (sszGet state0 builderPendingWithdrawals).push (val i) hlt)
            builderPendingWithdrawals = (sszGet state0 builderPendingWithdrawals).push (val i) hlt := by
          cases state0 <;> rfl
        have hgetP : sszGet (sszUpdate state0 with builderPendingWithdrawals :=
            (sszGet state0 builderPendingWithdrawals).push (val i) hlt)
            builderPendingPayments = sszGet state0 builderPendingPayments := by
          cases state0 <;> rfl
        obtain ⟨ihok, iherr⟩ := ih (sszUpdate state0 with builderPendingWithdrawals :=
          (sszGet state0 builderPendingWithdrawals).push (val i) hlt)
        rw [hgetW, sszListPush_val, Array.size_push] at ihok iherr
        refine ⟨fun hfits => ?_, fun hover => ?_⟩
        · obtain ⟨resultState, hrun, hw, hp⟩ := ihok (by omega)
          refine ⟨resultState, ?_, ?_, ?_⟩
          · rw [List.forIn_cons]
            simp only [h, if_pos, run_bind, hstep]
            exact hrun
          · rw [hw]; simp
          · rw [hp, hgetP]
        · rw [List.forIn_cons]
          simp only [h, if_pos, run_bind, hstep]
          exact iherr (by omega)
      · -- The list is full: this append raises, and the rest of the loop never runs.
        have hstep := appendState_run_of_le state0 (val i) (by omega)
        refine ⟨fun hfits => absurd hfits (by omega), fun _ => ?_⟩
        rw [List.forIn_cons]
        simp only [h, if_pos, run_bind, hstep]
        rfl
    · obtain ⟨ihok, iherr⟩ := ih state0
      have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest)) =
          List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      rw [hfilter]
      refine ⟨fun hfits => ?_, fun hover => ?_⟩
      · obtain ⟨resultState, hrun, hw, hp⟩ := ihok hfits
        refine ⟨resultState, ?_, hw, hp⟩
        rw [List.forIn_cons]
        simp only [h, run_bind, run_pure]
        exact hrun
      · rw [List.forIn_cons]
        simp only [h, run_bind, run_pure]
        exact iherr hover

/-- The quorum threshold of `processBuilderPendingPayments`, as a separate definition, so
`qualifyingBuilderWithdrawals` and the theorems below use one copy. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : State) : Gwei :=
  (getTotalActiveBalance state / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The withdrawals of the payments from the previous epoch whose weight reaches
`builderPaymentQuorum`, in slot order. The substep appends these. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : State) :
    List BuilderPendingWithdrawal :=
  let payments := sszGet state builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ builderPaymentQuorum state)).map
    fun i => (vget payments i).withdrawal

/-- The `builderPendingPayments` value `processBuilderPendingPayments` produces: the
field's current value shifted down by `SLOTS_PER_EPOCH` and padded with empties. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : State) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- Lower half of `expectedPaymentWindow`: each index `i < slotsPerEpoch` copies the
old upper half at `i + slotsPerEpoch`. -/
theorem expectedPaymentWindow_get_lt [Preset] [HasherTag] (state : State)
    (i : Nat) (hi : i < slotsPerEpoch) :
    vget (expectedPaymentWindow state) i =
      vget (sszGet state builderPendingPayments) (i + slotsPerEpoch) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget (sszGet state builderPendingPayments) (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, hi]

/-- Upper half of `expectedPaymentWindow`: each index in
`[slotsPerEpoch, 2 * slotsPerEpoch)` is the empty `BuilderPendingPayment`. -/
theorem expectedPaymentWindow_get_upper [Preset] [HasherTag] (state : State)
    (i : Nat) (hi : slotsPerEpoch ≤ i) (hi' : i < 2 * slotsPerEpoch) :
    vget (expectedPaymentWindow state) i = (default : BuilderPendingPayment) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget (sszGet state builderPendingPayments) (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, Nat.not_lt.mpr hi]

/-- The postcondition of a successful `processBuilderPendingPayments` run: `after`'s
withdrawal list is `before`'s followed by `qualifyingBuilderWithdrawals before`, and its
payment window is `expectedPaymentWindow before`. -/
def ProcessBuilderPendingPaymentsPost [Preset] [HasherTag] (before after : State) : Prop :=
  (sszGet after builderPendingWithdrawals).val =
    (sszGet before builderPendingWithdrawals).val ++
      (qualifyingBuilderWithdrawals before).toArray ∧
  sszGet after builderPendingPayments = expectedPaymentWindow before

/-- The two outcomes of `processBuilderPendingPayments`, split on whether the qualifying
withdrawals fit under `BUILDER_PENDING_WITHDRAWALS_LIMIT`.

- They fit: the run succeeds, and the result satisfies `ProcessBuilderPendingPaymentsPost`.
- They do not fit: the run raises `.listFull`. pyspec raises the same uncaught fault at the
  same append.

The proof joins `builderPendingWithdrawalsLoop_run` (the withdrawals loop) with the direct
application of `shiftWindow` (the payment-window shift). -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] (before : State) :
    ((sszGet before builderPendingWithdrawals).val.size +
        (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit →
      ∃ after : State,
        (processBuilderPendingPayments : GloasRun Unit).run before = .ok ((), after) ∧
        ProcessBuilderPendingPaymentsPost before after) ∧
    (builderPendingWithdrawalsLimit < (sszGet before builderPendingWithdrawals).val.size +
        (qualifyingBuilderWithdrawals before).length →
      (processBuilderPendingPayments : GloasRun Unit).run before =
        .error (.listFull "builderPendingWithdrawals")) := by
  obtain ⟨hloopOk, hloopErr⟩ :=
    builderPendingWithdrawalsLoop_run slotsPerEpoch
      (fun i => (vget (sszGet before builderPendingPayments) i).weight ≥
        builderPaymentQuorum before)
      (fun i => (vget (sszGet before builderPendingPayments) i).withdrawal) before
  -- `qualifyingBuilderWithdrawals` is the loop's filtered list mapped to withdrawals, so
  -- its length is the filter's length.
  have hlen : (qualifyingBuilderWithdrawals before).length =
      ((List.range slotsPerEpoch).filter fun i =>
        decide ((vget (sszGet before builderPendingPayments) i).weight ≥
          builderPaymentQuorum before)).length := by
    simp [qualifyingBuilderWithdrawals]
  refine ⟨fun hfits => ?_, fun hover => ?_⟩
  · obtain ⟨resultState, hrun, hw, hp⟩ := hloopOk (by omega)
    have hbare := run_of_run_seq_pure _ _ _ hrun
    simp only [builderPaymentQuorum] at hbare hw
    -- Build the witness in execution order: `resultState` is the withdrawals loop's
    -- output, then the final `sszUpdate` applies the payment-window shift. The `show`
    -- below confirms that this is the state produced by running the full function.
    refine ⟨(sszUpdate resultState with builderPendingPayments :=
        shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
          (fun _ => (default : BuilderPendingPayment))), ?_, ?_, ?_⟩
    · -- Re-elaborate the source shape here so the generated `sszUpdate`
      -- matcher aligns with the matcher used by `hbare`.
      show (do
          let quorum := builderPaymentQuorum before
          let payments := sszGet before builderPendingPayments
          for i in [0:slotsPerEpoch] do
            if (vget payments i).weight ≥ quorum then
              appendState builderPendingWithdrawals (vget payments i).withdrawal
          modifyState fun state =>
            sszUpdate state with builderPendingPayments :=
              shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
                (fun _ => (default : BuilderPendingPayment))
          : GloasRun Unit).run before =
          .ok ((), sszUpdate resultState with builderPendingPayments :=
            shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
              (fun _ => (default : BuilderPendingPayment)))
      simp only [run_bind, builderPaymentQuorum, hbare]
      cases resultState <;> rfl
    · have hgetW : sszGet (sszUpdate resultState with builderPendingPayments :=
          shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))) builderPendingWithdrawals =
          sszGet resultState builderPendingWithdrawals := by
        cases resultState <;> rfl
      rw [hgetW, hw]
      unfold qualifyingBuilderWithdrawals builderPaymentQuorum
      rfl
    · have hgetP : sszGet (sszUpdate resultState with builderPendingPayments :=
          shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))) builderPendingPayments =
          shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment)) := by
        cases resultState <;> rfl
      rw [hgetP, hp]
      unfold expectedPaymentWindow
      rfl
  · have hbare := run_of_run_seq_pure_error _ _ _ (hloopErr (by omega))
    simp only [builderPaymentQuorum] at hbare
    show (do
        let quorum := builderPaymentQuorum before
        let payments := sszGet before builderPendingPayments
        for i in [0:slotsPerEpoch] do
          if (vget payments i).weight ≥ quorum then
            appendState builderPendingWithdrawals (vget payments i).withdrawal
        modifyState fun state =>
          sszUpdate state with builderPendingPayments :=
            shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
              (fun _ => (default : BuilderPendingPayment))
        : GloasRun Unit).run before = .error (.listFull "builderPendingWithdrawals")
    simp only [run_bind, builderPaymentQuorum, hbare]
    rfl

/-- The success half of `processBuilderPendingPayments_run`, spelled out: under the
capacity hypothesis, every qualifying withdrawal is appended in slot order, and the
payment window shifts. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (before : State)
    (hfits : (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit) :
    ∃ after : State,
      (processBuilderPendingPayments : GloasRun Unit).run before = .ok ((), after) ∧
      (sszGet after builderPendingWithdrawals).val =
        (sszGet before builderPendingWithdrawals).val ++
          (qualifyingBuilderWithdrawals before).toArray ∧
      sszGet after builderPendingPayments = expectedPaymentWindow before :=
  let ⟨after, hrun, hw, hp⟩ := (processBuilderPendingPayments_run before).1 hfits
  ⟨after, hrun, hw, hp⟩

/-- The reject half of `processBuilderPendingPayments_run`: when the qualifying
withdrawals overflow the list limit, the substep raises `.listFull`. -/
theorem processBuilderPendingPayments_run_of_overflow [Preset] [HasherTag] (before : State)
    (hover : builderPendingWithdrawalsLimit < (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length) :
    (processBuilderPendingPayments : GloasRun Unit).run before =
      .error (.listFull "builderPendingWithdrawals") :=
  (processBuilderPendingPayments_run before).2 hover

end EthCLSpecs.Proofs.Gloas
