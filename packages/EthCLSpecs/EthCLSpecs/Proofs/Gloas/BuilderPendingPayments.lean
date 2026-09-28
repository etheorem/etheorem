import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.SSZListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:234-253`)
changes two fields, one after the other, in one state transition. It appends the
withdrawal of each qualifying payment from the previous epoch to
`builderPendingWithdrawals`, in slot order, through `appendState`. Then it shifts the
payment window down by `SLOTS_PER_EPOCH` and fills the empty half with empty payments.

`appendState` is the spec's `List.append`: at the list limit it raises `.listFull`, as
remerkleable's append does. So the substep has two outcomes, and
`processBuilderPendingPayments_run` states both. When the qualifying withdrawals fit under
`BUILDER_PENDING_WITHDRAWALS_LIMIT`, the run returns `pureState` of `preState` with only
the two fields written. When they do not fit, the run raises `.listFull`. pyspec raises at
the same append. That raise is a bare `Exception`. No reference wrapper catches it, so the
runner classifies it as an uncaught fault.

The withdrawals side is the reduction of the loop, by induction over the slot indices.
Each step is one `appendState`, and `appendState_run_of_lt` / `appendState_run_of_le`
state its two outcomes on the uncached box.

The window side applies the general behavior of `shiftWindow`.
`expectedPaymentWindow_get_lt` and `expectedPaymentWindow_get_upper` state the two facts
about index regions: the old upper half moves down, and the new upper half is empty.
`processBuilderPendingPayments` reads `builderPendingPayments` once, before the loop, and
the loop never writes that field.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The contract
`processBuilderPendingPayments_run` states the run at the box, in `.run` form, because
that is the shape the fork-choice bridge consumes. The readings state the `runPure` form.

This file proves only the local effect of one call, for any input value. It does not
prove that each payment settles exactly once across the protocol. It does not relate
this substep to `settleBuilderPayment` or `processProposerSlashing`, the other paths that
clear a `BuilderPendingPayment` before this substep runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Safety and invariant preservation".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_eq runPure_of_run_ok run_bind run_pure
  run_getThe except_bind_ok except_bind_error)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (Preset Gwei BeaconState)
open EthCLSpecs.Gloas.Const (slotsPerEpoch builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
open SizzLean.Proofs (sszListPush_val sszListPush?_of_lt sszListPush?_of_le)

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

/-- The reject half of `run_of_run_seq_pure`. The `pure ()` wrapper never raises. So when
`x >>= fun _ => pure ()` rejects, `x` rejects with the same error. -/
private theorem run_of_run_seq_pure_error {ε σ β : Type} (x : StateT σ (Except ε) β)
    (s0 : σ) (e : ε)
    (h : (x >>= fun _ => (pure () : StateT σ (Except ε) Unit)).run s0 = .error e) :
    x.run s0 = .error e := by
  rw [run_bind] at h
  cases hx : x.run s0 with
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hx] at h
    rw [except_bind_ok, run_pure] at h
    cases h
  | error e' =>
    rw [hx, except_bind_error] at h
    injection h with h'
    rw [h']

/-! ## The withdrawals loop

`builderPendingWithdrawalsLoop_run` states the two outcomes of the conditional
`appendState` loop. When the appended values fit, the run writes the old list followed by
the values. The record update names only `builderPendingWithdrawals`, so
`builderPendingPayments` keeps its value. When the values do not fit, the run raises
`.listFull` at the first append past the limit. `cond` is a `Prop` with a `Decidable`
instance, the same as the guard `p.weight ≥ quorum` in the spec body. -/

/-- One `appendState` to `builderPendingWithdrawals` with room: the run succeeds and writes
the longer list. -/
private theorem appendState_run_of_lt [Preset] [HasherTag] (preState : BeaconState)
    (w : BuilderPendingWithdrawal)
    (h : preState.builderPendingWithdrawals.val.size < builderPendingWithdrawalsLimit) :
    (appendState builderPendingWithdrawals w : GloasRun Unit).run (pureState preState) =
      .ok ((), pureState { preState with builderPendingWithdrawals :=
        preState.builderPendingWithdrawals.push w h }) := by
  have hpush : (sszGet (pureState preState) builderPendingWithdrawals).push? w
      = some (preState.builderPendingWithdrawals.push w h) :=
    sszListPush?_of_lt preState.builderPendingWithdrawals w h
  simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_some]
  rfl

/-- One `appendState` to a full `builderPendingWithdrawals`: the run raises `.listFull`, as
the spec's `List.append` raises. -/
private theorem appendState_run_of_le [Preset] [HasherTag] (preState : BeaconState)
    (w : BuilderPendingWithdrawal)
    (h : builderPendingWithdrawalsLimit ≤ preState.builderPendingWithdrawals.val.size) :
    (appendState builderPendingWithdrawals w : GloasRun Unit).run (pureState preState) =
      .error (.listFull "builderPendingWithdrawals") := by
  have hpush : (sszGet (pureState preState) builderPendingWithdrawals).push? w = none :=
    sszListPush?_of_le preState.builderPendingWithdrawals w h
  simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_none]
  rfl

/-- The two outcomes of the loop over any index list. The theorem states the run at the box
level, on `pureState preState`, so the contract below can rewrite with it directly. The
success half takes any list `withdrawals` whose array is the old array followed by the
appended values. Such a list exists exactly when the values fit. So the statement needs
no separate size premise. -/
private theorem builderPendingWithdrawalsList_run [Preset] [HasherTag]
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (l : List Nat) (preState : BeaconState) :
    (∀ withdrawals : SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit,
      withdrawals.val = preState.builderPendingWithdrawals.val ++
          ((l.filter fun i => decide (cond i)).map val).toArray →
      (do for i in l do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : GloasRun Unit).run (pureState preState)
        = .ok ((), pureState { preState with builderPendingWithdrawals := withdrawals })) ∧
    (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
        (l.filter fun i => decide (cond i)).length →
      (do for i in l do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : GloasRun Unit).run (pureState preState)
        = .error (.listFull "builderPendingWithdrawals")) := by
  induction l generalizing preState with
  | nil =>
    refine ⟨fun withdrawals hw => ?_, fun hover => ?_⟩
    · have hsame : withdrawals = preState.builderPendingWithdrawals :=
        Subtype.ext (by simpa using hw)
      rw [hsame]
      rfl
    · have hcap := preState.builderPendingWithdrawals.property
      simp at hover
      omega
  | cons i rest ih =>
    by_cases h : cond i
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = i :: List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_pos]; simpa using h
      rw [hfilter]
      by_cases hlt : preState.builderPendingWithdrawals.val.size < builderPendingWithdrawalsLimit
      · -- The append has room: step to the value with the longer list, then use `ih`.
        have hstep := appendState_run_of_lt preState (val i) hlt
        obtain ⟨ihok, iherr⟩ := ih
          { preState with
            builderPendingWithdrawals := preState.builderPendingWithdrawals.push (val i) hlt }
        refine ⟨fun withdrawals hw => ?_, fun hover => ?_⟩
        · simp only [List.forIn_cons, run_bind, ite_eq_left h, hstep, except_bind_ok, run_pure]
          exact ihok withdrawals (by rw [hw]; simp)
        · simp only [List.forIn_cons, run_bind, ite_eq_left h, hstep, except_bind_ok, run_pure]
          exact iherr (by simp only [sszListPush_val, Array.size_push]; simp at hover; omega)
      · -- The list is full: this append raises, and the rest of the loop never runs.
        have hstep := appendState_run_of_le preState (val i) (by omega)
        refine ⟨fun withdrawals hw => ?_, fun _ => ?_⟩
        · have hsize := congrArg Array.size hw
          have hcap := withdrawals.property
          simp at hsize
          omega
        · simp only [List.forIn_cons, run_bind, ite_eq_left h, hstep, except_bind_error]
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      rw [hfilter]
      obtain ⟨ihok, iherr⟩ := ih preState
      refine ⟨fun withdrawals hw => ?_, fun hover => ?_⟩
      · simp only [List.forIn_cons, run_bind, ite_eq_right h, run_pure, except_bind_ok]
        exact ihok withdrawals hw
      · simp only [List.forIn_cons, run_bind, ite_eq_right h, run_pure, except_bind_ok]
        exact iherr hover

/-- `processBuilderPendingPayments`'s withdrawals loop over `[0:n]`, the source's own
range: the list statement above at `List.range n`. -/
private theorem builderPendingWithdrawalsLoop_run [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) :
    (∀ withdrawals : SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit,
      withdrawals.val = preState.builderPendingWithdrawals.val ++
          (((List.range n).filter fun i => decide (cond i)).map val).toArray →
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : GloasRun Unit).run (pureState preState)
        = .ok ((), pureState { preState with builderPendingWithdrawals := withdrawals })) ∧
    (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
        ((List.range n).filter fun i => decide (cond i)).length →
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : GloasRun Unit).run (pureState preState)
        = .error (.listFull "builderPendingWithdrawals")) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact builderPendingWithdrawalsList_run cond val (List.range n) preState

/-! ## The named values the transition produces

`builderPaymentQuorum`, `qualifyingBuilderWithdrawals`, and `expectedPaymentWindow` name
the values in `processBuilderPendingPayments_run`'s conclusion, over plain `BeaconState`
values. A spec accessor that takes the boxed `State` reads `pureState state`, so the names
stay free of any box of their own. -/

/-- The quorum threshold of `processBuilderPendingPayments`. It is a separate
definition, so `qualifyingBuilderWithdrawals` and the theorems below use one copy. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) : Gwei :=
  (getTotalActiveBalance (pureState state) / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The withdrawals of the payments from the previous epoch whose weight reaches
`builderPaymentQuorum`, in slot order. The substep appends these. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : BeaconState) :
    List BuilderPendingWithdrawal :=
  let payments := state.builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ builderPaymentQuorum state)).map
    fun i => (vget payments i).withdrawal

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

`processBuilderPendingPayments_run` is the contract. Its success half joins the success
half of `builderPendingWithdrawalsLoop_run` with the final `modifyState`. The loop never
writes the payment window, so that final read sees the input value. The reject half is
the loop's reject half: the `modifyState` after the loop never runs. -/

/-- The two outcomes of `processBuilderPendingPayments` on the uncached box. They split on
whether the qualifying withdrawals fit under `BUILDER_PENDING_WITHDRAWALS_LIMIT`.

- They fit. Take the list `withdrawals` that holds the old list followed by
  `qualifyingBuilderWithdrawals preState`. The step on `pureState preState` returns the
  uncached box of `preState` with only the two fields written. Such a list exists exactly
  when the withdrawals fit.
- They do not fit. The run raises `.listFull`. pyspec raises the same uncaught fault at
  the same append.

The theorem states the run at the box level, so the fork-choice bridge applies it
directly. `processBuilderPendingPayments_run_of_fits` and
`processBuilderPendingPayments_run_of_overflow` read the two halves in `runPure` form. -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (∀ withdrawals : SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit,
        withdrawals.val = preState.builderPendingWithdrawals.val ++
            (qualifyingBuilderWithdrawals preState).toArray →
        (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
          = .ok ((), pureState { preState with
              builderPendingWithdrawals := withdrawals,
              builderPendingPayments := expectedPaymentWindow preState })) ∧
      (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
          (qualifyingBuilderWithdrawals preState).length →
        (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
          = .error (.listFull "builderPendingWithdrawals")) := by
  intro preState
  obtain ⟨hloopOk, hloopErr⟩ := builderPendingWithdrawalsLoop_run slotsPerEpoch
    (fun i => (vget preState.builderPendingPayments i).weight ≥ builderPaymentQuorum preState)
    (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
  -- `qualifyingBuilderWithdrawals` is the loop's filtered list mapped to withdrawals, so
  -- its length is the filter's length.
  have hlen : (qualifyingBuilderWithdrawals preState).length =
      ((List.range slotsPerEpoch).filter fun i =>
        decide ((vget preState.builderPendingPayments i).weight ≥
          builderPaymentQuorum preState)).length := by
    simp [qualifyingBuilderWithdrawals]
  refine ⟨fun withdrawals hw => ?_, fun hover => ?_⟩
  · obtain ⟨a, hbare⟩ := run_of_run_seq_pure _ _ _ (hloopOk withdrawals hw)
    -- Re-elaborate the source shape here so the loop term matches `hbare`'s left side and
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
          builderPendingWithdrawals := withdrawals,
          builderPendingPayments := expectedPaymentWindow preState })
    rw [run_bind, hbare, except_bind_ok]
    unfold expectedPaymentWindow
    rfl
  · have hbare := run_of_run_seq_pure_error _ _ _ (hloopErr (by rw [← hlen]; exact hover))
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
      = .error (.listFull "builderPendingWithdrawals")
    rw [run_bind, hbare, except_bind_error]

/-- The success half of `processBuilderPendingPayments_run`, at the value level. Under the
capacity hypothesis, the run appends every qualifying withdrawal in slot order and shifts
the payment window. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (preState : BeaconState)
    (hfits : preState.builderPendingWithdrawals.val.size +
      (qualifyingBuilderWithdrawals preState).length ≤ builderPendingWithdrawalsLimit) :
    runPure (processBuilderPendingPayments (StateTransition := GloasRun)) preState
      = .ok ((), { preState with
          builderPendingWithdrawals :=
            ⟨preState.builderPendingWithdrawals.val ++ (qualifyingBuilderWithdrawals preState).toArray,
              by simp only [Array.size_append, List.size_toArray]; omega⟩,
          builderPendingPayments := expectedPaymentWindow preState }) :=
  runPure_of_run_ok ((processBuilderPendingPayments_run preState).1 _ rfl)

/-- The reject half of `processBuilderPendingPayments_run`, at the value level. When the
qualifying withdrawals do not fit under the list limit, the substep raises `.listFull`. -/
theorem processBuilderPendingPayments_run_of_overflow [Preset] [HasherTag]
    (preState : BeaconState)
    (hover : builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
      (qualifyingBuilderWithdrawals preState).length) :
    runPure (processBuilderPendingPayments (StateTransition := GloasRun)) preState
      = .error (.listFull "builderPendingWithdrawals") := by
  rw [runPure_eq, (processBuilderPendingPayments_run preState).2 hover]
  rfl

end EthCLSpecs.Proofs.Gloas
