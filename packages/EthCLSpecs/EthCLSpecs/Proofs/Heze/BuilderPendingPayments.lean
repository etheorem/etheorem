import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Operations
import EthCLSpecs.Proofs.Heze.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.SSZListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the builder-payment epoch substep

Heze inherits `processBuilderPendingPayments` from Gloas
(`Heze/EpochProcessing.lean:110`). The inheritance makes a new constant,
`EthCLSpecs.Heze.processBuilderPendingPayments`, so the Gloas theorem in
`Proofs/Gloas/BuilderPendingPayments.lean` does not cover it. This module ports that
proof to the Heze constant. It also adds `mem_qualifyingPaymentIndices_iff`: an entry
of the proof-side filter is qualifying if and only if its weight reaches the quorum.
After a child block on the EMPTY edge, this substep is the remaining path for a bid.

The function changes two fields, one after the other, in one state transition. It
appends the withdrawal of each qualifying payment from the previous epoch to
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
`expectedPaymentWindow_get_lt` and `expectedPaymentWindow_get_upper` state the two
facts about index regions. The old upper half moves down. The new upper half is empty.
`processBuilderPendingPayments` reads `builderPendingPayments` twice: before the
withdrawals loop, and again from the state after the loop, as pyspec does. The loop
does not write that field. So both reads give the same value.

`processBuilderPendingPayments_run_bid` states the call for one bid. It takes
`BidPaymentCarried`: the entry for the slot of the bid still carries the withdrawal of
the bid.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The contract
`processBuilderPendingPayments_run` states the run at the box, in `.run` form, because
that is the shape the fork-choice bridge consumes. The readings state the `runPure` form.

This file proves only the local effect of one call, for any input value. It does not
prove that each payment settles exactly once across the protocol. It does not relate
this substep to `settleBuilderPayment` or `processProposerSlashing`. Those two paths can
clear a `BuilderPendingPayment` before this substep runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, section "Heze".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_eq runPure_of_run_ok run_bind run_pure
  run_getThe except_bind_ok except_bind_error run_of_run_seq_pure run_of_run_seq_pure_error)
open EthCLSpecs.Heze
open EthCLSpecs.Heze (Preset Gwei BeaconState)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  builderPaymentThresholdNumerator builderPaymentThresholdDenominator
  builderPendingWithdrawalsLimit)
open SizzLean.Proofs (sszListPush_val sszListPush?_of_lt sszListPush?_of_le)

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
    (appendState builderPendingWithdrawals w : HezeRun Unit).run (pureState preState) =
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
    (appendState builderPendingWithdrawals w : HezeRun Unit).run (pureState preState) =
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
          : HezeRun Unit).run (pureState preState)
        = .ok ((), pureState { preState with builderPendingWithdrawals := withdrawals })) ∧
    (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
        (l.filter fun i => decide (cond i)).length →
      (do for i in l do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : HezeRun Unit).run (pureState preState)
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
        · simp only [List.forIn_cons, run_bind, if_pos h, hstep, except_bind_ok, run_pure]
          exact ihok withdrawals (by rw [hw]; simp)
        · simp only [List.forIn_cons, run_bind, if_pos h, hstep, except_bind_ok, run_pure]
          exact iherr (by simp only [sszListPush_val, Array.size_push]; simp at hover; omega)
      · -- The list is full: this append raises, and the rest of the loop never runs.
        have hstep := appendState_run_of_le preState (val i) (by omega)
        refine ⟨fun withdrawals hw => ?_, fun _ => ?_⟩
        · have hsize := congrArg Array.size hw
          have hcap := withdrawals.property
          simp at hsize
          omega
        · simp only [List.forIn_cons, run_bind, if_pos h, hstep, except_bind_error]
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      rw [hfilter]
      obtain ⟨ihok, iherr⟩ := ih preState
      refine ⟨fun withdrawals hw => ?_, fun hover => ?_⟩
      · simp only [List.forIn_cons, run_bind, if_neg h, run_pure, except_bind_ok]
        exact ihok withdrawals hw
      · simp only [List.forIn_cons, run_bind, if_neg h, run_pure, except_bind_ok]
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
          : HezeRun Unit).run (pureState preState)
        = .ok ((), pureState { preState with builderPendingWithdrawals := withdrawals })) ∧
    (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
        ((List.range n).filter fun i => decide (cond i)).length →
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : HezeRun Unit).run (pureState preState)
        = .error (.listFull "builderPendingWithdrawals")) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact builderPendingWithdrawalsList_run cond val (List.range n) preState

/-! ## The named values the transition produces

`builderPaymentQuorum`, `qualifyingPaymentIndices`, `qualifyingBuilderWithdrawals`, and
`expectedPaymentWindow` name the values in `processBuilderPendingPayments_run`'s
conclusion, over plain `BeaconState` values. A spec accessor that takes the boxed `State`
reads `pureState state`, so the names stay free of any box of their own. -/

/-- The quorum threshold of `processBuilderPendingPayments`. It is a separate
definition, so `qualifyingPaymentIndices` and the theorems below use one copy. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) : Gwei :=
  (getTotalActiveBalance (pureState state) / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The indices `i < SLOTS_PER_EPOCH` of the payments from the previous epoch whose
weight reaches `builderPaymentQuorum`, in slot order. -/
def qualifyingPaymentIndices [Preset] [HasherTag] (state : BeaconState) : List Nat :=
  (List.range slotsPerEpoch).filter fun i =>
    decide ((vget state.builderPendingPayments i).weight ≥ builderPaymentQuorum state)

/-- The withdrawals of the qualifying payments from the previous epoch, in slot order.
The substep appends these. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : BeaconState) :
    List BuilderPendingWithdrawal :=
  (qualifyingPaymentIndices state).map fun i =>
    (vget state.builderPendingPayments i).withdrawal

/-- The value of `builderPendingPayments` after `processBuilderPendingPayments`. It is
the current value of the field, shifted down by `SLOTS_PER_EPOCH`, with empty payments
in the upper half. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : BeaconState) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow state.builderPendingPayments slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- The lower half of `expectedPaymentWindow`. Each index `i < slotsPerEpoch` holds the
old entry at `i + slotsPerEpoch`. -/
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

/-- The upper half of `expectedPaymentWindow`. Each index in
`[slotsPerEpoch, 2 * slotsPerEpoch)` holds the empty `BuilderPendingPayment`. -/
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
@[characterizes EthCLSpecs.Heze.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (∀ withdrawals : SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit,
        withdrawals.val = preState.builderPendingWithdrawals.val ++
            (qualifyingBuilderWithdrawals preState).toArray →
        (processBuilderPendingPayments (StateTransition := HezeRun)).run (pureState preState)
          = .ok ((), pureState { preState with
              builderPendingWithdrawals := withdrawals,
              builderPendingPayments := expectedPaymentWindow preState })) ∧
      (builderPendingWithdrawalsLimit < preState.builderPendingWithdrawals.val.size +
          (qualifyingBuilderWithdrawals preState).length →
        (processBuilderPendingPayments (StateTransition := HezeRun)).run (pureState preState)
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
    simp [qualifyingBuilderWithdrawals, qualifyingPaymentIndices]
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
        : HezeRun Unit).run (pureState preState)
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
        : HezeRun Unit).run (pureState preState)
      = .error (.listFull "builderPendingWithdrawals")
    rw [run_bind, hbare, except_bind_error]

/-- The success half of `processBuilderPendingPayments_run`, at the value level. Under the
capacity hypothesis, the run appends every qualifying withdrawal in slot order and shifts
the payment window. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (preState : BeaconState)
    (hfits : preState.builderPendingWithdrawals.val.size +
      (qualifyingBuilderWithdrawals preState).length ≤ builderPendingWithdrawalsLimit) :
    runPure (processBuilderPendingPayments (StateTransition := HezeRun)) preState
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
    runPure (processBuilderPendingPayments (StateTransition := HezeRun)) preState
      = .error (.listFull "builderPendingWithdrawals") := by
  rw [runPure_eq, (processBuilderPendingPayments_run preState).2 hover]
  rfl

/-- Take an entry `i` in the previous-epoch half of the payment window. Entry `i` is
qualifying if and only if its weight reaches the quorum. The lemma unfolds the
proof-side filter `qualifyingPaymentIndices`, the filter that
`processBuilderPendingPayments_run` states the queued withdrawals with. -/
theorem mem_qualifyingPaymentIndices_iff [Preset] [HasherTag] (state : BeaconState) (i : Nat)
    (hi : i < slotsPerEpoch) :
    i ∈ qualifyingPaymentIndices state ↔
      (vget state.builderPendingPayments i).weight ≥ builderPaymentQuorum state := by
  simp [qualifyingPaymentIndices, List.mem_filter, List.mem_range, hi]

/-- The withdrawal that `processExecutionPayloadBid` records for a bid with a nonzero
value (`Gloas/Operations.lean`, `process_execution_payload_bid`). -/
def bidWithdrawal [Preset] (bid : ExecutionPayloadBid) : BuilderPendingWithdrawal :=
  { feeRecipient := bid.feeRecipient, amount := bid.value, builderIndex := bid.builderIndex }

/-- The payment of `bid` reaches the epoch substep that judges it. At `state`, the entry
for the slot of the bid in the previous-epoch half of the payment window carries the
withdrawal of the bid. The entry got there through the block transitions between the bid
and the substep. `processExecutionPayloadBid` writes it in the current-epoch half, and the
epoch substep one epoch earlier moves it down. A proposer slashing of the block's proposer
clears it, and a child block on the FULL edge settles it (`settleBuilderPayment`). -/
def BidPaymentCarried [Preset] [HasherTag] (state : BeaconState) (bid : ExecutionPayloadBid) :
    Prop :=
  (vget state.builderPendingPayments (builderPaymentIndex bid.slot false)).withdrawal
    = bidWithdrawal bid

/-- The index of a slot in the previous-epoch half is less than `SLOTS_PER_EPOCH`. -/
theorem builderPaymentIndex_previous_lt [Preset] (slot : Slot) :
    builderPaymentIndex slot false < slotsPerEpoch := by
  have := uint64ModOfNatToNatLt slot slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  simpa [builderPaymentIndex, umodIdx] using this

/-- The weight of the entry for the slot of `bid` in the previous-epoch half. -/
def bidPaymentWeight [Preset] [HasherTag] (state : BeaconState) (bid : ExecutionPayloadBid) :
    Gwei :=
  (vget state.builderPendingPayments (builderPaymentIndex bid.slot false)).weight

/-- What the epoch substep does with the payment of `bid`, from `preState` to
`postState`. It appends the withdrawals of the entries at
`qualifyingPaymentIndices preState`, in slot order. The entry of the bid is among them if
and only if its weight reaches `builderPaymentQuorum`. At or above the quorum, the
withdrawal of the bid is in the result. Below it, the entry of the bid is not appended.

The claim is about the entry of the bid, not about the withdrawal value. Below the quorum,
an equal withdrawal can still be in the result, from the list before the substep or from
another entry. -/
structure EpochPaysBidIffQuorum [Preset] [HasherTag] (preState postState : BeaconState)
    (bid : ExecutionPayloadBid) : Prop where
  /-- The substep appends the withdrawals of the entries at `qualifyingPaymentIndices
  preState`, in slot order (`qualifyingBuilderWithdrawals`). -/
  appended : postState.builderPendingWithdrawals.val =
    preState.builderPendingWithdrawals.val ++
      (qualifyingBuilderWithdrawals preState).toArray
  /-- The entry of the bid is qualifying if and only if its weight reaches the quorum. -/
  qualifying_iff : builderPaymentIndex bid.slot false ∈ qualifyingPaymentIndices preState ↔
    bidPaymentWeight preState bid ≥ builderPaymentQuorum preState
  /-- When the weight reaches the quorum, the withdrawal of the bid is queued. -/
  paid : bidPaymentWeight preState bid ≥ builderPaymentQuorum preState →
    bidWithdrawal bid ∈ postState.builderPendingWithdrawals.val
  /-- When the weight is below the quorum, the slot of the bid is not among the entries
  whose withdrawals `appended` adds, so the entry of the bid is not appended. -/
  unpaid : bidPaymentWeight preState bid < builderPaymentQuorum preState →
    builderPaymentIndex bid.slot false ∉ qualifyingPaymentIndices preState

/-- The epoch substep appends the entry of the bid if and only if the entry reaches the
quorum. Take a `preState` where the payment of `bid` is carried (`BidPaymentCarried`),
and where the qualifying withdrawals fit under the list limit. Then
`processBuilderPendingPayments` succeeds, and `EpochPaysBidIffQuorum` holds. -/
theorem processBuilderPendingPayments_run_bid [Preset] [HasherTag] (preState : BeaconState)
    (bid : ExecutionPayloadBid) (hcarried : BidPaymentCarried preState bid)
    (hfits : preState.builderPendingWithdrawals.val.size +
      (qualifyingBuilderWithdrawals preState).length ≤ builderPendingWithdrawalsLimit) :
    ∃ postState : BeaconState,
      runPure (processBuilderPendingPayments (StateTransition := HezeRun)) preState
        = .ok ((), postState) ∧
      EpochPaysBidIffQuorum preState postState bid := by
  refine ⟨_, processBuilderPendingPayments_run_of_fits preState hfits, ?_⟩
  have hiff := mem_qualifyingPaymentIndices_iff preState _
    (builderPaymentIndex_previous_lt bid.slot)
  refine ⟨rfl, hiff, fun hq => ?_, fun hlt hmem => ?_⟩
  · unfold BidPaymentCarried at hcarried
    show bidWithdrawal bid ∈ preState.builderPendingWithdrawals.val ++
      (qualifyingBuilderWithdrawals preState).toArray
    rw [Array.mem_append]
    right
    unfold qualifyingBuilderWithdrawals
    rw [List.mem_toArray]
    exact List.mem_map.mpr ⟨_, hiff.mpr hq, hcarried⟩
  · -- Below the quorum, membership would give `weight ≥ quorum`, against `hlt`.
    exact absurd (hiff.mp hmem) (UInt64.not_le.mpr hlt)

end EthCLSpecs.Proofs.Heze
