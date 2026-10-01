import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Operations
import EthCLSpecs.Proofs.Heze.Run
import SizzLean.Proofs.SSZListPush

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
`expectedPaymentWindow_get_lt` and `expectedPaymentWindow_get_upper` state the two
facts about index regions. The old upper half moves down. The new upper half is empty.
`processBuilderPendingPayments` reads `builderPendingPayments` twice: before the
withdrawals loop, and again from the state after the loop, as pyspec does. The loop
does not write that field. So both reads give the same value.

`processBuilderPendingPayments_run_bid` states the call for one bid. It takes
`BidPaymentCarried`: the entry for the slot of the bid still carries the withdrawal of
the bid.

This file proves only the local effect of one call, for any input state. It does not
prove that each payment settles exactly once across the protocol. It does not relate
this substep to `settleBuilderPayment` or `processProposerSlashing`. Those two paths can
clear a `BuilderPendingPayment` before this substep runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, section "Heze".

Every theorem below states its conclusions about the state through `sszGet`, for the
two fields the function changes. None of them uses equality of whole `State` values.
The cache overlay of a `State` adds one pending write for each `sszUpdate` call, so two
states with equal fields can differ as values. The theorems state no frame condition
for the other fields.

-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLSpecs.Heze
open EthCLSpecs.Heze (Preset Gwei)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  builderPaymentThresholdNumerator builderPaymentThresholdDenominator
  builderPendingWithdrawalsLimit)
open EthCLSpecs.Proofs (run_bind run_pure run_getThe except_bind_ok run_of_run_seq_pure
  run_of_run_seq_pure_error)
open SizzLean.Proofs (sszListPush_val sszListPush?_of_lt sszListPush?_of_le)

/-- One `appendState` to `builderPendingWithdrawals` with room: the run succeeds and writes
the longer list. -/
private theorem appendState_run_of_lt [Preset] [HasherTag] (state0 : State)
    (w : BuilderPendingWithdrawal)
    (h : (sszGet state0 builderPendingWithdrawals).val.size < builderPendingWithdrawalsLimit) :
    (appendState builderPendingWithdrawals w : HezeRun Unit).run state0 =
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
    (appendState builderPendingWithdrawals w : HezeRun Unit).run state0 =
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
            : HezeRun Unit).run state0 = .ok ((), resultState) ∧
        (sszGet resultState builderPendingWithdrawals).val =
          (sszGet state0 builderPendingWithdrawals).val ++
            (((List.range n).filter fun i => decide (cond i)).map val).toArray ∧
        sszGet resultState builderPendingPayments = sszGet state0 builderPendingPayments) ∧
    (builderPendingWithdrawalsLimit < (sszGet state0 builderPendingWithdrawals).val.size +
        ((List.range n).filter fun i => decide (cond i)).length →
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : HezeRun Unit).run state0 = .error (.listFull "builderPendingWithdrawals")) := by
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

/-- The quorum threshold of `processBuilderPendingPayments`. It is a separate
definition, so `qualifyingPaymentIndices` and the theorems below use one copy. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : State) : Gwei :=
  (getTotalActiveBalance state / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The indices `i < SLOTS_PER_EPOCH` of the payments from the previous epoch whose
weight reaches `builderPaymentQuorum`, in slot order. -/
def qualifyingPaymentIndices [Preset] [HasherTag] (state : State) : List Nat :=
  (List.range slotsPerEpoch).filter fun i =>
    decide ((vget (sszGet state builderPendingPayments) i).weight ≥ builderPaymentQuorum state)

/-- The withdrawals of the qualifying payments from the previous epoch, in slot order.
The substep appends these. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : State) :
    List BuilderPendingWithdrawal :=
  (qualifyingPaymentIndices state).map fun i =>
    (vget (sszGet state builderPendingPayments) i).withdrawal

/-- The value of `builderPendingPayments` after `processBuilderPendingPayments`. It is
the current value of the field, shifted down by `SLOTS_PER_EPOCH`, with empty payments
in the upper half. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : State) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- The lower half of `expectedPaymentWindow`. Each index `i < slotsPerEpoch` holds the
old entry at `i + slotsPerEpoch`. -/
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

/-- The upper half of `expectedPaymentWindow`. Each index in
`[slotsPerEpoch, 2 * slotsPerEpoch)` holds the empty `BuilderPendingPayment`. -/
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
@[characterizes EthCLSpecs.Heze.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] (before : State) :
    ((sszGet before builderPendingWithdrawals).val.size +
        (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit →
      ∃ after : State,
        (processBuilderPendingPayments : HezeRun Unit).run before = .ok ((), after) ∧
        ProcessBuilderPendingPaymentsPost before after) ∧
    (builderPendingWithdrawalsLimit < (sszGet before builderPendingWithdrawals).val.size +
        (qualifyingBuilderWithdrawals before).length →
      (processBuilderPendingPayments : HezeRun Unit).run before =
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
    simp [qualifyingBuilderWithdrawals, qualifyingPaymentIndices]
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
          : HezeRun Unit).run before =
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
      unfold qualifyingBuilderWithdrawals qualifyingPaymentIndices builderPaymentQuorum
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
        : HezeRun Unit).run before = .error (.listFull "builderPendingWithdrawals")
    simp only [run_bind, builderPaymentQuorum, hbare]
    rfl

/-- The success half of `processBuilderPendingPayments_run`, spelled out: under the
capacity hypothesis, every qualifying withdrawal is appended in slot order, and the
payment window shifts. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (before : State)
    (hfits : (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit) :
    ∃ after : State,
      (processBuilderPendingPayments : HezeRun Unit).run before = .ok ((), after) ∧
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
    (processBuilderPendingPayments : HezeRun Unit).run before =
      .error (.listFull "builderPendingWithdrawals") :=
  (processBuilderPendingPayments_run before).2 hover

/-- Take an entry `i` in the previous-epoch half of the payment window. Entry `i` is
qualifying if and only if its weight reaches the quorum. The lemma unfolds the
proof-side filter `qualifyingPaymentIndices`, the filter that
`processBuilderPendingPayments_run` states the queued withdrawals with. -/
theorem mem_qualifyingPaymentIndices_iff [Preset] [HasherTag] (state : State) (i : Nat)
    (hi : i < slotsPerEpoch) :
    i ∈ qualifyingPaymentIndices state ↔
      (vget (sszGet state builderPendingPayments) i).weight ≥ builderPaymentQuorum state := by
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
def BidPaymentCarried [Preset] [HasherTag] (state : State) (bid : ExecutionPayloadBid) :
    Prop :=
  (vget (sszGet state builderPendingPayments) (builderPaymentIndex bid.slot false)).withdrawal
    = bidWithdrawal bid

/-- The index of a slot in the previous-epoch half is less than `SLOTS_PER_EPOCH`. -/
theorem builderPaymentIndex_previous_lt [Preset] (slot : Slot) :
    builderPaymentIndex slot false < slotsPerEpoch := by
  have := uint64ModOfNatToNatLt slot slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  simpa [builderPaymentIndex, umodIdx] using this

/-- The weight of the entry for the slot of `bid` in the previous-epoch half. -/
def bidPaymentWeight [Preset] [HasherTag] (state : State) (bid : ExecutionPayloadBid) : Gwei :=
  (vget (sszGet state builderPendingPayments) (builderPaymentIndex bid.slot false)).weight

/-- What the epoch substep does with the payment of `bid`, from `before` to `after`. It
appends the withdrawals of the entries at `qualifyingPaymentIndices before`, in slot
order. The entry of the bid is among them if and only if its weight reaches
`builderPaymentQuorum`. At or above the quorum, the withdrawal of the bid is in the result.
Below it, the entry of the bid is not appended.

The claim is about the entry of the bid, not about the withdrawal value. Below the quorum,
an equal withdrawal can still be in the result, from the list before the substep or from
another entry. -/
structure EpochPaysBidIffQuorum [Preset] [HasherTag] (before after : State)
    (bid : ExecutionPayloadBid) : Prop where
  /-- The substep appends the withdrawals of the entries at `qualifyingPaymentIndices
  before`, in slot order (`qualifyingBuilderWithdrawals`). -/
  appended : (sszGet after builderPendingWithdrawals).val =
    (sszGet before builderPendingWithdrawals).val ++
      (qualifyingBuilderWithdrawals before).toArray
  /-- The entry of the bid is qualifying if and only if its weight reaches the quorum. -/
  qualifying_iff : builderPaymentIndex bid.slot false ∈ qualifyingPaymentIndices before ↔
    bidPaymentWeight before bid ≥ builderPaymentQuorum before
  /-- When the weight reaches the quorum, the withdrawal of the bid is queued. -/
  paid : bidPaymentWeight before bid ≥ builderPaymentQuorum before →
    bidWithdrawal bid ∈ (sszGet after builderPendingWithdrawals).val
  /-- When the weight is below the quorum, the slot of the bid is not among the entries
  whose withdrawals `appended` adds, so the entry of the bid is not appended. -/
  unpaid : bidPaymentWeight before bid < builderPaymentQuorum before →
    builderPaymentIndex bid.slot false ∉ qualifyingPaymentIndices before

/-- The epoch substep appends the entry of the bid if and only if the entry reaches the
quorum. Take a state where the payment of `bid` is carried (`BidPaymentCarried`), and
where the qualifying withdrawals fit under the list limit. Then
`processBuilderPendingPayments` succeeds, and `EpochPaysBidIffQuorum` holds. -/
theorem processBuilderPendingPayments_run_bid [Preset] [HasherTag] (before : State)
    (bid : ExecutionPayloadBid) (hcarried : BidPaymentCarried before bid)
    (hfits : (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit) :
    ∃ after : State,
      (processBuilderPendingPayments : HezeRun Unit).run before = .ok ((), after) ∧
      EpochPaysBidIffQuorum before after bid := by
  obtain ⟨after, hrun, hw, -⟩ := processBuilderPendingPayments_run_of_fits before hfits
  have hiff := mem_qualifyingPaymentIndices_iff before _
    (builderPaymentIndex_previous_lt bid.slot)
  refine ⟨after, hrun, ⟨hw, hiff, fun hq => ?_, fun hlt hmem => ?_⟩⟩
  rotate_left
  · -- Below the quorum, membership would give `weight ≥ quorum`, against `hlt`.
    exact absurd (hiff.mp hmem) (UInt64.not_le.mpr hlt)
  unfold BidPaymentCarried at hcarried
  rw [hw, Array.mem_append]
  right
  unfold qualifyingBuilderWithdrawals
  rw [List.mem_toArray]
  exact List.mem_map.mpr ⟨_, hiff.mpr hq, hcarried⟩

end EthCLSpecs.Proofs.Heze
