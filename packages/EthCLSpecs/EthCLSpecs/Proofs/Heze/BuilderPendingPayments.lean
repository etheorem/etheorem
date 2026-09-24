import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Proofs.Heze.Run
import SizzLean.Proofs.SSZListPush

/-!
# `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the builder-payment epoch substep

Heze inherits `processBuilderPendingPayments` from Gloas
(`Heze/EpochProcessing.lean:110`). The inheritance makes a new constant,
`EthCLSpecs.Heze.processBuilderPendingPayments`, so the Gloas theorem in
`Proofs/Gloas/BuilderPendingPayments.lean` does not cover it. This module ports that
proof to the Heze constant. It also adds a per-entry fact,
`mem_qualifyingPaymentIndices_iff`: an entry is qualifying if and only if its weight
reaches the quorum. With the capacity hypothesis of
`processBuilderPendingPayments_run_of_fits`, the function queues the withdrawal of each
qualifying entry. Without that hypothesis, the clamp below can drop it. After a child
block on the EMPTY edge, this substep is the remaining path for a bid.

The function changes two fields, one after the other, in one state transition. This
file proves each change on its own, then joins them into one theorem about the
function. The function pushes the withdrawal of each qualifying payment from the
previous epoch through the bounded `SSZList.push`, in slot order. Under an explicit
capacity hypothesis, it appends every qualifying withdrawal. Then it shifts the payment
window down by `SLOTS_PER_EPOCH` and fills the empty half with empty payments.

**Known differences from pyspec.** There are two. `processBuilderPendingPayments_run`
states the model's behavior in both cases.

1. At the list limit (`2^20` withdrawals), pyspec's `builder_pending_withdrawals.append`
   raises, and the state transition is invalid. The model's `SSZList.push` drops the
   withdrawal and the run succeeds.
2. The quorum is `(total / SLOTS_PER_EPOCH) * 6 / 10` in `UInt64`. When the per-slot
   balance is more than `2^64 / 6` Gwei, the product overflows. pyspec's `uint64`
   raises. The model's product wraps, and the run continues with a wrong quorum.

No conformance vector reaches either case. `IMPLEMENTATION_NOTES.md`, "Gloas diff",
records both as open gaps. The Gloas theorem has the same differences.

The withdrawals side has two parts:

1. a pure fact about the clamp in `SSZList.push`: a fold of `push` over a list gives
   the original list plus the prefix that fits. This fact has no condition, and
   `SizzLean.Proofs.SSZListPush` proves it for all lists;
2. the reduction of the loop to that fold, in iteration order.

This file does not assume or prove a capacity invariant. The claim that every
qualifying withdrawal is appended is a corollary of the clamp fact. It needs the
explicit hypothesis `original.size + qualifying.length ≤ builderPendingWithdrawalsLimit`.

The window side applies the general behavior of `shiftWindow`.
`expectedPaymentWindow_get_lt` and `expectedPaymentWindow_get_upper` state the two
facts about index regions. The old upper half moves down. The new upper half is empty.
`processBuilderPendingPayments` reads `builderPendingPayments` twice: before the
withdrawals loop, and again from the state after the loop, as pyspec does. The loop
does not write that field. So both reads give the same value.

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
open EthCLSpecs.Heze.Const (slotsPerEpoch builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
open EthCLSpecs.Proofs (run_bind run_pure)
open SizzLean.Proofs (sszListFoldlPush_val_of_fits)

/-- For a single `for` loop `x`, `do x` elaborates as `x >>= fun _ => pure ()`. This
lemma removes that wrapper. A fact about the loop then applies at a use site that runs
the bare `forIn` before more code. -/
private theorem run_of_run_seq_pure {ε σ : Type} (x : StateT σ (Except ε) PUnit) (s0 s1 : σ)
    (h : (x >>= fun _ => (pure () : StateT σ (Except ε) Unit)).run s0 = .ok ((), s1)) :
    x.run s0 = .ok (PUnit.unit, s1) := by
  rw [run_bind] at h
  cases hx : x.run s0 with
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hx] at h
    cases a
    simpa only [run_pure] using h
  | error e => rw [hx] at h; simp at h

/-- The reduction of the withdrawals loop. The loop of conditional `appendState` calls
always succeeds. Its effect on the state is a pure `SSZList.push` fold over the
qualifying indices (`sszListFoldlPush_val` states the clamp). The loop does not change
`builderPendingPayments`. `cond` is a `Prop` with a `Decidable` instance, the same as
the guard `p.weight ≥ quorum` in the spec body. The theorem compares fields through
`sszGet`. -/
private theorem builderPendingWithdrawalsLoop_run [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (state0 : State) :
    ∃ resultState : State,
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : HezeRun Unit).run state0 = .ok ((), resultState) ∧
      sszGet resultState builderPendingWithdrawals =
        (((List.range n).filter fun i => decide (cond i)).map val).foldl
          (fun l w => l.push w) (sszGet state0 builderPendingWithdrawals) ∧
      sszGet resultState builderPendingPayments = sszGet state0 builderPendingPayments := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  induction (List.range n) generalizing state0 with
  | nil => exact ⟨state0, rfl, by simp, rfl⟩
  | cons i rest ih =>
    by_cases h : cond i
    · have hstep : (appendState builderPendingWithdrawals (val i) : HezeRun Unit).run state0 =
          .ok ((), sszUpdate state0 with
            builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i)) := by
        cases state0 <;> rfl
      obtain ⟨resultState, hrun, hw, hp⟩ := ih (sszUpdate state0 with
        builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i))
      refine ⟨resultState, ?_, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [h, if_pos, run_bind, hstep]
        exact hrun
      · have hgetW : sszGet (sszUpdate state0 with
            builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i))
            builderPendingWithdrawals = (sszGet state0 builderPendingWithdrawals).push (val i) := by
          cases state0 <;> rfl
        have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest)) =
            i :: List.filter (fun i => decide (cond i)) rest := by
          rw [List.filter_cons_of_pos]; simpa using h
        rw [hw, hgetW, hfilter, List.map_cons, List.foldl_cons]
      · have hgetP : sszGet (sszUpdate state0 with
            builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i))
            builderPendingPayments = sszGet state0 builderPendingPayments := by
          cases state0 <;> rfl
        rw [hp, hgetP]
    · obtain ⟨resultState, hrun, hw, hp⟩ := ih state0
      refine ⟨resultState, ?_, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [h, run_bind, run_pure]
        exact hrun
      · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest)) =
            List.filter (fun i => decide (cond i)) rest := by
          rw [List.filter_cons_of_neg]; simpa using h
        rw [hw, hfilter]
      · exact hp

/-- The quorum threshold of `processBuilderPendingPayments`. It is a separate
definition, so `qualifyingPaymentIndices`, `expectedWithdrawals`, and their theorems
use one copy. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : State) : Gwei :=
  (getTotalActiveBalance state / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The indices `i < SLOTS_PER_EPOCH` of the payments from the previous epoch whose
weight reaches `builderPaymentQuorum`, in slot order. -/
def qualifyingPaymentIndices [Preset] [HasherTag] (state : State) : List Nat :=
  (List.range slotsPerEpoch).filter fun i =>
    decide ((vget (sszGet state builderPendingPayments) i).weight ≥ builderPaymentQuorum state)

/-- The withdrawals of the qualifying payments from the previous epoch, in slot order,
before the capacity clamp of `SSZList.push`. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : State) :
    List BuilderPendingWithdrawal :=
  (qualifyingPaymentIndices state).map fun i =>
    (vget (sszGet state builderPendingPayments) i).withdrawal

/-- The value of `builderPendingWithdrawals` after `processBuilderPendingPayments`. It
is `qualifyingBuilderWithdrawals`, folded through `SSZList.push`, from the current
value of the field. `sszListFoldlPush_val` and `sszListFoldlPush_val_of_fits` state
the clamp behavior of this fold. -/
def expectedWithdrawals [Preset] [HasherTag] (state : State) :
    SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit :=
  (qualifyingBuilderWithdrawals state).foldl (fun l w => l.push w)
    (sszGet state builderPendingWithdrawals)

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

/-- The postcondition of `processBuilderPendingPayments_run`. The two changed fields of
`after` equal `expectedWithdrawals before` and `expectedPaymentWindow before`. It has a
name, so the capacity corollary can restate the withdrawals half and reuse the window
half. -/
def ProcessBuilderPendingPaymentsPost [Preset] [HasherTag] (before after : State) : Prop :=
  sszGet after builderPendingWithdrawals = expectedWithdrawals before ∧
  sszGet after builderPendingPayments = expectedPaymentWindow before

/-- For any input state, `processBuilderPendingPayments` succeeds, and the result
satisfies `ProcessBuilderPendingPaymentsPost`. The proof joins
`builderPendingWithdrawalsLoop_run` (the withdrawals loop) and the direct application
of `shiftWindow` (the window shift). The module docstring describes these two
effects. -/
@[characterizes EthCLSpecs.Heze.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] (before : State) :
    ∃ after : State,
      (processBuilderPendingPayments : HezeRun Unit).run before = .ok ((), after) ∧
      ProcessBuilderPendingPaymentsPost before after := by
  obtain ⟨resultState, hrun, hw, hp⟩ :=
    builderPendingWithdrawalsLoop_run slotsPerEpoch
      (fun i => (vget (sszGet before builderPendingPayments) i).weight ≥
        builderPaymentQuorum before)
      (fun i => (vget (sszGet before builderPendingPayments) i).withdrawal) before
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
    unfold expectedWithdrawals qualifyingBuilderWithdrawals qualifyingPaymentIndices
      builderPaymentQuorum
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

/-- The capacity corollary of `processBuilderPendingPayments_run`. Under an explicit
capacity hypothesis, the function appends every qualifying withdrawal in slot order,
and the `SSZList.push` clamp does not apply. The window half is the same as in
`ProcessBuilderPendingPaymentsPost`. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag] (before : State)
    (hfits : (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit) :
    ∃ after : State,
      (processBuilderPendingPayments : HezeRun Unit).run before = .ok ((), after) ∧
      (sszGet after builderPendingWithdrawals).val =
        (sszGet before builderPendingWithdrawals).val ++
          (qualifyingBuilderWithdrawals before).toArray ∧
      sszGet after builderPendingPayments = expectedPaymentWindow before := by
  obtain ⟨after, hrun, hw, hp⟩ := processBuilderPendingPayments_run before
  refine ⟨after, hrun, ?_, hp⟩
  rw [hw]
  unfold expectedWithdrawals
  exact sszListFoldlPush_val_of_fits _ _ hfits

/-- Take an entry `i` in the previous-epoch half of the payment window. Entry `i` is
qualifying if and only if its weight reaches the quorum. This lemma is about the
proof-side filter `qualifyingPaymentIndices` only. Under the capacity hypothesis of
`processBuilderPendingPayments_run_of_fits`, the function appends the withdrawal of
entry `i` exactly when entry `i` is qualifying. At the list limit, the clamp can drop
the withdrawal of a qualifying entry. -/
theorem mem_qualifyingPaymentIndices_iff [Preset] [HasherTag] (state : State) (i : Nat)
    (hi : i < slotsPerEpoch) :
    i ∈ qualifyingPaymentIndices state ↔
      (vget (sszGet state builderPendingPayments) i).weight ≥ builderPaymentQuorum state := by
  simp [qualifyingPaymentIndices, List.mem_filter, List.mem_range, hi]

end EthCLSpecs.Proofs.Heze
