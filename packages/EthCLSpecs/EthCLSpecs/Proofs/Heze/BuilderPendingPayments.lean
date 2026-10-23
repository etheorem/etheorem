import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Operations
import EthCLLib.Proofs.Checked
import EthCLSpecs.Proofs.Heze.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.ProgressiveListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the builder-payment epoch substep

Heze inherits `processBuilderPendingPayments` from Gloas
(`Heze/EpochProcessing.lean:129`). The inheritance makes a new constant,
`EthCLSpecs.Heze.processBuilderPendingPayments`, so the Gloas theorem in
`Proofs/Gloas/BuilderPendingPayments.lean` does not cover it. This module ports that
proof to the Heze constant. It also adds `mem_qualifyingPaymentIndices_iff`: an entry
of the proof-side filter is qualifying if and only if its weight reaches the quorum.
After a child block on the EMPTY edge, this substep is the only remaining way to pay a
bid.

The function changes two fields, one after the other, in one state transition. It
appends the withdrawal of each qualifying payment from the previous epoch to
`builderPendingWithdrawals`, in slot order, through `appendState`. Then it shifts the
payment window down by `SLOTS_PER_EPOCH` and fills the empty half with empty payments.

The substep first reads the total active balance for its quorum. That read faults on a
`uint64` overflow of the sum, and `processBuilderPendingPayments_run_total_error` states that
outcome. The quorum then multiplies the per-slot balance by
`BUILDER_PAYMENT_THRESHOLD_NUMERATOR`, a checked product that faults when it reaches
`2 ^ 64` (`QuorumFits`), and `processBuilderPendingPayments_run_quorum_error` states that
outcome. The other theorems take the total and `QuorumFits` as premises.

`builderPendingWithdrawals` is a `ProgressiveList`, and `ProgressiveList.push` always
appends. So, given the total and `QuorumFits`, the run always succeeds.
`processBuilderPendingPayments_run` states that outcome, and `progressiveListFoldlPush_val`
(`SizzLean.Proofs.ProgressiveListPush`) says that the fold of `push` ends at the old list
followed by every value, in order.

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
this substep to `settleBuilderPayment` or `slashValidator`. Those two paths can clear a
`BuilderPendingPayment` before this substep runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, section "Heze".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind run_pure
  except_bind_ok except_bind_error run_of_run_seq_pure)
open EthCLSpecs.Heze
open EthCLSpecs.Heze (Preset Gwei BeaconState)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  builderPaymentThresholdNumerator builderPaymentThresholdDenominator)
open SizzLean.Proofs (progressiveListFoldlPush_val)

/-! ## The withdrawals loop

`builderPendingWithdrawalsLoop_run_eq` is the equation of the conditional `appendState`
loop. The loop always succeeds, and its effect is a `ProgressiveList.push` fold over the
qualifying indices. The record update names only `builderPendingWithdrawals`, so
`builderPendingPayments` keeps its value. `cond` is a `Prop` with a `Decidable`
instance, the same as the guard `p.weight ≥ quorum` in the spec body. -/

/-- The loop equation over any index list. The theorem states the run at the box level,
on `pureState preState`, so the contract below can rewrite with it directly. -/
private theorem builderPendingWithdrawalsList_run_eq [Preset] [HasherTag]
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) (l : List Nat) :
    (do for i in l do
          if cond i then
            appendState builderPendingWithdrawals (val i)
        : HezeRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals :=
            ((l.filter fun i => decide (cond i)).map val).foldl
              (fun l w => l.push w) preState.builderPendingWithdrawals }) := by
  induction l generalizing preState with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : cond i
    · have hstep : (appendState builderPendingWithdrawals (val i) : HezeRun Unit).run
            (pureState preState)
          = .ok ((), pureState { preState with builderPendingWithdrawals :=
            preState.builderPendingWithdrawals.push (val i) }) := rfl
      have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = i :: List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_pos]; simpa using h
      simp only [List.forIn_cons, run_bind, ite_eq_left h, hstep, except_bind_ok, run_pure]
      rw [hfilter, List.map_cons, List.foldl_cons]
      exact ih { preState with builderPendingWithdrawals :=
        preState.builderPendingWithdrawals.push (val i) }
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      simp only [List.forIn_cons, run_bind, ite_eq_right h, run_pure, except_bind_ok]
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
        : HezeRun Unit).run (pureState preState)
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

`builderPaymentQuorum`, `qualifyingPaymentIndices`, `qualifyingBuilderWithdrawals`,
`expectedWithdrawals`, and `expectedPaymentWindow` name the values in
`processBuilderPendingPayments_run`'s conclusion, over plain `BeaconState` values. A spec
accessor that takes the boxed `State` reads `pureState state`, so the names stay free of
any box of their own. -/

/-- The quorum threshold of `processBuilderPendingPayments`, from the total active balance
`total`. The substep reads the total through `getTotalActiveBalance`, which can fault, so the
theorems below take its value as a premise. It is a separate definition, so
`qualifyingPaymentIndices` and the theorems below use one copy. -/
def builderPaymentQuorum [Preset] (total : Gwei) : Gwei :=
  (total / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The quorum product `per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR` stays below
`2 ^ 64` for the total `total`. Then the checked product does not fault, and the quorum is
`builderPaymentQuorum total`. -/
def QuorumFits [Preset] (total : Gwei) : Prop :=
  (total / UInt64.ofNat slotsPerEpoch).toNat * builderPaymentThresholdNumerator.toNat < 2 ^ 64

/-- The quorum product as the substep forms it: the product when it fits. -/
private theorem quorumMul_of_fits [Preset] [HasherTag] (total : Gwei) (h : QuorumFits total) :
    (checkedMul (total / UInt64.ofNat slotsPerEpoch) builderPaymentThresholdNumerator
      "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR"
      : HezeRun Gwei)
      = pure ((total / UInt64.ofNat slotsPerEpoch) * builderPaymentThresholdNumerator) :=
  EthCLLib.Proofs.checkedMul_of_lt _ _ _ h

/-- The indices `i < SLOTS_PER_EPOCH` of the payments from the previous epoch whose
weight reaches `builderPaymentQuorum total`, in slot order. -/
def qualifyingPaymentIndices [Preset] (state : BeaconState) (total : Gwei) : List Nat :=
  (List.range slotsPerEpoch).filter fun i =>
    decide ((vget state.builderPendingPayments i).weight ≥ builderPaymentQuorum total)

/-- The withdrawals of the qualifying payments from the previous epoch, in slot order.
The substep appends these. -/
def qualifyingBuilderWithdrawals [Preset] (state : BeaconState) (total : Gwei) :
    List BuilderPendingWithdrawal :=
  (qualifyingPaymentIndices state total).map fun i =>
    (vget state.builderPendingPayments i).withdrawal

/-- The value of `builderPendingWithdrawals` after `processBuilderPendingPayments`:
`qualifyingBuilderWithdrawals`, folded through `ProgressiveList.push` from the current
value of the field. `progressiveListFoldlPush_val` says that the fold appends every
withdrawal. -/
def expectedWithdrawals [Preset] (state : BeaconState) (total : Gwei) :
    ProgressiveList BuilderPendingWithdrawal :=
  (qualifyingBuilderWithdrawals state total).foldl (fun l w => l.push w)
    state.builderPendingWithdrawals

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

`processBuilderPendingPayments_run` is the contract. It joins
`builderPendingWithdrawalsLoop_run_eq` with the final `modifyState`. The loop never
writes the payment window, so that final read sees the input value. -/

/-- The outcome of `processBuilderPendingPayments` on the uncached box. The step on
`pureState preState` returns the uncached box of `preState` with only the two fields
written. The theorem states the run at the box level, so the fork-choice bridge applies
it directly. `processBuilderPendingPayments_run_appended` reads it in `runPure` form. -/
@[characterizes EthCLSpecs.Heze.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState) (total : Gwei),
      getTotalActiveBalance (pureState preState) = .ok total → QuorumFits total →
      (processBuilderPendingPayments (StateTransition := HezeRun)).run (pureState preState)
        = .ok ((), pureState { preState with
            builderPendingWithdrawals := expectedWithdrawals preState total,
            builderPendingPayments := expectedPaymentWindow preState }) := by
  intro preState total htotal hq
  have hloop := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
    (fun i => (vget preState.builderPendingPayments i).weight ≥ builderPaymentQuorum total)
    (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
  -- The total read succeeds with `total`, so the bind on it is `pure total`.
  have hread : (liftErr (getTotalActiveBalance (pureState preState)) : HezeRun Gwei)
      = pure total := by
    simp only [htotal, liftErr, Except.mapError, MonadExcept.ofExcept]
  -- Re-elaborate the source shape here so the total read can be rewritten, the loop term
  -- matches `hloop`'s left side, and the final `sszUpdate` reduces against the
  -- record-update form on the right.
  show (do
      let t ← (liftErr (getTotalActiveBalance (pureState preState)) : HezeRun Gwei)
      let quorumNumerator ← (checkedMul (t / UInt64.ofNat slotsPerEpoch)
        builderPaymentThresholdNumerator
        "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR"
        : HezeRun Gwei)
      let quorum := quorumNumerator / builderPaymentThresholdDenominator
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
        builderPendingWithdrawals := expectedWithdrawals preState total,
        builderPendingPayments := expectedPaymentWindow preState })
  rw [hread, pure_bind, quorumMul_of_fits total hq, pure_bind]
  show (do
      let quorum := builderPaymentQuorum total
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
        builderPendingWithdrawals := expectedWithdrawals preState total,
        builderPendingPayments := expectedPaymentWindow preState })
  obtain ⟨a, hbare⟩ := run_of_run_seq_pure _ _ _ hloop
  rw [run_bind, hbare, except_bind_ok]
  unfold expectedWithdrawals qualifyingBuilderWithdrawals qualifyingPaymentIndices
    expectedPaymentWindow
  rfl

/-- `processBuilderPendingPayments_run` at the value level. Given the total and
`QuorumFits`, the run appends every qualifying withdrawal in slot order and shifts the
payment window. -/
theorem processBuilderPendingPayments_run_appended [Preset] [HasherTag]
    (preState : BeaconState) (total : Gwei)
    (htotal : getTotalActiveBalance (pureState preState) = .ok total)
    (hq : QuorumFits total) :
    runPure (processBuilderPendingPayments (StateTransition := HezeRun)) preState
      = .ok ((), { preState with
          builderPendingWithdrawals :=
            ⟨preState.builderPendingWithdrawals.val ++
              (qualifyingBuilderWithdrawals preState total).toArray⟩,
          builderPendingPayments := expectedPaymentWindow preState }) := by
  rw [runPure_of_run_ok (processBuilderPendingPayments_run preState total htotal hq)]
  congr 1
  have hval : (expectedWithdrawals preState total).val =
      preState.builderPendingWithdrawals.val ++
        (qualifyingBuilderWithdrawals preState total).toArray := by
    unfold expectedWithdrawals
    rw [progressiveListFoldlPush_val]
  rw [show expectedWithdrawals preState total = ⟨(expectedWithdrawals preState total).val⟩ from by
    cases expectedWithdrawals preState total
    rfl]
  rw [hval]

/-- The quorum product faults: the substep raises `.arithmetic` after the total read and
before the loop. pyspec raises `ValueError` at `per_slot_balance *
BUILDER_PAYMENT_THRESHOLD_NUMERATOR` in `get_builder_payment_quorum_threshold`. -/
theorem processBuilderPendingPayments_run_quorum_error [Preset] [HasherTag]
    (preState : BeaconState) (total : Gwei)
    (htotal : getTotalActiveBalance (pureState preState) = .ok total)
    (hq : ¬ QuorumFits total) :
    (processBuilderPendingPayments (StateTransition := HezeRun)).run (pureState preState)
      = .error (.arithmetic
          "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR") := by
  have hmul := EthCLLib.Proofs.checkedMul_of_ge (m := HezeRun)
    (total / UInt64.ofNat slotsPerEpoch) builderPaymentThresholdNumerator
    "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR"
    (Nat.le_of_not_lt hq)
  simp [processBuilderPendingPayments, htotal, liftErr, Except.mapError, MonadExcept.ofExcept,
    hmul, throwArithmetic]
  rfl

/-- The total read faults: the substep raises that fault before the loop. The read is
`get_total_active_balance`, which faults only on a `uint64` overflow of the sum. -/
theorem processBuilderPendingPayments_run_total_error [Preset] [HasherTag]
    (preState : BeaconState) (err : StateTransitionError)
    (htotal : getTotalActiveBalance (pureState preState) = .error err) :
    (processBuilderPendingPayments (StateTransition := HezeRun)).run (pureState preState)
      = .error err := by
  simp [processBuilderPendingPayments, htotal, liftErr, Except.mapError, MonadExcept.ofExcept]
  rfl

/-- Take an entry `i` in the previous-epoch half of the payment window. Entry `i` is
qualifying if and only if its weight reaches the quorum. The lemma unfolds the
proof-side filter `qualifyingPaymentIndices`, which `processBuilderPendingPayments_run`
uses to state the queued withdrawals. -/
theorem mem_qualifyingPaymentIndices_iff [Preset] (state : BeaconState) (total : Gwei)
    (i : Nat) (hi : i < slotsPerEpoch) :
    i ∈ qualifyingPaymentIndices state total ↔
      (vget state.builderPendingPayments i).weight ≥ builderPaymentQuorum total := by
  simp [qualifyingPaymentIndices, List.mem_filter, List.mem_range, hi]

/-- The withdrawal that `processExecutionPayloadBid` records for a bid with a nonzero
value (`Gloas/Operations.lean`, `process_execution_payload_bid`). -/
def bidWithdrawal [Preset] (bid : ExecutionPayloadBid) : BuilderPendingWithdrawal :=
  { feeRecipient := bid.feeRecipient, amount := bid.value, builderIndex := bid.builderIndex }

/-- The payment of `bid` reaches the epoch substep that judges it. At `state`, the entry
for the slot of the bid in the previous-epoch half of the payment window carries the
withdrawal of the bid. The entry got there through the block transitions between the bid
and the substep. `processExecutionPayloadBid` writes it in the current-epoch half, and the
epoch substep one epoch earlier moves it down. A slashing of the block's proposer clears
it (`slashValidator`), and a child block on the FULL edge settles it
(`settleBuilderPayment`). -/
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
`postState`, given the total active balance `total` of `preState`. It appends the
withdrawals of the entries at `qualifyingPaymentIndices preState total`, in slot order. The
entry of the bid is among them if and only if its weight reaches `builderPaymentQuorum
total`. At or above the quorum, the withdrawal of the bid is in the result. Below it, the
entry of the bid is not appended.

The claim concerns the entry of the bid. Below the quorum, an equal withdrawal value can
still be in the result, from the list before the substep or from another entry. -/
structure EpochPaysBidIffQuorum [Preset] [HasherTag] (preState postState : BeaconState)
    (total : Gwei) (bid : ExecutionPayloadBid) : Prop where
  /-- The substep appends the withdrawals of the entries at `qualifyingPaymentIndices
  preState total`, in slot order (`qualifyingBuilderWithdrawals`). -/
  appended : postState.builderPendingWithdrawals.val =
    preState.builderPendingWithdrawals.val ++
      (qualifyingBuilderWithdrawals preState total).toArray
  /-- The entry of the bid is qualifying if and only if its weight reaches the quorum. -/
  qualifying_iff : builderPaymentIndex bid.slot false ∈ qualifyingPaymentIndices preState total ↔
    bidPaymentWeight preState bid ≥ builderPaymentQuorum total
  /-- When the weight reaches the quorum, the withdrawal of the bid is queued. -/
  paid : bidPaymentWeight preState bid ≥ builderPaymentQuorum total →
    bidWithdrawal bid ∈ postState.builderPendingWithdrawals.val
  /-- When the weight is below the quorum, the slot of the bid is not among the entries
  whose withdrawals `appended` adds, so the entry of the bid is not appended. -/
  unpaid : bidPaymentWeight preState bid < builderPaymentQuorum total →
    builderPaymentIndex bid.slot false ∉ qualifyingPaymentIndices preState total

/-- The epoch substep appends the entry of the bid if and only if the entry reaches the
quorum. Take a `preState` where the payment of `bid` is carried (`BidPaymentCarried`), whose
total active balance is `total`, and whose quorum product fits (`QuorumFits`). Then
`processBuilderPendingPayments` succeeds, and `EpochPaysBidIffQuorum` holds. -/
theorem processBuilderPendingPayments_run_bid [Preset] [HasherTag] (preState : BeaconState)
    (bid : ExecutionPayloadBid) (hcarried : BidPaymentCarried preState bid)
    (total : Gwei) (htotal : getTotalActiveBalance (pureState preState) = .ok total)
    (hquorum : QuorumFits total) :
    ∃ postState : BeaconState,
      runPure (processBuilderPendingPayments (StateTransition := HezeRun)) preState
        = .ok ((), postState) ∧
      EpochPaysBidIffQuorum preState postState total bid := by
  refine ⟨_, processBuilderPendingPayments_run_appended preState total htotal hquorum, ?_⟩
  have hiff := mem_qualifyingPaymentIndices_iff preState total _
    (builderPaymentIndex_previous_lt bid.slot)
  refine ⟨rfl, hiff, fun hq => ?_, fun hlt hmem => ?_⟩
  · unfold BidPaymentCarried at hcarried
    show bidWithdrawal bid ∈ preState.builderPendingWithdrawals.val ++
      (qualifyingBuilderWithdrawals preState total).toArray
    rw [Array.mem_append]
    right
    unfold qualifyingBuilderWithdrawals
    rw [List.mem_toArray]
    exact List.mem_map.mpr ⟨_, hiff.mpr hq, hcarried⟩
  · -- Below the quorum, membership would give `weight ≥ quorum`, against `hlt`.
    exact absurd (hiff.mp hmem) (UInt64.not_le.mpr hlt)

end EthCLSpecs.Proofs.Heze
