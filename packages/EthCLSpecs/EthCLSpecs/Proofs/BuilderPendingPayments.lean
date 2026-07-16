import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Proofs.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:229-248`)
has two effects, independently characterizable even though they run sequentially within
one state transition. When invoked by the epoch substep, it feeds every qualifying
previous-epoch payment's withdrawal, in slot order, through the bounded `SSZList.push`;
under an explicit capacity hypothesis, every qualifying withdrawal is appended. It then
shifts the payment window down by `SLOTS_PER_EPOCH`, padding the vacated half with
empties. This file proves both and combines them into one theorem about the function
itself.

The withdrawals side rests on two pieces: a pure fact about `SSZList.push`'s clamp
(iterating it over a list of values ends at the original list plus the clamped prefix
that fits, unconditionally), and the loop's own reduction to that list, in iteration
order. `Const.builderPendingWithdrawalsLimit` (`2 ^ 20`) has no proven or asserted bound
anywhere in the codebase, nothing here derives capacity headroom; the "every qualifying
withdrawal is appended" statement above is a corollary of the unconditional clamp fact
under an explicit `original.size + qualifying.length ≤ Const.builderPendingWithdrawalsLimit`
hypothesis, not an unconditional theorem.

The window side is a direct instance of `shiftWindow`'s general behavior:
`processBuilderPendingPayments` reads `builderPendingPayments` once, before the
withdrawals loop runs, and the loop never writes that field, so the window
transformation's input is unaffected by whatever the withdrawals loop did.

This file proves only the local before/after behavior of one call, for an arbitrary
input state. It does not prove protocol-wide exactly-once settlement, and says nothing
about how this substep's effect interacts with `settleBuilderPayment` or
`processProposerSlashing`, the other paths that clear a `BuilderPendingPayment` before
this substep ever runs.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Safety and invariant preservation".

Every theorem below states its state-level conclusions through `sszGet`, never through
bare `State` equality: `State`'s cache overlay accumulates one pending write per
`sszUpdate` call, and raw state equality is unnecessary here, each theorem records only
the specific fields it proves something about, through `sszGet`.

-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (SSZList)

/-- Folding `SSZList.push` over a list of values lands on the original array
plus however much of the values list fits under `cap`: once the list is at
capacity, `SSZList.push`'s own `if` makes every further push a no-op, so only
the first `cap - xs.val.size` values appear in the result, in order. No
additional capacity hypothesis is required. -/
theorem sszListFoldlPush_val {α : Type} {cap : Nat} (xs : SSZList α cap) (vs : List α) :
    (vs.foldl (fun l w => l.push w) xs).val =
      xs.val ++ (vs.take (cap - xs.val.size)).toArray := by
  induction vs generalizing xs with
  | nil => simp
  | cons v rest ih =>
    rw [List.foldl_cons, ih]
    by_cases h : xs.val.size < cap
    · have hpush : (xs.push v).val = xs.val.push v := by
        unfold SSZList.push
        rw [dif_pos h]
      rw [hpush, Array.size_push]
      have htake : cap - xs.val.size = cap - (xs.val.size + 1) + 1 := by omega
      rw [htake, List.take_succ_cons, List.toArray_cons, Array.push_eq_append,
        Array.append_assoc]
    · have hpush : (xs.push v).val = xs.val := by
        unfold SSZList.push
        rw [dif_neg h]
      have hcap : cap - xs.val.size = 0 := by omega
      rw [hpush, hcap]
      simp

/-- Under an explicit capacity hypothesis, `sszListFoldlPush_val`'s clamp never
engages: every value in `vs` is appended, in order. `Subtype.ext` promotes this
from `.val` to the full `SSZList` equality only where a caller needs it. -/
theorem sszListFoldlPush_val_of_fits {α : Type} {cap : Nat} (xs : SSZList α cap)
    (vs : List α) (hfits : xs.val.size + vs.length ≤ cap) :
    (vs.foldl (fun l w => l.push w) xs).val = xs.val ++ vs.toArray := by
  rw [sszListFoldlPush_val, List.take_of_length_le (by omega)]

open EthCLSpecs.Gloas
open EthCLSpecs.Fulu (Preset Gwei getTotalActiveBalance)
open EthCLSpecs.Fulu.Const (slotsPerEpoch builderPaymentThresholdNumerator builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
open EthCLLib.Spec

/-- `do x` for a lone `for`-loop `x` elaborates as `x >>= fun _ => pure ()`, not as `x`
itself: a `do`-block's last statement always gets an appended `pure`, even when that
statement already has the block's own return type. `x`'s own accumulator type is `PUnit`
(a `for`-loop's natural result), one universe below the ascribed `do`-block's `Unit`; the
appended `pure ()` is what bridges the two. This peels the wrapper back off, so a fact
about `do x`'s run (as produced by ascribing a lone `for`-loop to its monad) can connect
to a use site that runs `x` directly, immediately followed by more code instead of an
implicit `pure`. -/
theorem run_of_run_seq_pure {ε σ : Type} (x : EStateM ε σ PUnit) (s0 s1 : σ)
    (h : (x >>= fun _ => (pure () : EStateM ε σ Unit)).run s0 = .ok () s1) :
    x.run s0 = .ok PUnit.unit s1 := by
  rw [EStateM.run_bind] at h
  cases hx : x.run s0 with
  | ok a s =>
    rw [hx] at h
    cases a
    simpa only [EStateM.run_pure] using h
  | error e s => rw [hx] at h; simp at h

/-- The withdrawals loop's own reduction: running `for i in [0:n] do if cond i then
appendState builderPendingWithdrawals (val i)` from `state0` always succeeds (the loop
body has no error path), and its two observable effects reduce to pure list operations.
`builderPendingWithdrawals` picks up `val i` for every `i < n` with `cond i`, in order,
through the exact `SSZList.push` fold; `sszListFoldlPush_val` characterizes its clamping
behavior. `builderPendingPayments` is untouched, since the loop body never writes it.
`cond` is a `Prop` with a `Decidable` instance, not a `Bool`, matching how the production
loop's `p.weight ≥ quorum` guard actually elaborates (`UInt64`'s `≥` is `Prop`-valued).
Raw state equality is unnecessary: the theorem records the relevant fields through
`sszGet`, not through `=` on `State` itself, whose cache overlay
(`SizzLean.Cache.TreeBacked.pending`) does not guarantee that iterating a same-field
write is syntactically identical to one combined write. -/
theorem forLoopAppendIf_run [Preset] [HasherTag] (n : Nat) (cond : Nat → Prop)
    [DecidablePred cond] (val : Nat → BuilderPendingWithdrawal) (state0 : State) :
    ∃ resultState : State,
      (do for i in [0:n] do
            if cond i then
              appendState builderPendingWithdrawals (val i)
          : EStateM StateTransitionError State Unit).run state0 = .ok () resultState ∧
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
    · have hstep : (appendState builderPendingWithdrawals (val i) :
          EStateM StateTransitionError State Unit).run state0 =
          .ok () (sszUpdate state0 with
            builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i)) := by
        cases state0 <;> rfl
      obtain ⟨resultState, hrun, hw, hp⟩ := ih (sszUpdate state0 with
        builderPendingWithdrawals := (sszGet state0 builderPendingWithdrawals).push (val i))
      refine ⟨resultState, ?_, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [h, if_pos, EStateM.run_bind, hstep]
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
        simp only [h, EStateM.run_bind, EStateM.run_pure]
        exact hrun
      · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest)) =
            List.filter (fun i => decide (cond i)) rest := by
          rw [List.filter_cons_of_neg]; simpa using h
        rw [hw, hfilter]
      · exact hp

/-- `processBuilderPendingPayments`'s quorum threshold, factored out for reuse between
`qualifyingBuilderWithdrawals`, `expectedWithdrawals`, and their theorems. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : State) : Gwei :=
  (getTotalActiveBalance state / UInt64.ofNat slotsPerEpoch) *
    builderPaymentThresholdNumerator / builderPaymentThresholdDenominator

/-- The previous-epoch payments whose weight clears `builderPaymentQuorum`, mapped to
their withdrawals, in slot order, before `SSZList.push`'s capacity clamp. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : State) :
    List BuilderPendingWithdrawal :=
  let payments := sszGet state builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ builderPaymentQuorum state)).map
    fun i => (vget payments i).withdrawal

/-- The `builderPendingWithdrawals` value `processBuilderPendingPayments` produces:
`qualifyingBuilderWithdrawals`, folded through `SSZList.push` from the field's current
value. `sszListFoldlPush_val` and `sszListFoldlPush_val_of_fits` characterize this
fold's clamping behavior. -/
def expectedWithdrawals [Preset] [HasherTag] (state : State) :
    SSZList BuilderPendingWithdrawal builderPendingWithdrawalsLimit :=
  (qualifyingBuilderWithdrawals state).foldl (fun l w => l.push w)
    (sszGet state builderPendingWithdrawals)

/-- The `builderPendingPayments` value `processBuilderPendingPayments` produces: the
field's current value shifted down by `SLOTS_PER_EPOCH` and padded with empties. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : State) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- The postcondition `processBuilderPendingPayments_run` establishes: `after`'s two
touched fields equal `expectedWithdrawals` / `expectedPaymentWindow` of `before`. Named
so a later capacity-guarded corollary can restate the withdrawals half without
re-deriving the window half. -/
def ProcessBuilderPendingPaymentsPost [Preset] [HasherTag] (before after : State) : Prop :=
  sszGet after builderPendingWithdrawals = expectedWithdrawals before ∧
  sszGet after builderPendingPayments = expectedPaymentWindow before

/-- `processBuilderPendingPayments`'s complete successful-run postcondition, for an
arbitrary input state: it always succeeds, and the result satisfies
`ProcessBuilderPendingPaymentsPost`. Combines `forLoopAppendIf_run` (the withdrawals
loop) with `shiftWindow`'s direct application (the payment-window shift), the two
effects the module docstring describes. -/
theorem processBuilderPendingPayments_run [Preset] [HasherTag] (before : State) :
    ∃ after : State,
      (processBuilderPendingPayments :
        EStateM StateTransitionError State Unit).run before = .ok () after ∧
      ProcessBuilderPendingPaymentsPost before after := by
  obtain ⟨resultState, hrun, hw, hp⟩ :=
    forLoopAppendIf_run slotsPerEpoch
      (fun i => (vget (sszGet before builderPendingPayments) i).weight ≥
        builderPaymentQuorum before)
      (fun i => (vget (sszGet before builderPendingPayments) i).withdrawal) before
  have hbare := run_of_run_seq_pure _ _ _ hrun
  simp only [builderPaymentQuorum] at hbare hw
  refine ⟨(sszUpdate resultState with builderPendingPayments :=
      shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
        (fun _ => (default : BuilderPendingPayment))), ?_, ?_, ?_⟩
  · -- `show`, not `unfold`: `unfold` would leave the goal holding
    -- `processBuilderPendingPayments`'s own compiled term, whose `sszUpdate` case-split
    -- is a different (if computationally identical) declaration than the one `hbare`'s
    -- `appendState` elaborates to in *this* file. Retyping the source here elaborates
    -- that case-split fresh, in this file, where it lines up with `hbare`'s for the
    -- `simp [hbare]` below; `show`'s defeq check doesn't care which spelling it's given.
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
        : EStateM StateTransitionError State Unit).run before =
        .ok () (sszUpdate resultState with builderPendingPayments :=
          shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment)))
    simp only [EStateM.run_bind, builderPaymentQuorum, hbare]
    cases resultState <;> rfl
  · have hgetW : sszGet (sszUpdate resultState with builderPendingPayments :=
        shiftWindow (sszGet resultState builderPendingPayments) slotsPerEpoch slotsPerEpoch
          (fun _ => (default : BuilderPendingPayment))) builderPendingWithdrawals =
        sszGet resultState builderPendingWithdrawals := by
      cases resultState <;> rfl
    rw [hgetW, hw]
    unfold expectedWithdrawals qualifyingBuilderWithdrawals builderPaymentQuorum
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

end EthCLSpecs.Proofs
