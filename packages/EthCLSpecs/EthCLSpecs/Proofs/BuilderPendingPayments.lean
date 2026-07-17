import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Proofs.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:229-248`)
modifies two fields sequentially within one state transition. This file characterizes
those effects independently and combines them into one theorem about the function.
When invoked by the epoch substep, it feeds every qualifying previous-epoch payment's
withdrawal, in slot order, through the bounded `SSZList.push`; under an explicit
capacity hypothesis, every qualifying withdrawal is appended. It then shifts the
payment window down by `SLOTS_PER_EPOCH`, padding the vacated half with empties.

The withdrawals side rests on two pieces: a pure fact about `SSZList.push`'s clamp
(iterating it over a list of values ends at the original list plus the clamped prefix
that fits, unconditionally), and the loop's own reduction to that list, in iteration
order. No capacity-headroom invariant is assumed or proved here; the "every qualifying
withdrawal is appended" statement above is a corollary of the unconditional clamp fact
under an explicit `original.size + qualifying.length ≤ Const.builderPendingWithdrawalsLimit`
hypothesis, not an unconditional theorem.

The window side is a direct instance of `shiftWindow`'s general behavior:
`expectedPaymentWindow_get_lt` / `expectedPaymentWindow_get_upper` state the two
index-region facts (old upper half moves down; new upper half is empty).
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
`sszUpdate` call. Raw state equality is unnecessary here; each theorem records only
the relevant fields through `sszGet`.

-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLSpecs.Gloas
open EthCLSpecs.Fulu (Preset Gwei getTotalActiveBalance)
open EthCLSpecs.Fulu.Const (slotsPerEpoch builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator builderPendingWithdrawalsLimit)
-- Names from `EthCLLib.Spec`; `open scoped` activates the `appendState` macro.
open EthCLLib.Spec (SSZList HasherTag StateTransitionError vget shiftWindow)
open scoped EthCLLib.Spec

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
engages: every value in `vs` is appended, in order. -/
theorem sszListFoldlPush_val_of_fits {α : Type} {cap : Nat} (xs : SSZList α cap)
    (vs : List α) (hfits : xs.val.size + vs.length ≤ cap) :
    (vs.foldl (fun l w => l.push w) xs).val = xs.val ++ vs.toArray := by
  rw [sszListFoldlPush_val, List.take_of_length_le (by omega)]

/-- `do x` for a lone `for`-loop `x` elaborates as `x >>= fun _ => pure ()`, not as `x`
itself. Peels that wrapper so a fact about the ascribed loop connects to a use site
that runs the bare `forIn` before more code. -/
private theorem run_of_run_seq_pure {ε σ : Type} (x : EStateM ε σ PUnit) (s0 s1 : σ)
    (h : (x >>= fun _ => (pure () : EStateM ε σ Unit)).run s0 = .ok () s1) :
    x.run s0 = .ok PUnit.unit s1 := by
  rw [EStateM.run_bind] at h
  cases hx : x.run s0 with
  | ok a s =>
    rw [hx] at h
    cases a
    simpa only [EStateM.run_pure] using h
  | error e s => rw [hx] at h; simp at h

/-- The withdrawals loop's own reduction: the conditional `appendState` loop always
succeeds, and its observable effects reduce to a pure `SSZList.push` fold over the
qualifying indices (`sszListFoldlPush_val` characterizes the clamp).
`builderPendingPayments` is untouched. `cond` is a `Prop` with a `Decidable`
instance, matching the production `p.weight ≥ quorum` guard. Field agreement is
via `sszGet`. -/
private theorem builderPendingWithdrawalsLoop_run [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (state0 : State) :
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

/-- The postcondition `processBuilderPendingPayments_run` establishes: `after`'s two
touched fields equal `expectedWithdrawals` / `expectedPaymentWindow` of `before`. Named
so a later capacity-guarded corollary can restate the withdrawals half without
re-deriving the window half. -/
def ProcessBuilderPendingPaymentsPost [Preset] [HasherTag] (before after : State) : Prop :=
  sszGet after builderPendingWithdrawals = expectedWithdrawals before ∧
  sszGet after builderPendingPayments = expectedPaymentWindow before

/-- `processBuilderPendingPayments`'s two-field successful-run postcondition, for an
arbitrary input state: it always succeeds, and the result satisfies
`ProcessBuilderPendingPaymentsPost`. Combines `builderPendingWithdrawalsLoop_run`
(the withdrawals loop) with `shiftWindow`'s direct application (the payment-window
shift), the two effects the module docstring describes. -/
theorem processBuilderPendingPayments_run [Preset] [HasherTag] (before : State) :
    ∃ after : State,
      (processBuilderPendingPayments :
        EStateM StateTransitionError State Unit).run before = .ok () after ∧
      ProcessBuilderPendingPaymentsPost before after := by
  obtain ⟨resultState, hrun, hw, hp⟩ :=
    builderPendingWithdrawalsLoop_run slotsPerEpoch
      (fun i => (vget (sszGet before builderPendingPayments) i).weight ≥
        builderPaymentQuorum before)
      (fun i => (vget (sszGet before builderPendingPayments) i).withdrawal) before
  have hbare := run_of_run_seq_pure _ _ _ hrun
  simp only [builderPaymentQuorum] at hbare hw
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

/-- Capacity-guarded corollary of `processBuilderPendingPayments_run`: under an
explicit headroom hypothesis, every qualifying withdrawal is appended in slot order,
with no `SSZList.push` clamp. The payment-window half is unchanged from
`ProcessBuilderPendingPaymentsPost`. -/
theorem processBuilderPendingPayments_run_of_fits [Preset] [HasherTag]
    (before : State)
    (hfits : (sszGet before builderPendingWithdrawals).val.size +
      (qualifyingBuilderWithdrawals before).length ≤ builderPendingWithdrawalsLimit) :
    ∃ after : State,
      (processBuilderPendingPayments :
        EStateM StateTransitionError State Unit).run before = .ok () after ∧
      (sszGet after builderPendingWithdrawals).val =
        (sszGet before builderPendingWithdrawals).val ++
          (qualifyingBuilderWithdrawals before).toArray ∧
      sszGet after builderPendingPayments = expectedPaymentWindow before := by
  obtain ⟨after, hrun, hw, hp⟩ := processBuilderPendingPayments_run before
  refine ⟨after, hrun, ?_, hp⟩
  rw [hw]
  unfold expectedWithdrawals
  exact sszListFoldlPush_val_of_fits _ _ hfits

end EthCLSpecs.Proofs
