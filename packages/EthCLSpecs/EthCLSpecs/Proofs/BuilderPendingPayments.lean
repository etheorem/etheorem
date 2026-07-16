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

TODO: state and prove `processBuilderPendingPayments_run_eq` and its
capacity-guarded corollary.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (SSZList)

/-- Folding `SSZList.push` over a list of values lands on the original array
plus however much of the values list fits under `cap`: once the list is at
capacity, `SSZList.push`'s own `if` makes every further push a no-op, so only
the first `cap - xs.val.size` values are ever appended, in order. Unconditional,
no capacity hypothesis; this is what the clamp *means*. -/
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

end EthCLSpecs.Proofs
