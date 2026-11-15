import EthCLSpecs.Gloas.Operations
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.CLUint
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid`: exact `Checked` characterization

`EthCLSpecs.Gloas.canBuilderCoverBid` is the `Checked Bool` predicate
`can_builder_cover_bid` uses before queuing a `BuilderPendingPayment`. The
pyspec computes `min_balance = MIN_DEPOSIT_AMOUNT + pending_withdrawals_amount`
with the checked `Gwei` add before it compares, so the helper raises where that
add raises; the final subtraction sits in the guarded else branch, so it never
raises when the helper returns. This file characterizes the `.ok true` result
exactly: the pending sum binds, the checked add binds, the guarded subtraction
binds, and the difference covers the bid.

The pending sum `getPendingBalanceToWithdrawForBuilder` is a fold of checked
adds over `builderPendingWithdrawals` and `builderPendingPayments`, so it can
fault on overflow; both theorems state its `.ok` equation as a hypothesis and
say nothing about its internal fold.

These are literal `Gwei` values. The theorems do not assert that accumulation
of pending obligations is overflow-free. Indexing is total, so the theorems
also hold for out-of-range `builderIndex` values, without claiming that the
resulting default value represents a registered builder.

Statements bind plain `BeaconState` values; the spec functions receive
`pureState state`, and the reads spell `state.builders[i]!`.

Three steps, in the order the proofs chain them:

* `canBuilderCoverBid_eq`: the run equation. It rewrites the helper into
  `coverBidResult`, the bind chain over an abstract balance and an abstract
  pending step, with the balance read spelled as the plain
  `state.builders[i]!` field.
* `coverBidResult_eq_ok_true_iff`: the abstract iff. It dispatches on the
  `Checked` sum and names the three `.ok` equations and the comparison the
  `.ok true` result commits to.
* `canBuilderCoverBid_iff`: the exact implementation-level characterization,
  `Gwei` throughout, each `Checked` step spelled as the `.ok` equation the body
  binds. It carries the `@[characterizes]` tag.

* `canBuilderCoverBid_iff_toPlainInt_add_le`: a semantic characterization
  relative to that same computed `minBalance`, restated over `Nat` so the guard
  reads as a single addition-fits-in-balance fact rather than a subtraction.
  The `.toPlainInt` reads are the pyspec's `int(x)`, the plain-`int` view the
  checked operators' own success and value lemmas are stated over.

A private `le_diff_iff_toPlainInt_add_le` carries the `Gwei`-to-`Nat` step the
second theorem needs, keeping the spec-level statements free of the arithmetic
detour.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Bounds and termination
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag Checked ArithFault)
open EthCLSpecs.Gloas (BeaconState BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)
open EthCLLib.Proofs (pureState sub_eq_ok)
open SizzLean.Proofs (view_uncachedBox)

/-- A bind on `.ok` is the continuation. `EthCLLib.Proofs.Run` already names
this fact as `except_bind_ok`, but in the `>>=` (`Bind.bind`) spelling, and
`simp only` does not fire it on the `Except.bind` terms the fork body's `do`
block desugars to. The proof rewrites the `.bind` spelling, so it carries the
`.bind`-shaped copy of the two one-line facts. -/
private theorem bind_ok {α β : Type} (v : α) (k : α → Checked β) :
    (Except.ok v : Checked α).bind k = k v := rfl

/-- A bind on `.error` stays the error. Companion of `bind_ok`. -/
private theorem bind_error {α β : Type} (e : ArithFault) (k : α → Checked β) :
    (Except.error e : Checked α).bind k = .error e := rfl

/-- The body of `canBuilderCoverBid` with the balance read and the pending step
abstracted. The `if` and the two checked operators are exactly the ones the
fork body writes; the run equation below instantiates the abstraction, and the
iff below analyzes it once, over plain variables. -/
private def coverBidResult [Preset] (balance : Gwei) (pendingStep : Checked Gwei)
    (bidAmount : Gwei) : Checked Bool :=
  pendingStep.bind fun pending =>
    (EthCLSpecs.Gloas.Const.minDepositAmountG + pending).bind fun minBalance =>
      if balance < minBalance then .ok false
      else (balance - minBalance).bind fun diff => .ok (decide (diff ≥ bidAmount))

/-- **Run equation.** The helper is its bind chain with the balance read spelled
as the plain `state.builders[i]!` field: `view_uncachedBox` reduces the read on
the pure box to the field, and the two terms are then the same term. -/
private theorem canBuilderCoverBid_eq [Preset] [HasherTag]
    (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    canBuilderCoverBid (pureState state) builderIndex bidAmount =
      coverBidResult (state.builders[builderIndex.toNat]!.balance)
        (getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex) bidAmount := by
  unfold canBuilderCoverBid coverBidResult
  simp only [view_uncachedBox]
  rfl

/-- The abstract contract: `coverBidResult` returns `.ok true` exactly when the
pending step binds, the checked `minBalance` add binds, the guarded subtraction
binds, and the difference covers the bid. The `.ok` equation on the subtraction
carries the guard: `sub` succeeds exactly when `minBalance ≤ balance`, which is
the else branch the body subtracts in. -/
private theorem coverBidResult_eq_ok_true_iff [Preset] (balance bidAmount : Gwei)
    (pendingStep : Checked Gwei) :
    coverBidResult balance pendingStep bidAmount = .ok true ↔
      ∃ pending minBalance diff : Gwei,
        pendingStep = .ok pending ∧
        (EthCLSpecs.Gloas.Const.minDepositAmountG + pending : Checked Gwei) = .ok minBalance ∧
        (balance - minBalance : Checked Gwei) = .ok diff ∧
        bidAmount ≤ diff := by
  unfold coverBidResult
  constructor
  · intro h
    -- Peel the three binds by cases on each `Checked` step; `bind_ok` /
    -- `bind_error` substitute the branch, and the surviving arms name the witnesses.
    cases hp : pendingStep with
    | error e => rw [hp] at h; simp only [bind_error] at h; exact absurd h (by simp)
    | ok pending =>
      rw [hp] at h
      simp only [bind_ok] at h
      cases hm : (EthCLSpecs.Gloas.Const.minDepositAmountG + pending : Checked Gwei) with
      | error e => rw [hm] at h; simp only [bind_error] at h; exact absurd h (by simp)
      | ok minBalance =>
        rw [hm] at h
        simp only [bind_ok] at h
        split at h
        · -- The guard took the `.ok false` branch, so the result cannot be `.ok true`.
          exact absurd h (by simp)
        · cases hs : (balance - minBalance : Checked Gwei) with
          | error e => rw [hs] at h; simp only [bind_error] at h; exact absurd h (by simp)
          | ok diff =>
            rw [hs] at h
            simp only [bind_ok, Except.ok.injEq] at h
            exact ⟨pending, minBalance, diff, rfl, hm, hs, of_decide_eq_true h⟩
  · rintro ⟨pending, minBalance, diff, hp, hm, hs, hge⟩
    rw [hp]
    simp only [bind_ok]
    rw [hm]
    simp only [bind_ok]
    -- The guard's `balance < minBalance` is the negation of `sub`'s own success
    -- condition, so the `.ok diff` equation pins it to the else branch.
    have hle : minBalance.toPlainInt ≤ balance.toPlainInt := (sub_eq_ok _ _ diff).mp hs |>.1
    split
    · rename_i hguard
      exfalso
      have hnat : balance.val.toNat < minBalance.val.toNat :=
        UInt64.lt_iff_toNat_lt.mp hguard
      have hle' : minBalance.val.toNat ≤ balance.val.toNat := hle
      omega
    · rw [hs]
      simp only [bind_ok]
      exact congrArg Except.ok (decide_eq_true hge)

/-- `canBuilderCoverBid` returns `.ok true` exactly when its three `Checked`
steps bind, the pending sum, the checked `minBalance` add, and the guarded
subtraction, and the difference covers the bid. The `.ok` equation on the
subtraction carries the guard: `sub` succeeds exactly when
`minBalance ≤ builderBalance`, which is the else branch the body subtracts in.
These are the literal `Gwei` values computed by the implementation; no claim is
made that pending-obligation accumulation is overflow-free or that
`builderIndex` identifies a registered builder. -/
@[characterizes EthCLSpecs.Gloas.canBuilderCoverBid]
theorem canBuilderCoverBid_iff [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true ↔
        ∃ pending minBalance diff : Gwei,
          getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending ∧
          (Gloas.Const.minDepositAmountG + pending : Checked Gwei) = .ok minBalance ∧
          (state.builders[builderIndex.toNat]!.balance - minBalance : Checked Gwei) = .ok diff ∧
          bidAmount ≤ diff := fun _ _ _ => by
  rw [canBuilderCoverBid_eq, coverBidResult_eq_ok_true_iff]

/-- The arithmetic bridge behind the `Nat` restatement below: under the guarded
subtraction's `.ok` equation, `a` is the builder's balance, `b` the computed
`minBalance`, and the difference `diff` bounds `c` (the bid) exactly when
`minBalance + c` fits in the balance over `Nat`. The `.toPlainInt` reads are
the pyspec's `int(x)`, the plain-`int` view the checked operators' success and
value lemmas state their conditions over, so this bridge is the one conversion
the comparison needs. Stated on bare `Gwei`s, so the spec-level theorem can
apply it without respelling the balance expressions to generalize them first. -/
private theorem le_diff_iff_toPlainInt_add_le {a b diff c : Gwei}
    (hok : (a - b : Checked Gwei) = .ok diff) :
    c ≤ diff ↔ b.toPlainInt + c.toPlainInt ≤ a.toPlainInt := by
  obtain ⟨hle, hval⟩ := sub_eq_ok a b diff |>.mp hok
  -- The lemma's facts live in the `toPlainInt` spelling, the comparison's in the
  -- `val.toNat` one; both spellings of each atom go into `omega`.
  have hleNat : b.val.toNat ≤ a.val.toNat := hle
  have hvalNat : diff.val.toNat = a.val.toNat - b.val.toNat := hval
  have hlePlain : b.toPlainInt ≤ a.toPlainInt := hle
  have hvalPlain : diff.toPlainInt = a.toPlainInt - b.toPlainInt := hval
  constructor
  · intro h
    have hc : c.toPlainInt ≤ diff.toPlainInt := UInt64.le_iff_toNat_le.mp h
    omega
  · intro h
    have hc : b.val.toNat + c.val.toNat ≤ a.val.toNat := h
    exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- Equivalent `Nat`-level characterization: `canBuilderCoverBid` accepts
exactly when the computed `minBalance` plus the bid fits within the builder's
balance. The addition in this conclusion cannot wrap; `minBalance` itself
remains the literal `Gwei` value produced by the implementation. The
`.toPlainInt` reads are the pyspec's `int(x)`, the plain-`int` view the checked
operators' lemmas are stated over. -/
theorem canBuilderCoverBid_iff_toPlainInt_add_le [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true ↔
        ∃ pending minBalance : Gwei,
          getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending ∧
          (Gloas.Const.minDepositAmountG + pending : Checked Gwei) = .ok minBalance ∧
          minBalance.toPlainInt + bidAmount.toPlainInt ≤
            state.builders[builderIndex.toNat]!.balance.toPlainInt := by
  intro state builderIndex bidAmount
  rw [canBuilderCoverBid_iff]
  constructor
  · rintro ⟨pending, minBalance, diff, hp, hm, hs, hge⟩
    exact ⟨pending, minBalance, hp, hm, (le_diff_iff_toPlainInt_add_le hs).mp hge⟩
  · rintro ⟨pending, minBalance, hp, hm, hle⟩
    -- The fit hypothesis rebuilds the guarded subtraction's witness: `sub` succeeds
    -- under `minBalance ≤ balance`, and the witness reads back as the truncating
    -- difference, which is the value the bridge compares against.
    have hmb : minBalance.toPlainInt
        ≤ state.builders[builderIndex.toNat]!.balance.toPlainInt :=
      Nat.le_trans (Nat.le_add_right _ _) hle
    have hsub : (state.builders[builderIndex.toNat]!.balance - minBalance : Checked Gwei)
        = .ok (EthCLLib.Spec.CLUint64.trustedOfUInt64
          (state.builders[builderIndex.toNat]!.balance.val - minBalance.val)) := by
      rw [sub_eq_ok]
      refine ⟨hmb, ?_⟩
      show (state.builders[builderIndex.toNat]!.balance.val - minBalance.val).toNat
        = state.builders[builderIndex.toNat]!.balance.toPlainInt - minBalance.toPlainInt
      exact UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hmb)
    exact ⟨pending, minBalance, _, hp, hm, hsub, (le_diff_iff_toPlainInt_add_le hsub).mpr hle⟩

end EthCLSpecs.Proofs.Gloas
