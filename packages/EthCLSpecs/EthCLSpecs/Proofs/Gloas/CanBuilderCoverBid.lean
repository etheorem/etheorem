import EthCLSpecs.Gloas.Operations
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid`: Boolean characterization

`EthCLSpecs.Gloas.canBuilderCoverBid` is the funding gate `processExecutionPayloadBid`
asserts before queuing a `BuilderPendingPayment`. At the migrated `Gwei` surface the
pending-balance sum, the reserve add, and the cover subtraction are the checked `Gwei`
chain, so the predicate returns a `Checked Bool`: a fault on any step rejects the bid
exactly where the pyspec raises.

These are the literal `Gwei` values; the theorem does not assert that accumulation
of pending obligations is overflow-free. Indexing is total, so the theorem also
holds for out-of-range `builderIndex` values, without claiming that the resulting
default value represents a registered builder.

Statements bind plain `BeaconState` values; the state readers and the spec
functions receive `pureState state`, and the reads spell `state.builders[i]!`.

Three theorems (task 4.2 restates the second and third through the checked-chain
laws; these repairs keep the tree building and the tags in place):

* `canBuilderCoverBid_eq`: the exact run equation, the body itself.
* `canBuilderCoverBid_ok_iff`: under the three `Checked` steps' success hypotheses,
  `true` is exactly the guard passing and the bid fitting the remainder.
* `canBuilderCoverBid_ok_toNat_add_le`: the `Nat` reading of the same contract, the
  addition-fits-in-balance form.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag Checked)
open EthCLSpecs.Gloas (BeaconState BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)
open EthCLLib.Proofs (pureState)

/-- **Exact run equation.** The pending sum, the reserve add, and the cover
subtraction bind in order; the guard then picks a branch, and the else branch
forms the checked subtraction. This is the body itself, so `rfl` states it. -/
@[characterizes EthCLSpecs.Gloas.canBuilderCoverBid]
theorem canBuilderCoverBid_eq [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid (pureState state) builderIndex bidAmount
        = (do
            let builderBalance := state.builders[builderIndex.toNat]!.balance
            let pending ← getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex
            let minBalance ← Gloas.Const.minDepositAmountG + pending
            if builderBalance < minBalance then pure false
            else
              let cover ← builderBalance - minBalance
              pure (cover ≥ bidAmount)) :=
  fun _ _ _ => rfl

/-- Under the three checked steps' success hypotheses, `canBuilderCoverBid`
answers `true` exactly when the computed `minBalance` does not exceed the
builder's balance and the bid fits in the remainder. No claim is made that
pending-obligation accumulation is overflow-free or that `builderIndex`
identifies a registered builder. -/
theorem canBuilderCoverBid_ok_iff [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount pending minBalance cover : Gwei),
      getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending →
      ((Gloas.Const.minDepositAmountG + pending : Checked Gwei)) = .ok minBalance →
      ((state.builders[builderIndex.toNat]!.balance - minBalance : Checked Gwei)) = .ok cover →
      (canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true ↔
        minBalance ≤ state.builders[builderIndex.toNat]!.balance ∧ bidAmount ≤ cover) := by
  intro state builderIndex bidAmount pending minBalance cover hpend hmin hsub
  rw [canBuilderCoverBid_eq, hpend]
  -- `zeta` reduces the body's leading `let` and the successful read bind, putting
  -- the two remaining checked steps where the hypotheses name them.
  show ((do
      let minBalance ← Gloas.Const.minDepositAmountG + pending
      if state.builders[builderIndex.toNat]!.balance < minBalance then pure false
      else
        let cover ← state.builders[builderIndex.toNat]!.balance - minBalance
        pure (cover ≥ bidAmount)) : Checked Bool) = .ok true ↔
    (minBalance ≤ state.builders[builderIndex.toNat]!.balance ∧ bidAmount ≤ cover)
  rw [hmin]
  -- The successful add reduces away, putting the guard and the cover subtraction
  -- on the hypothesis-named values.
  show (((if state.builders[builderIndex.toNat]!.balance < minBalance then Except.ok false
        else
          (do
            let cover ← state.builders[builderIndex.toNat]!.balance - minBalance
            pure (cover ≥ bidAmount)) : Checked Bool)) = .ok true) ↔
    (minBalance ≤ state.builders[builderIndex.toNat]!.balance ∧ bidAmount ≤ cover)
  rw [hsub]
  split
  · next hlt =>
    have hnat : ¬ (minBalance.val.toNat ≤ state.builders[builderIndex.toNat]!.balance.val.toNat) := by
      have hv : state.builders[builderIndex.toNat]!.balance.val < minBalance.val := hlt
      have h1 : state.builders[builderIndex.toNat]!.balance.val.toNat < minBalance.val.toNat :=
        UInt64.lt_iff_toNat_lt.mp hv
      omega
    simp only [Except.ok.injEq, Bool.false_eq_true, false_iff, not_and]
    exact fun hle _ => absurd (UInt64.le_iff_toNat_le.mp hle) hnat
  · next hguard =>
    have hge : minBalance ≤ state.builders[builderIndex.toNat]!.balance := by
      show minBalance.val ≤ state.builders[builderIndex.toNat]!.balance.val
      rw [UInt64.le_iff_toNat_le]
      have hn : ¬ (state.builders[builderIndex.toNat]!.balance.val.toNat < minBalance.val.toNat) :=
        fun hltv => hguard (UInt64.lt_iff_toNat_lt.mpr hltv)
      omega
    constructor
    · intro htrue
      exact ⟨hge, decide_eq_true_iff.mp (Except.ok.inj htrue)⟩
    · intro ⟨_, hfit⟩
      show (Except.ok (decide (bidAmount ≤ cover)) : Checked Bool) = .ok true
      rw [decide_eq_true hfit]

/-- Equivalent `Nat`-level characterization: under the checked steps' success
hypotheses, `canBuilderCoverBid` accepts exactly when the computed `minBalance`
plus the bid fits within the builder's balance. The addition in this conclusion
cannot wrap. -/
theorem canBuilderCoverBid_ok_toNat_add_le [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount pending minBalance cover : Gwei),
      getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending →
      ((Gloas.Const.minDepositAmountG + pending : Checked Gwei)) = .ok minBalance →
      ((state.builders[builderIndex.toNat]!.balance - minBalance : Checked Gwei)) = .ok cover →
      (canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true →
        minBalance.toPlainNat + bidAmount.toPlainNat
          ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat) := by
  intro state builderIndex bidAmount pending minBalance cover hpend hmin hsub hok
  have ⟨h_le, h_fit⟩ := (canBuilderCoverBid_ok_iff state builderIndex bidAmount pending minBalance cover
    hpend hmin hsub).mp hok
  -- The cover value reads back as the plain difference (`sub_value`), and the
  -- guard's `≤` is the native one, so the `Nat` facts close by arithmetic.
  have hcoverNat := EthCLLib.Proofs.sub_value state.builders[builderIndex.toNat]!.balance minBalance cover hsub
  have hle : minBalance.val.toNat ≤ state.builders[builderIndex.toNat]!.balance.val.toNat :=
    UInt64.le_iff_toNat_le.mp h_le
  have hfit : bidAmount.val.toNat ≤ cover.val.toNat := UInt64.le_iff_toNat_le.mp h_fit
  have hcov : cover.val.toNat = state.builders[builderIndex.toNat]!.balance.val.toNat
      - minBalance.val.toNat := by
    have hc := EthCLLib.Proofs.sub_value state.builders[builderIndex.toNat]!.balance minBalance cover hsub
    exact hc
  have t1 : minBalance.toPlainNat = minBalance.val.toNat := rfl
  have t2 : state.builders[builderIndex.toNat]!.balance.toPlainNat
      = state.builders[builderIndex.toNat]!.balance.val.toNat := rfl
  have t3 : bidAmount.toPlainNat = bidAmount.val.toNat := rfl
  have t4 : cover.toPlainNat = cover.val.toNat := rfl
  omega

end EthCLSpecs.Proofs.Gloas
