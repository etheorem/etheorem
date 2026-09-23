import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid`: Boolean characterization

`EthCLSpecs.Gloas.canBuilderCoverBid` is the check that `processExecutionPayloadBid` asserts
before it queues a `BuilderPendingPayment`. It returns an `Except`, because two of its steps
can fault as the pyspec's do: the pending-balance sums, and
`MIN_DEPOSIT_AMOUNT + pending_withdrawals_amount`.

The characterization takes the pending balance as a successful result, and the addition as
one that stays below `2 ^ 64`. It then gives the `Bool` exactly, in terms of the
`builderBalance` and `minBalance` values the function computes. Two more theorems give the two
faults. Indexing is total, so the theorems also hold for an out-of-range `builderIndex`. They
do not claim that the default value represents a registered builder.

The theorems:

* `canBuilderCoverBid_iff`: the exact characterization, `UInt64` throughout, with the guard and
  the subtraction spelled as the function computes them.
* `canBuilderCoverBid_iff_toNat_add_le`: the same result over `Nat`, so the guard reads as one
  addition that fits in the balance.
* `canBuilderCoverBid_pending_error` and `canBuilderCoverBid_min_overflow`: the two faults.

A private `le_sub_iff_toNat_add_le` carries the step from `UInt64` to `Nat` that the second
theorem needs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Bounds and termination
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedAdd throwArithmetic liftErr)
open EthCLSpecs.Gloas (BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)

/-- The descriptor of the `MIN_DEPOSIT_AMOUNT` addition. -/
abbrev minBalanceDescr : String :=
  "can_builder_cover_bid: MIN_DEPOSIT_AMOUNT + pending_withdrawals_amount"

/-- With a successful pending balance and a `MIN_DEPOSIT_AMOUNT` addition below `2 ^ 64`,
`canBuilderCoverBid` returns `true` exactly when its computed `minBalance` does not exceed the
builder's balance and the bid fits in the remainder. No claim is made that `builderIndex`
identifies a registered builder. -/
@[characterizes EthCLSpecs.Gloas.canBuilderCoverBid]
theorem canBuilderCoverBid_iff [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount pending : Gwei),
      (getPendingBalanceToWithdrawForBuilder state builderIndex
          : Except StateTransitionError Gwei) = .ok pending →
      Gloas.Const.minDepositAmountG.toNat + pending.toNat < 2 ^ 64 →
      ((canBuilderCoverBid state builderIndex bidAmount : Except StateTransitionError Bool)
          = .ok true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance := Gloas.Const.minDepositAmountG + pending
        minBalance ≤ builderBalance ∧ bidAmount ≤ builderBalance - minBalance) := by
  intro state builderIndex bidAmount pending hpend hmin
  have hc : ¬ Gloas.Const.minDepositAmountG + pending < Gloas.Const.minDepositAmountG := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hmin]
    omega
  -- Reduce the two binds first, while `hc` still matches the carry test's `UInt64` form.
  simp only [canBuilderCoverBid, hpend, GloasRun.except_bind_ok, checkedAdd, hc, ite_false]
  -- Both lemmas restate `UInt64`'s `<` / `≤` as `Nat` comparisons on `toNat`,
  -- which is what lets `simp` discharge the guard's `if` and pair the surviving
  -- branch conditions into the conjunction.
  simp [pure, Except.pure, GloasRun.except_bind_ok, UInt64.lt_iff_toNat_lt,
    UInt64.le_iff_toNat_le]

/-- **Pending-balance fault.** When the pending-balance sums fault, `canBuilderCoverBid` rejects
with the same fault. -/
theorem canBuilderCoverBid_pending_error [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei)
      (err : StateTransitionError),
      (getPendingBalanceToWithdrawForBuilder state builderIndex
          : Except StateTransitionError Gwei) = .error err →
      (canBuilderCoverBid state builderIndex bidAmount : Except StateTransitionError Bool)
        = .error err := by
  intro state builderIndex bidAmount err hpend
  simp [canBuilderCoverBid, hpend]
  rfl

/-- **Minimum-balance fault.** When `MIN_DEPOSIT_AMOUNT + pending` reaches `2 ^ 64`,
`canBuilderCoverBid` rejects with `.arithmetic`. The pyspec raises `ValueError` at the same
point. -/
theorem canBuilderCoverBid_min_overflow [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount pending : Gwei),
      (getPendingBalanceToWithdrawForBuilder state builderIndex
          : Except StateTransitionError Gwei) = .ok pending →
      2 ^ 64 ≤ Gloas.Const.minDepositAmountG.toNat + pending.toNat →
      (canBuilderCoverBid state builderIndex bidAmount : Except StateTransitionError Bool)
        = .error (.arithmetic minBalanceDescr) := by
  intro state builderIndex bidAmount pending hpend hmin
  have hc : Gloas.Const.minDepositAmountG + pending < Gloas.Const.minDepositAmountG := by
    have := UInt64.toNat_lt pending
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  simp only [canBuilderCoverBid, hpend, GloasRun.except_bind_ok, checkedAdd, hc, ite_true]
  rfl

/-- The arithmetic bridge behind the `Nat` restatement below: under `b ≤ a`, the
truncating difference `a - b` bounds `c` exactly when `b + c` fits in `a` over
`Nat`. Stated on bare `UInt64`s, so the spec-level theorem can apply it without
respelling the balance expressions to generalize them first. -/
private theorem le_sub_iff_toNat_add_le {a b c : UInt64} (h : b ≤ a) :
    c ≤ a - b ↔ b.toNat + c.toNat ≤ a.toNat := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h]
  have := UInt64.le_iff_toNat_le.mp h
  omega

/-- The same characterization over `Nat`: `canBuilderCoverBid` accepts exactly when the
computed `minBalance` plus the bid fits within the builder's balance. The addition in this
conclusion cannot wrap. -/
theorem canBuilderCoverBid_iff_toNat_add_le [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount pending : Gwei),
      (getPendingBalanceToWithdrawForBuilder state builderIndex
          : Except StateTransitionError Gwei) = .ok pending →
      Gloas.Const.minDepositAmountG.toNat + pending.toNat < 2 ^ 64 →
      ((canBuilderCoverBid state builderIndex bidAmount : Except StateTransitionError Bool)
          = .ok true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance := Gloas.Const.minDepositAmountG + pending
        minBalance.toNat + bidAmount.toNat ≤ builderBalance.toNat) := by
  intro state builderIndex bidAmount pending hpend hmin
  rw [canBuilderCoverBid_iff state builderIndex bidAmount pending hpend hmin]
  dsimp only
  constructor
  · rintro ⟨h_min, h_bid⟩
    exact (le_sub_iff_toNat_add_le h_min).mp h_bid
  · intro h
    -- `Nat.le_add_right` drops the bid to recover the `minBalance ≤ builderBalance`
    -- half; both operands are inferred from `h`, so neither is respelled here.
    have h_min := UInt64.le_iff_toNat_le.mpr (Nat.le_trans (Nat.le_add_right _ _) h)
    exact ⟨h_min, (le_sub_iff_toNat_add_le h_min).mpr h⟩

end EthCLSpecs.Proofs.Gloas
