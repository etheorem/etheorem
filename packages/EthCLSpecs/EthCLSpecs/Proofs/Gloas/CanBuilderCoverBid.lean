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

Three theorems:

* `canBuilderCoverBid_eq`: the exact run equation, the body itself.
* `canBuilderCoverBid_ok_iff`: under the read's success and the two range facts the checked
  steps pose (`add_ok_iff`'s and `sub_ok_iff`'s success conditions on the plain values),
  `true` is exactly the bid fitting the remainder, read back through `add_value` and
  `sub_value` as one `Nat` inequality.
* `canBuilderCoverBid_ok_toNat_add_le`: the addition-fits-in-balance form of the same
  contract, a corollary of `canBuilderCoverBid_ok_iff`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag Checked)
open EthCLSpecs.Gloas (BeaconState BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)
open EthCLLib.Proofs (pureState add_ok_iff add_value sub_ok_iff sub_value)

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

/-- Under the checked chain's real obligations, `canBuilderCoverBid` answers `true`
exactly when the bid fits the remainder. The read hypothesis is the callee's own
success. The two range facts are the `+` and `-` steps' success conditions on the
plain values (`add_ok_iff` and `sub_ok_iff`), so they name the arithmetic the chain
checks and no intermediate `minBalance` or `cover` value appears: the conclusion
reads the remainder off through `add_value` and `sub_value` as one `Nat`
inequality. No claim is made that pending-obligation accumulation is overflow-free
or that `builderIndex` identifies a registered builder. Laws: `add_ok_iff`,
`add_value`, `sub_ok_iff`, `sub_value`. -/
theorem canBuilderCoverBid_ok_iff [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount pending : Gwei),
      getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending →
      Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat < 2 ^ 64 →
      Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat
          ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat →
      (canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true ↔
        bidAmount.toPlainNat ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat
          - (Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat)) := by
  intro state builderIndex bidAmount pending hpend hrange hfit
  -- The fused laws name the two intermediates the body binds: `add_ok_iff`
  -- produces `minBalance` from the sum's range fact, `sub_ok_iff` produces
  -- `cover` from the difference's, and the value laws read both back in `Nat`
  -- terms, so the branch reasoning below is plain arithmetic.
  obtain ⟨minBalance, hmin⟩ := add_ok_iff _ _ |>.mpr hrange
  have hminval : minBalance.toPlainNat
      = Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat :=
    add_value _ _ _ hmin
  have hble : minBalance.toPlainNat
      ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat := by
    rw [hminval]
    exact hfit
  obtain ⟨cover, hsub⟩ := sub_ok_iff _ _ |>.mpr hble
  have hcovval : cover.toPlainNat
      = state.builders[builderIndex.toNat]!.balance.toPlainNat - minBalance.toPlainNat :=
    sub_value _ _ _ hsub
  -- The laws state the equations through `CLUint64.add` / `sub`; the body writes
  -- the operator surface. The two are definitionally equal, and the ascribed
  -- copies make the rewrite below match the body's terms.
  have hmin' : ((Gloas.Const.minDepositAmountG + pending : Checked Gwei)) = .ok minBalance := hmin
  have hsub' : ((state.builders[builderIndex.toNat]!.balance - minBalance : Checked Gwei))
      = .ok cover := hsub
  rw [canBuilderCoverBid_eq, hpend]
  -- `zeta` reduces the body's leading `let` and the successful read bind, putting
  -- the two remaining checked steps where the laws named them.
  show ((do
      let minBalance ← Gloas.Const.minDepositAmountG + pending
      if state.builders[builderIndex.toNat]!.balance < minBalance then pure false
      else
        let cover ← state.builders[builderIndex.toNat]!.balance - minBalance
        pure (cover ≥ bidAmount)) : Checked Bool) = .ok true ↔
    (bidAmount.toPlainNat ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat
      - (Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat))
  rw [hmin']
  show (((if state.builders[builderIndex.toNat]!.balance < minBalance then Except.ok false
        else
          (do
            let cover ← state.builders[builderIndex.toNat]!.balance - minBalance
            pure (cover ≥ bidAmount)) : Checked Bool)) = .ok true) ↔
    (bidAmount.toPlainNat ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat
      - (Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat))
  rw [hsub']
  split
  · next hlt =>
    -- The guard rejects exactly when `minBalance` exceeds the balance, which the
    -- fit hypothesis excludes; both readings are the native ones on `.val`.
    have hnat : ¬ (state.builders[builderIndex.toNat]!.balance.val.toNat
        < minBalance.val.toNat) := by
      have h1 : state.builders[builderIndex.toNat]!.balance.val.toNat
          = state.builders[builderIndex.toNat]!.balance.toPlainNat := rfl
      have h2 : minBalance.val.toNat = minBalance.toPlainNat := rfl
      omega
    exact absurd (UInt64.lt_iff_toNat_lt.mp hlt) hnat
  · next =>
    constructor
    · intro htrue
      have hle : bidAmount ≤ cover := decide_eq_true_iff.mp (Except.ok.inj htrue)
      have hnat : bidAmount.val.toNat ≤ cover.val.toNat :=
        UInt64.le_iff_toNat_le.mp hle
      have h1 : bidAmount.val.toNat = bidAmount.toPlainNat := rfl
      have h2 : cover.val.toNat = cover.toPlainNat := rfl
      have h3 : state.builders[builderIndex.toNat]!.balance.val.toNat
          = state.builders[builderIndex.toNat]!.balance.toPlainNat := rfl
      have h4 : minBalance.val.toNat = minBalance.toPlainNat := rfl
      omega
    · intro hres
      have hle : bidAmount.val.toNat ≤ cover.val.toNat := by
        have h1 : bidAmount.val.toNat = bidAmount.toPlainNat := rfl
        have h2 : cover.val.toNat = cover.toPlainNat := rfl
        have h3 : state.builders[builderIndex.toNat]!.balance.val.toNat
            = state.builders[builderIndex.toNat]!.balance.toPlainNat := rfl
        have h4 : minBalance.val.toNat = minBalance.toPlainNat := rfl
        omega
      show (Except.ok (decide (bidAmount ≤ cover)) : Checked Bool) = .ok true
      have hle' : bidAmount ≤ cover := by
        show bidAmount.val ≤ cover.val
        rw [UInt64.le_iff_toNat_le]
        exact hle
      rw [decide_eq_true hle']

/-- Equivalent `Nat`-level reading of the same contract: under the same two range
facts, acceptance puts the bid plus the computed `minBalance` within the builder's
balance, an addition that cannot wrap. A corollary of `canBuilderCoverBid_ok_iff`
by arithmetic: the remainder there is exact because the fit hypothesis bounds the
subtrahend. Laws used: `canBuilderCoverBid_ok_iff` (hence `add_value`,
`sub_value`). -/
theorem canBuilderCoverBid_ok_toNat_add_le [Preset] [HasherTag] :
    ∀ (state : BeaconState) (builderIndex : BuilderIndex) (bidAmount pending : Gwei),
      getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex = .ok pending →
      Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat < 2 ^ 64 →
      Gloas.Const.minDepositAmountG.toPlainNat + pending.toPlainNat
          ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat →
      canBuilderCoverBid (pureState state) builderIndex bidAmount = .ok true →
        bidAmount.toPlainNat + (Gloas.Const.minDepositAmountG.toPlainNat
            + pending.toPlainNat)
          ≤ state.builders[builderIndex.toNat]!.balance.toPlainNat := by
  intro state builderIndex bidAmount pending hpend hrange hfit hok
  have hle := (canBuilderCoverBid_ok_iff state builderIndex bidAmount pending
    hpend hrange hfit).mp hok
  omega

end EthCLSpecs.Proofs.Gloas
