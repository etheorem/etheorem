import EthCLSpecs.Gloas.Operations
import Std.Tactic.BVDecide

/-!
# `EthCLSpecs.Proofs.CanBuilderCoverBid`: Boolean characterization

`EthCLSpecs.Gloas.canBuilderCoverBid` is a pure `Bool` predicate used by
`processExecutionPayloadBid` before queuing a `BuilderPendingPayment`. This
file characterizes its result exactly using the `builderBalance` and
`minBalance` values computed by the implementation.

These are literal `UInt64` values; the theorem does not assert that accumulation
of pending obligations is overflow-free. Indexing is total, so the theorem also
holds for out-of-range `builderIndex` values, without claiming that the resulting
default value represents a registered builder.

Two theorems:

* `canBuilderCoverBid_iff`: the exact implementation-level characterization,
  `UInt64` throughout, guard and subtraction spelled exactly as the function
  computes them.
* `canBuilderCoverBid_iff_toNat_add_le`: a semantic characterization relative
  to that same computed `minBalance`, restated over `Nat` so the guard reads
  as a single addition-fits-in-balance fact rather than a subtraction.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Bounds and termination
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Fulu (BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)

/-- `canBuilderCoverBid` returns `true` exactly when its computed `minBalance`
does not exceed the builder's balance and the bid fits in the remainder.
These are the literal `UInt64` values computed by the implementation; no
claim is made that pending-obligation accumulation is overflow-free or that
`builderIndex` identifies a registered builder. -/
theorem canBuilderCoverBid_iff [Preset] [HasherTag] :
    ∀ (state : EthCLSpecs.Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid state builderIndex bidAmount = true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance :=
          EthCLSpecs.Fulu.Const.minDepositAmountG +
          getPendingBalanceToWithdrawForBuilder state builderIndex
        minBalance ≤ builderBalance ∧ bidAmount ≤ builderBalance - minBalance := by
  intro state builderIndex bidAmount
  unfold canBuilderCoverBid
  -- Reduce the local `let`s before splitting the function's balance guard.
  dsimp only
  split <;> simp_all <;> bv_decide

/-- Equivalent `Nat`-level characterization: `canBuilderCoverBid` accepts
exactly when the computed `minBalance` plus the bid fits within the builder's
balance. The addition in this conclusion cannot wrap; `minBalance` itself
remains the literal `UInt64` value produced by the implementation. -/
theorem canBuilderCoverBid_iff_toNat_add_le [Preset] [HasherTag] :
    ∀ (state : EthCLSpecs.Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid state builderIndex bidAmount = true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance :=
          EthCLSpecs.Fulu.Const.minDepositAmountG +
          getPendingBalanceToWithdrawForBuilder state builderIndex
        minBalance.toNat + bidAmount.toNat ≤ builderBalance.toNat := by
  intro state builderIndex bidAmount
  rw [canBuilderCoverBid_iff]
  dsimp only
  generalize (sszGet state builders[builderIndex.toNat]!).balance = builderBalance
  generalize EthCLSpecs.Fulu.Const.minDepositAmountG +
    getPendingBalanceToWithdrawForBuilder state builderIndex = minBalance
  constructor
  · rintro ⟨h_min, h_bid⟩
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_min] at h_bid
    have h_min_nat := UInt64.le_iff_toNat_le.mp h_min
    omega
  · intro h
    have h_min : minBalance ≤ builderBalance := UInt64.le_iff_toNat_le.mpr (by omega)
    refine ⟨h_min, ?_⟩
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_min]
    omega

end EthCLSpecs.Proofs
