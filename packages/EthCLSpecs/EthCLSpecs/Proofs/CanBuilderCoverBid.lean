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

open EthCLLib.Spec
open EthCLSpecs.Fulu (BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)

namespace EthCLSpecs.Proofs

variable [Preset] [HasherTag]

/-- `canBuilderCoverBid` returns `true` exactly when its computed `minBalance`
does not exceed the builder's balance and the bid fits in the remainder.
These are the literal `UInt64` values computed by the implementation; no
non-overflow or in-range interpretation is asserted. -/
theorem canBuilderCoverBid_iff (state : EthCLSpecs.Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    canBuilderCoverBid state builderIndex bidAmount = true ↔
      let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
      let minBalance := EthCLSpecs.Fulu.Const.minDepositAmountG + getPendingBalanceToWithdrawForBuilder state builderIndex
      minBalance ≤ builderBalance ∧ bidAmount ≤ builderBalance - minBalance := by
  unfold canBuilderCoverBid
  -- Reduce the local `let`s before splitting the function's balance guard.
  dsimp only
  split <;> simp_all <;> bv_decide

/-- The same fact as `canBuilderCoverBid_iff`, restated over `Nat` so the
subtraction disappears: `canBuilderCoverBid` accepts exactly when the reserve
`minBalance` (still the implementation's computed `UInt64` value, not
decomposed into `MIN_DEPOSIT_AMOUNT` plus the pending-obligation sum) and the
bid, added as `Nat`s, fit within the balance. `Nat` addition cannot wrap, so
this is the overflow-free reading of the `UInt64` guard, an equivalence, not
just the forward direction, derived from `canBuilderCoverBid_iff` by bridging
`≤` and the (here provably non-wrapping) `UInt64` subtraction to `Nat` via
`UInt64.le_iff_toNat_le` / `UInt64.toNat_sub_of_le`, then closing the resulting
plain-`Nat` goal with `omega` (which, unlike `bv_decide`, has no trouble with
`Nat`'s unbounded `+`). `generalize` stands in for mathlib's `set`, unavailable
in this mathlib-free package, to name the two computed values once rather than
repeat the full projection chain in every step. -/
theorem canBuilderCoverBid_iff_toNat_add_le
    (state : EthCLSpecs.Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    canBuilderCoverBid state builderIndex bidAmount = true ↔
      let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
      let minBalance := EthCLSpecs.Fulu.Const.minDepositAmountG + getPendingBalanceToWithdrawForBuilder state builderIndex
      minBalance.toNat + bidAmount.toNat ≤ builderBalance.toNat := by
  rw [canBuilderCoverBid_iff]
  dsimp only
  generalize (sszGet state builders[builderIndex.toNat]!).balance = builderBalance
  generalize EthCLSpecs.Fulu.Const.minDepositAmountG + getPendingBalanceToWithdrawForBuilder state builderIndex = minBalance
  constructor
  · rintro ⟨h1, h2⟩
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h1] at h2
    have h1' := UInt64.le_iff_toNat_le.mp h1
    omega
  · intro h
    have h1 : minBalance ≤ builderBalance := UInt64.le_iff_toNat_le.mpr (by omega)
    refine ⟨h1, ?_⟩
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h1]
    omega

end EthCLSpecs.Proofs
