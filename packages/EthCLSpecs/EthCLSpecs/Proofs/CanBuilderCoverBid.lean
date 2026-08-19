import EthCLSpecs.Gloas.Operations

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

A private `le_sub_iff_toNat_add_le` carries the `UInt64`-to-`Nat` step the second
theorem needs, keeping the spec-level statements free of the arithmetic detour.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Bounds and termination
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas (BuilderIndex Gwei Preset)
open EthCLSpecs.Gloas (canBuilderCoverBid getPendingBalanceToWithdrawForBuilder)

/-- `canBuilderCoverBid` returns `true` exactly when its computed `minBalance`
does not exceed the builder's balance and the bid fits in the remainder.
These are the literal `UInt64` values computed by the implementation; no
claim is made that pending-obligation accumulation is overflow-free or that
`builderIndex` identifies a registered builder. -/
@[characterizes EthCLSpecs.Gloas.canBuilderCoverBid]
theorem canBuilderCoverBid_iff [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid state builderIndex bidAmount = true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance :=
          Gloas.Const.minDepositAmountG +
          getPendingBalanceToWithdrawForBuilder state builderIndex
        minBalance ≤ builderBalance ∧ bidAmount ≤ builderBalance - minBalance := by
  intro state builderIndex bidAmount
  -- Both lemmas restate `UInt64`'s `<` / `≤` as `Nat` comparisons on `toNat`,
  -- which is what lets `simp` discharge the guard's `if` and pair the surviving
  -- branch conditions into the conjunction.
  simp [canBuilderCoverBid, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]

/-- The arithmetic bridge behind the `Nat` restatement below: under `b ≤ a`, the
truncating difference `a - b` bounds `c` exactly when `b + c` fits in `a` over
`Nat`. Stated on bare `UInt64`s, so the spec-level theorem can apply it without
respelling the balance expressions to generalize them first. -/
private theorem le_sub_iff_toNat_add_le {a b c : UInt64} (h : b ≤ a) :
    c ≤ a - b ↔ b.toNat + c.toNat ≤ a.toNat := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h]
  have := UInt64.le_iff_toNat_le.mp h
  omega

/-- Equivalent `Nat`-level characterization: `canBuilderCoverBid` accepts
exactly when the computed `minBalance` plus the bid fits within the builder's
balance. The addition in this conclusion cannot wrap; `minBalance` itself
remains the literal `UInt64` value produced by the implementation. -/
theorem canBuilderCoverBid_iff_toNat_add_le [Preset] [HasherTag] :
    ∀ (state : Gloas.State) (builderIndex : BuilderIndex) (bidAmount : Gwei),
      canBuilderCoverBid state builderIndex bidAmount = true ↔
        let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
        let minBalance :=
          Gloas.Const.minDepositAmountG +
          getPendingBalanceToWithdrawForBuilder state builderIndex
        minBalance.toNat + bidAmount.toNat ≤ builderBalance.toNat := by
  intro state builderIndex bidAmount
  rw [canBuilderCoverBid_iff]
  dsimp only
  constructor
  · rintro ⟨h_min, h_bid⟩
    exact (le_sub_iff_toNat_add_le h_min).mp h_bid
  · intro h
    -- `Nat.le_add_right` drops the bid to recover the `minBalance ≤ builderBalance`
    -- half; both operands are inferred from `h`, so neither is respelled here.
    have h_min := UInt64.le_iff_toNat_le.mpr (Nat.le_trans (Nat.le_add_right _ _) h)
    exact ⟨h_min, (le_sub_iff_toNat_add_le h_min).mpr h⟩

end EthCLSpecs.Proofs
