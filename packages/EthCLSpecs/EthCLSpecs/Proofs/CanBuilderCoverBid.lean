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

end EthCLSpecs.Proofs
