import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.ParentPayloadEmpty`: a child on the EMPTY edge settles nothing

In the pinned `v1.7.0-alpha.11`, the child block of a block applies the payload of that
block. (The change came in `v1.7.0-alpha.5`.) `processParentExecutionPayload` compares
two hashes: the `parentBlockHash` of the child bid, and the `blockHash` of the cached
parent bid. It calls `applyParentExecutionPayload` only when the two hashes are equal.
`applyParentExecutionPayload` is the only caller of `settleBuilderPayment`
(`consensus-specs/specs/gloas/beacon-chain.md:1198-1241`).

Fork choice uses the same comparison. `getParentPayloadStatus` puts a child under the
EMPTY node or the FULL node of its parent. This module proves one fact for each side.

1. On the EMPTY edge, with the empty parent requests, `processParentExecutionPayload`
   does not change the state. With other parent requests, it rejects with an `assert`.
   The module proves this one step, not the whole block transition.
2. Fork choice calls an edge EMPTY exactly when the two hashes are different.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconBlock ExecutionRequests
  processParentExecutionPayload getParentPayloadStatus)

/-- On the EMPTY edge, `processParentExecutionPayload` does not change
the state. The hypotheses are that the child bid does not extend the block hash of the
cached parent bid, and that the child carries the empty parent requests. Then the run
succeeds and returns the input state. So `builderPendingPayments` and
`builderPendingWithdrawals` do not change, and this step does not settle the bid of the
parent. -/
theorem processParentExecutionPayload_run_of_empty_parent
    [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (state : State) (block : BeaconBlock),
      block.body.signedExecutionPayloadBid.message.parentBlockHash
          ≠ (sszGet state latestExecutionPayloadBid).blockHash →
      htr block.body.parentExecutionRequests = htr (default : ExecutionRequests) →
      (processParentExecutionPayload (StateTransition := HezeRun) block).run state
        = .ok ((), state) := by
  intro state block hempty hreq
  simp [processParentExecutionPayload, hempty, hreq]
  rfl

/-- Fork choice puts `child` under the EMPTY node of its parent exactly when the
`parentBlockHash` of the child bid is different from the `blockHash` of the parent
bid. -/
theorem getParentPayloadStatus_run_eq_empty_iff
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store : Store map) (child parent : BeaconBlock),
      FcMap.lookup store.blocks child.parentRoot = some parent →
      ((getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
            store child).run store
          = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, store)
        ↔ child.body.signedExecutionPayloadBid.message.parentBlockHash
            ≠ parent.body.signedExecutionPayloadBid.message.blockHash) := by
  intro store child parent hparent
  by_cases h : child.body.signedExecutionPayloadBid.message.parentBlockHash
      = parent.body.signedExecutionPayloadBid.message.blockHash
  · simp [getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey, hparent, h,
      EthCLSpecs.Heze.Const.payloadStatusEmpty, EthCLSpecs.Heze.Const.payloadStatusFull]
    -- The FULL status `1` and the EMPTY status `0` are different `UInt8` values.
    intro heq
    injection heq with hpair
    injection hpair with hstatus
    exact absurd hstatus (by decide)
  · simp [getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey, hparent, h]
    rfl

end EthCLSpecs.Proofs.Heze
