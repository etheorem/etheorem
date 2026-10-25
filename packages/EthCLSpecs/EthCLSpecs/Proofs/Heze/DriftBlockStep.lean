import EthCLSpecs.Proofs.Heze.DriftWithdraw
import EthCLSpecs.Proofs.Heze.CheckpointFrame

/-!
# `EthCLSpecs.Proofs.Heze.DriftBlockStep`: one block keeps the invariant

`process_block` runs eight steps: the parent payload, the header, the withdrawals, the bid,
RANDAO, the eth1 vote, the operations, and the sync aggregate. Each step keeps `OpsInv`
(`processBlock_ops`). The parent payload adds one reservation per withdrawal request and a cost
per consolidation request, each attestation costs `attBudget sq`, and the sync aggregate costs
`syncBudget sq U`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- A step that keeps `econBox` and `ordView` keeps `OpsInv`. -/
theorem OpsInv.of_frames {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s)
    (he : econBox (pureState s') = econBox (pureState s))
    (ho : ordView (pureState s') = ordView (pureState s)) : OpsInv vals st₀ a₀ E CX CC Γp B s' :=
  hs.of_econ he (congrArg Prod.snd ho)

/-- **One block keeps the invariant.** The start state `a₀` holds the facts of `OpsCtx` and
`ConsCtx`, its registry is below `2 ^ 40`, and `sq * sq ≤ T ≤ U` for its total active balance
`T`. Each withdrawal request of the block has an amount below `2 ^ 62`. -/
theorem processBlock_ops {vals : List ValidatorIndex} {st₀ a₀ b : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (Y : ConsCtx st₀ a₀ E CC)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B a₀) (h40 : a₀.validators.val.size < 2 ^ 40)
    {sq U : Nat} (h0 : 0 < sq)
    (hsq : sq * sq ≤ (totBal a₀).toNat)
    (hU : (totBal a₀).toNat ≤ U)
    (blk : EthCLSpecs.Heze.BeaconBlock)
    (hamt : ∀ wr ∈ blk.body.parentExecutionRequests.withdrawals.val, wr.amount.toNat < 2 ^ 62)
    (hΓ : Γp + blk.body.parentExecutionRequests.withdrawals.val.size ≤ Γc)
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) blk).run (pureState a₀)
      = .ok ((), pureState b)) :
    OpsInv vals st₀ a₀ E CX CC (Γp + blk.body.parentExecutionRequests.withdrawals.val.size)
      (B + blk.body.parentExecutionRequests.consolidations.val.size * slashCost maxEBN +
        blk.body.attestations.val.size * attBudget sq + syncBudget sq U) b := by
  obtain ⟨NX, ΓX, P, -, -⟩ := X.pre
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  have t1 := processParentExecutionPayload_ops X Y hs blk hamt hΓ h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  have t2 := t1.of_frames (processBlockHeader_frame_econ h2) (processBlockHeader_frame_ord h2)
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  have t3 : OpsInv vals st₀ a₀ E CX CC (Γp + blk.body.parentExecutionRequests.withdrawals.val.size)
      (B + blk.body.parentExecutionRequests.consolidations.val.size * slashCost maxEBN) s3 := by
    obtain ⟨⟨V, W, tag, I⟩, hk⟩ := t2
    obtain ⟨hk', V', I'⟩ := I.processWithdrawals vals X.nodup st₀
      (by rw [hk.epoch]; exact P.curE) (by have := hk.size; unfold sizeOf at this; omega) h3
    exact ⟨⟨V', W, tag, I'⟩, hk.trans hk'⟩
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  have t4 := t3.of_frames (processExecutionPayloadBid_frame_econ h4)
    (processExecutionPayloadBid_frame_ord h4)
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  have t5 := t4.of_frames (processRandao_frame_econ h5) (processRandao_frame_ord h5)
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  have t6 := t5.of_frames (processEth1Data_frame_econ h6) (processEth1Data_frame_ord h6)
  obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  have t7 := processOperations_ops X hΓ t6 h0 hsq _ h7
  -- The sync aggregate.
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := t7
  have ht := totBal_congr hk P.h64
  obtain ⟨hm, hb, hsz⟩ := processSyncAggregate_move vals X.nodup st₀ E _ s7 b h0 (by rw [ht]; exact hsq)
    (by rw [ht]; exact hU) X.consts.syncLt h
  have hv : b.validators = s7.validators := by rw [hb]
  have hsl : b.slot = s7.slot := by rw [hb]
  exact ⟨⟨_, W, tag, I.balanceStep (by rw [hb]) hsz hm⟩, hk.trans (AcKeep.of_validators hsl hv)⟩

end

end EthCLSpecs.Proofs.Heze
