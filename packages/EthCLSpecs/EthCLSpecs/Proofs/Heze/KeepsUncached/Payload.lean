import EthCLSpecs.Proofs.Heze.KeepsUncached.Block

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached.Payload`: the parent payload keeps the uncached box

`processParentExecutionPayload` is the first substep of `processBlock`. When the parent
block was full, it runs `applyParentExecutionPayload`. That function runs five loops of
execution requests, settles the parent's builder payment, and writes two fields. This
file proves `KeepsUncached` for the five request handlers, their callees, and the two
payload functions.

The request handlers are inherited bodies (`processDepositRequest`,
`processWithdrawalRequest`, `processConsolidationRequest` from Fulu, the builder
requests from Gloas), so each lemma names the Heze constant. Most proofs unfold the
body and run the `keeps_uncached` tactic. A callee with a state write has its own
lemma, and the caller's proof applies it at the bind. The two payload functions take
one bind at a time. The tactic runs out of heartbeats on their long bodies, and the
settlement `if` of `applyParentExecutionPayload` elaborates to a join point that the
proof names once. All the lemmas are supporting facts, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config ValidatorIndex Gwei BLSPubkey Bytes32 ExecutionAddress
  BuilderIndex BeaconBlock DepositRequest WithdrawalRequest ConsolidationRequest
  BuilderDepositRequest BuilderExitRequest ExecutionRequests
  processDepositRequest processWithdrawalRequest processConsolidationRequest
  computeConsolidationEpochAndUpdateChurn switchToCompoundingValidator
  queueExcessActiveBalance initiateBuilderExit addBuilderToRegistry applyDepositForBuilder
  processBuilderDepositRequest processBuilderExitRequest applyParentExecutionPayload
  processParentExecutionPayload)
open EthCLLib.Proofs (pureState KeepsUncached keepsUncached_bind keepsUncached_get
  keepsUncached_ite keepsUncached_pure keepsUncached_throw keepsUncached_modify
  keepsUncached_forIn_sszList)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- Close each goal that `keeps_uncached` leaves open at a call to a function with a
lemma of its own. The tactic does not unfold a callee, so a call such as
`initiateValidatorExit i` stays as a goal. This tactic applies the callee lemmas, which
come from this file and from `Proofs/Heze/KeepsUncached.lean` and `…/Block.lean`. -/
local macro "close_callees" : tactic => `(tactic| all_goals first
  | exact keepsUncached_initiateValidatorExit _
  | exact keepsUncached_computeExitEpochAndUpdateChurn _
  | exact keepsUncached_computeConsolidationEpochAndUpdateChurn _
  | exact keepsUncached_switchToCompoundingValidator _
  | exact keepsUncached_addBuilderToRegistry _ _ _ _ _
  | exact keepsUncached_initiateBuilderExit _
  | exact keepsUncached_settleBuilderPayment _
  | exact keepsUncached_processDepositRequest _
  | exact keepsUncached_processWithdrawalRequest _
  | exact keepsUncached_processConsolidationRequest _
  | exact keepsUncached_processBuilderDepositRequest _
  | exact keepsUncached_processBuilderExitRequest _
  | exact keepsUncached_applyParentExecutionPayload _)

/-- `processDepositRequest` keeps the flavour: a read, a write of the deposit start
index, and an `appendState` of the pending deposit. -/
theorem keepsUncached_processDepositRequest (dr : DepositRequest) :
    KeepsUncached (processDepositRequest (StateTransition := HezeRun) dr) := by
  unfold processDepositRequest
  keeps_uncached
  close_callees

/-- `computeConsolidationEpochAndUpdateChurn` keeps the flavour: one read and one
two-clause write, as `computeExitEpochAndUpdateChurn`. -/
theorem keepsUncached_computeConsolidationEpochAndUpdateChurn (consolidationBalance : Gwei) :
    KeepsUncached (computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      consolidationBalance) := by
  unfold computeConsolidationEpochAndUpdateChurn
  keeps_uncached
  close_callees

/-- `queueExcessActiveBalance` keeps the flavour: a read, a balance write, and an
`appendState` of the pending deposit when the balance is above the minimum. -/
theorem keepsUncached_queueExcessActiveBalance (i : ValidatorIndex) :
    KeepsUncached (queueExcessActiveBalance (StateTransition := HezeRun) i) := by
  unfold queueExcessActiveBalance
  keeps_uncached
  close_callees

/-- `switchToCompoundingValidator` keeps the flavour: a credential write, then
`queueExcessActiveBalance`. -/
theorem keepsUncached_switchToCompoundingValidator (i : ValidatorIndex) :
    KeepsUncached (switchToCompoundingValidator (StateTransition := HezeRun) i) := by
  unfold switchToCompoundingValidator
  keeps_uncached
  all_goals exact keepsUncached_queueExcessActiveBalance _

/-- `processWithdrawalRequest` keeps the flavour: the gates of the request, then either
a validator exit through `initiateValidatorExit`, or a partial withdrawal through
`computeExitEpochAndUpdateChurn` and an `appendState`. -/
theorem keepsUncached_processWithdrawalRequest (wr : WithdrawalRequest) :
    KeepsUncached (processWithdrawalRequest (StateTransition := HezeRun) wr) := by
  unfold processWithdrawalRequest
  keeps_uncached
  close_callees

set_option maxHeartbeats 400000 in
/-- `processConsolidationRequest` keeps the flavour: the gates of the request, then a
switch to compounding credentials or a consolidation. The consolidation runs
`computeConsolidationEpochAndUpdateChurn`, a checked sum, a validator write, and an
`appendState`. The checked sum needs more than the default heartbeat limit. -/
theorem keepsUncached_processConsolidationRequest (req : ConsolidationRequest) :
    KeepsUncached (processConsolidationRequest (StateTransition := HezeRun) req) := by
  unfold processConsolidationRequest
  keeps_uncached
  close_callees

/-- `initiateBuilderExit` keeps the flavour: a read, a gate, and one builder write. -/
theorem keepsUncached_initiateBuilderExit (builderIndex : BuilderIndex) :
    KeepsUncached (initiateBuilderExit (StateTransition := HezeRun) builderIndex) := by
  unfold initiateBuilderExit
  keeps_uncached
  close_callees

/-- `addBuilderToRegistry` keeps the flavour: a read, then a `setOrAppendState` of the
new builder. -/
theorem keepsUncached_addBuilderToRegistry (pubkey : BLSPubkey) (version : UInt8)
    (executionAddress : ExecutionAddress) (amount : Gwei) (slot : EthCLSpecs.Heze.Slot) :
    KeepsUncached (addBuilderToRegistry (StateTransition := HezeRun) pubkey version
      executionAddress amount slot) := by
  unfold addBuilderToRegistry
  keeps_uncached
  close_callees

/-- `applyDepositForBuilder` keeps the flavour: a new builder through
`addBuilderToRegistry`, or a balance write on the builder that the key names. -/
theorem keepsUncached_applyDepositForBuilder (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) (sig : EthCLSpecs.Heze.BLSSignature) (slot : EthCLSpecs.Heze.Slot) :
    KeepsUncached (applyDepositForBuilder (StateTransition := HezeRun) pubkey wc amount
      sig slot) := by
  unfold applyDepositForBuilder
  keeps_uncached
  close_callees

/-- `processBuilderDepositRequest` keeps the flavour: its gates, then
`applyDepositForBuilder`. -/
theorem keepsUncached_processBuilderDepositRequest (request : BuilderDepositRequest) :
    KeepsUncached (processBuilderDepositRequest (StateTransition := HezeRun) request) := by
  unfold processBuilderDepositRequest
  keeps_uncached
  close_callees

/-- `processBuilderExitRequest` keeps the flavour: its gates, then
`initiateBuilderExit`. -/
theorem keepsUncached_processBuilderExitRequest (request : BuilderExitRequest) :
    KeepsUncached (processBuilderExitRequest (StateTransition := HezeRun) request) := by
  unfold processBuilderExitRequest
  keeps_uncached
  close_callees

/-- `applyParentExecutionPayload` keeps the flavour: five loops of requests, each through
its handler lemma, then the settlement of the parent payment through
`settleBuilderPayment` or an `appendState`, then two writes. -/
theorem keepsUncached_applyParentExecutionPayload (requests : ExecutionRequests) :
    KeepsUncached (applyParentExecutionPayload (StateTransition := HezeRun) requests) := by
  unfold applyParentExecutionPayload
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_sszList _ (fun d _ => keepsUncached_bind
    (keepsUncached_processDepositRequest d) (fun _ => keepsUncached_pure _)) _ _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_sszList _ (fun w _ => keepsUncached_bind
    (keepsUncached_processWithdrawalRequest w) (fun _ => keepsUncached_pure _)) _ _)
    (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_sszList _ (fun c _ => keepsUncached_bind
    (keepsUncached_processConsolidationRequest c) (fun _ => keepsUncached_pure _)) _ _)
    (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_sszList _ (fun bd _ => keepsUncached_bind
    (keepsUncached_processBuilderDepositRequest bd) (fun _ => keepsUncached_pure _)) _ _)
    (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_forIn_sszList _ (fun be _ => keepsUncached_bind
    (keepsUncached_processBuilderExitRequest be) (fun _ => keepsUncached_pure _)) _ _)
    (fun _ => ?_)
  -- The `do` block after the settlement `if` elaborates to a join point
  -- `have __do_jp := fun _ => …` that every branch calls. `extract_lets` names it, so the
  -- fact about it is proved once and each branch reuses it.
  extract_lets jp
  have hjp : ∀ y, KeepsUncached (jp y) := fun _ =>
    keepsUncached_bind (keepsUncached_modify _ (fun _ => ⟨_, rfl⟩))
      (fun _ => keepsUncached_modify _ (fun _ => ⟨_, rfl⟩))
  refine keepsUncached_ite
    (fun _ => keepsUncached_bind (keepsUncached_settleBuilderPayment _) hjp) (fun _ => ?_)
  refine keepsUncached_ite
    (fun _ => keepsUncached_bind (keepsUncached_settleBuilderPayment _) hjp) (fun _ => ?_)
  refine keepsUncached_ite (fun _ => keepsUncached_bind ?_ hjp)
    (fun _ => keepsUncached_bind (keepsUncached_pure _) hjp)
  keeps_uncached

/-- `processParentExecutionPayload` keeps the flavour: a read and a gate, then
`applyParentExecutionPayload` when the parent block was full. -/
theorem keepsUncached_processParentExecutionPayload (block : BeaconBlock) :
    KeepsUncached (processParentExecutionPayload (StateTransition := HezeRun) block) := by
  unfold processParentExecutionPayload
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_ite (fun _ => ?_) (fun _ => ?_)
  · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
  · exact keepsUncached_bind
      (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
      (fun _ => keepsUncached_applyParentExecutionPayload _)

end

end EthCLSpecs.Proofs.Heze
