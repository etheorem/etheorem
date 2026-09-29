import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLLib.Proofs.Frame

/-!
# `EthCLSpecs.Proofs.Heze.HandlerFrames`: only `onInclusionList` writes the IL store

The IL store (`inclusionListStore`) is one field of the Heze `Store`. `onInclusionList`
writes it (`OnInclusionList.lean`). This module proves that the six other handlers keep it:
`onTick`, `onBlock`, `onAttestation`, `onAttesterSlashing`, `onPayloadAttestationMessage`,
and `onExecutionPayloadEnvelope`. Each theorem is a `KeepsAt` fact
(`EthCLLib/Proofs/Frame.lean`) for the field, at every value.

The handlers have one shape. They read the store with `get`, compute, and write a record
update of the store they read with `set`. Helpers that return a store return a record
update of their store argument. None of the updates names `inclusionListStore`. So the
proofs walk the handler body one bind at a time, and the tactic `keeps_solve` does the walk.

## The tactic

`keeps_step` applies one rule of `EthCLLib/Proofs/Frame.lean` to the goal, in a fixed order:

1. A side goal `st.inclusionListStore = v` closes by a hypothesis from a `get`, or by the
   checkpoint lemmas below and then a hypothesis.
2. `get`, `set`, `pure`, `throw`, and `ofExcept` have their own rules.
3. The loop rules come before the bind rules. A bind rule can also match the unfolded
   body of a loop, and then the loop rule never fires.
4. A bind whose first action returns a store tries `KeepsAt.bind_ret`, then a plain bind
   with a solved first action. The fallback is `KeepsAt.bind_reset`, for a first action
   followed by a `set`, such as `getHead` in `onBlock`.
5. `split` handles `if` and `match`, and `frame_unfold` unfolds one helper.

Each rule applies at reducible and instance transparency, so a rule that does not match
fails fast. The rules take the first action of a bind as an implicit argument. With an
explicit `_` there, a failed match against an `if` exhausts the heartbeats.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  run_bind_eq_ok run_pure_eq_ok KeepsAt Resets)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store InclusionListStore Attestation AttesterSlashing
  SignedBeaconBlock PayloadAttestationMessage SignedExecutionPayloadEnvelope ExecutionPayload
  ExecutionRequests Transaction onTick onBlock onAttestation onAttesterSlashing
  onPayloadAttestationMessage onExecutionPayloadEnvelope)

/-- `updateCheckpoints` writes only the two checkpoints. -/
theorem updateCheckpoints_ilStore {map : MapKind} [EthCLSpecs.Heze.Preset] [HasherTag]
    [EthCLSpecs.Heze.Config] [FcMap map] (st : Store map)
    (j f : EthCLSpecs.Heze.Checkpoint) :
    (EthCLSpecs.Heze.updateCheckpoints st j f).inclusionListStore = st.inclusionListStore := by
  simp only [EthCLSpecs.Heze.updateCheckpoints]
  (repeat' split) <;> rfl

/-- `updateUnrealizedCheckpoints` writes only the two unrealized checkpoints. -/
theorem updateUnrealizedCheckpoints_ilStore {map : MapKind} [EthCLSpecs.Heze.Preset] [HasherTag]
    [EthCLSpecs.Heze.Config] [FcMap map] (st : Store map)
    (j f : EthCLSpecs.Heze.Checkpoint) :
    (EthCLSpecs.Heze.updateUnrealizedCheckpoints st j f).inclusionListStore
      = st.inclusionListStore := by
  simp only [EthCLSpecs.Heze.updateUnrealizedCheckpoints]
  (repeat' split) <;> rfl

/-- A `for` loop over an SSZ list keeps `f` when each body run keeps it. The loop runs
over the underlying array (`SizzLean/Repr/Instances.lean`). -/
theorem keepsAt_forIn_sszList {σ ε α β δ : Type} {f : σ → β} {v : β} {cap : Nat}
    (body : δ → α → StateT σ (Except ε) (ForInStep α))
    (hbody : ∀ d a, KeepsAt f v (body d a)) (xs : SizzLean.Repr.SSZList δ cap) (init : α) :
    KeepsAt f v (forIn xs init body) :=
  KeepsAt.forIn_array body hbody xs.val init

/-- Unfold one read-only or store-returning helper that a handler calls. -/
syntax "frame_unfold" : tactic
macro_rules
  | `(tactic| frame_unfold) => `(tactic| first
      | unfold FcMap.getOrThrow
      | unfold FcMap.getOrThrowKey
      | unfold FcMap.getOrAssert
      | simp only [EthCLLib.Spec.checkedAdd]
      | simp only [EthCLLib.Spec.checkedSub]
      | simp only [EthCLLib.Spec.checkedMul]
      | simp only [EthCLLib.Spec.throwArithmetic]
      | simp only [EthCLLib.Spec.liftErr]
      | simp only [EthCLLib.Spec.sszOfArrayM]
      | simp only [EthCLLib.Spec.throwListFull]
      | simp only [EthCLLib.Spec.arrGetIdx]
      | simp only [EthCLLib.Spec.runNestedStateTransition]
      | unfold EthCLSpecs.Heze.onTickPerSlot.computeSlotsSinceEpochStart
      | simp only [EthCLLib.Spec.evalNestedStateTransition]
      | simp only [EthCLSpecs.Heze.getCurrentSlot]
      | simp only [EthCLSpecs.Heze.getSlotsSinceGenesis]
      | simp only [EthCLSpecs.Heze.getCurrentStoreEpoch]
      | simp only [EthCLSpecs.Heze.timeIntoSlotMs]
      | simp only [EthCLSpecs.Heze.getParentPayloadStatus]
      | simp only [EthCLSpecs.Heze.getAncestor]
      | simp only [EthCLSpecs.Heze.getCheckpointBlock]
      | simp only [EthCLSpecs.Heze.getDependentRoot]
      | simp only [EthCLSpecs.Heze.validateOnAttestation]
      | simp only [EthCLSpecs.Heze.recordBlockTimeliness]
      | simp only [EthCLSpecs.Heze.updateProposerBoostRoot]
      | simp only [EthCLSpecs.Heze.recordPtcVotes]
      | simp only [EthCLSpecs.Heze.storeTargetCheckpointState]
      | simp only [EthCLSpecs.Heze.onTickPerSlot]
      | simp only [EthCLSpecs.Heze.onPayloadAttestationMessage]
      | simp only [EthCLSpecs.Heze.notifyPtcMessages]
      | simp only [EthCLSpecs.Heze.computePulledUpTip]
      | simp only [EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]
      | simp only [EthCLSpecs.Heze.getInclusionListTransactions]
      | simp only [EthCLSpecs.Heze.getInclusionListCommittee]
      | simp only [EthCLSpecs.Heze.collectInclusionListTransactions])

/-- Split a bind whose first action returns a state value. The `Returns` goal stays open
for the `Returns` rules of `keeps_step`. -/
syntax "keeps_bind_ret" : tactic
macro_rules
  | `(tactic| keeps_bind_ret) => `(tactic| with_reducible_and_instances
      refine EthCLLib.Proofs.KeepsAt.bind_ret ?_ ?_ fun _ _ => ?_)
/-- Split a bind. -/
syntax "keeps_bind" : tactic
macro_rules
  | `(tactic| keeps_bind) => `(tactic| with_reducible_and_instances
      refine EthCLLib.Proofs.KeepsAt.bind ?_ fun _ => ?_)

/-- One step of a `KeepsAt` or `Resets` proof over a handler body. -/
syntax "keeps_step" : tactic
/-- A `KeepsAt` or `Resets` proof over a handler body, run until it closes. -/
syntax "keeps_solve" : tactic
macro_rules
  | `(tactic| keeps_solve) => `(tactic| (repeat' keeps_step) <;> done)
macro_rules
  | `(tactic| keeps_step) => `(tactic| first
      | assumption
      | rw [EthCLSpecs.Proofs.Heze.updateCheckpoints_ilStore]
      | rw [EthCLSpecs.Proofs.Heze.updateUnrealizedCheckpoints_ilStore]
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.get_bind fun _ _ => ?_
      | with_reducible_and_instances refine EthCLLib.Proofs.KeepsAt.set_bind _ ?_ ?_
      | with_reducible_and_instances refine EthCLLib.Proofs.Resets.set_bind _ ?_ ?_
      | with_reducible_and_instances refine EthCLLib.Proofs.KeepsAt.set _ ?_
      | with_reducible_and_instances refine EthCLLib.Proofs.Resets.set _ ?_
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.pure _
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.throw _
      | with_reducible_and_instances exact EthCLLib.Proofs.Resets.throw _
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.ofExcept _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.fuelLoop _ _ (fun _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.fuelIterateM! _ _ (fun _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.forIn_array _ (fun _ _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.forIn_list _ (fun _ _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLSpecs.Proofs.Heze.keepsAt_forIn_sszList _ (fun _ _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.foldlM_array _ (fun _ _ => ?_) _ _
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.foldlM_list _ (fun _ _ => ?_) _ _
      | with_reducible_and_instances refine EthCLLib.Proofs.Returns.pure _ ?_
      | with_reducible_and_instances exact EthCLLib.Proofs.Returns.throw _
      | with_reducible_and_instances refine EthCLLib.Proofs.Returns.bind fun _ => ?_
      | (keeps_bind_ret; focus keeps_solve)
      | (keeps_bind; focus keeps_solve)
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.bind_reset fun _ => ?_
      | with_reducible_and_instances refine EthCLLib.Proofs.Resets.bind fun _ => ?_
      | split
      | frame_unfold
      | (dsimp only; fail_if_success done))

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

omit [CryptoBackend] in
/-- `onTick` keeps the IL store. -/
theorem onTick_keeps_ilStore (v : InclusionListStore map) (time : UInt64) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the IL store. -/
theorem onBlock_keeps_ilStore (v : InclusionListStore map) (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

/-- `onAttestation` keeps the IL store. -/
theorem onAttestation_keeps_ilStore (v : InclusionListStore map) (att : Attestation)
    (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the IL store. -/
theorem onAttesterSlashing_keeps_ilStore (v : InclusionListStore map) (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the IL store. `onBlock` runs it for each attester
of the block's payload attestations. -/
theorem onPayloadAttestationMessage_keeps_ilStore (v : InclusionListStore map)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

section EngineSeam
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the IL store. It reads the IL store to record the
answer, and writes the answer map. -/
theorem onExecutionPayloadEnvelope_keeps_ilStore (v : InclusionListStore map)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.inclusionListStore) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

end EngineSeam

end

end EthCLSpecs.Proofs.Heze
