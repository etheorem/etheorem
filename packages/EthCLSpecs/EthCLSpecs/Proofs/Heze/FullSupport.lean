import EthCLSpecs.Proofs.Heze.HonestVoteSide

/-!
# `EthCLSpecs.Proofs.Heze.FullSupport`: a message on the FULL side is from after the block

`HonestVoteSide.lean` follows `get_ancestor` (`gloas/fork-choice.md:337`) from a node below
`empty r` to `empty r`. This module proves the other direction of the walk. A `getAncestor`
run returns an ancestor of its start node (`getAncestor_run_above`). Each step moves to the
parent that the block of the current node names. The walk starts at a node with a valid
status.

So `is_ancestor` (`:355`) answers `true` at a decided node `d` only for a node below `d`
(`isAncestor_run_true_below`). `storeSide_full_below` applies this to the side of an index.
The store puts `i` on `full` only when the supported node of its latest message lies below
`full r`. That message is from a slot after the slot of `r` (`fullSupport_slot_gt`). The
lemma needs a block at the message root with a slot no greater than the message slot.
`validate_on_attestation` checks that bound (`gloas/fork-choice.md:867`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok run_bind_eq_ok
  run_pure_eq_ok fuelLoop_run_inv)
open EthCLLib.Spec (HasherTag MapKind FcMap Step fuelLoop)
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Store Root Slot ForkChoiceNode BeaconBlock ValidatorIndex
  LatestMessage getAncestor isAncestor getParentPayloadStatus getSupportedNode)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- `NodeBelow` is transitive. -/
theorem NodeBelow.trans (store : Store map) (a b c : ForkChoiceNode)
    (hab : NodeBelow store a b) (hbc : NodeBelow store b c) : NodeBelow store a c := by
  induction hbc with
  | refl => exact hab
  | step p q _ hpq ih => exact NodeBelow.step p q ih hpq

/-- A `.next` step of the walk from a node with a valid status moves to an ancestor of that
node. The new node has a valid status. -/
theorem ancStep_run_next_below (store : Store map) (slot : Slot) (m q : ForkChoiceNode)
    (hm : ValidStatus m) {t t' : Store map}
    (h : (ancStep store slot m).run t = .ok (.next q, t')) :
    NodeBelow store q m ∧ ValidStatus q := by
  unfold ancStep at h
  obtain ⟨b, t1, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hlook : FcMap.lookup store.blocks m.root = some b := by
    unfold FcMap.getOrThrow FcMap.getOrThrowKey at hb
    split at hb
    · rename_i v hv
      rw [hv, run_pure_eq_ok _ _ _ _ hb]
    · cases hb
  split at h
  · obtain ⟨ps, t2, hps, h⟩ := run_bind_eq_ok _ _ _ _ h
    have hq := run_pure_eq_ok _ _ _ _ h
    injection hq with hq
    subst hq
    have hedge : NodeEdge store { root := b.parentRoot, payloadStatus := ps } (.pending m.root) :=
      NodeEdge.block _ m.root b t1 t2 hlook rfl hps
    refine ⟨?_, ?_⟩
    · rcases hm with hs | hs | hs
      · have : m = .pending m.root := node_eq_of_root_status _ _ rfl hs
        rw [this]
        exact NodeBelow.step _ _ NodeBelow.refl hedge
      · have : m = .empty m.root := node_eq_of_root_status _ _ rfl hs
        rw [this]
        exact NodeBelow.step _ _ (NodeBelow.step _ _ NodeBelow.refl hedge) (NodeEdge.empty _)
      · have : m = .full m.root := node_eq_of_root_status _ _ rfl hs
        rw [this]
        exact NodeBelow.step _ _ (NodeBelow.step _ _ NodeBelow.refl hedge) (NodeEdge.full _)
    · rcases getParentPayloadStatus_run_decided store _ _ b ps hps with hs | hs
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr hs)
  · cases run_pure_eq_ok _ _ _ _ h

/-- `getAncestor` returns an ancestor of a node with a valid status. -/
theorem getAncestor_run_above (store : Store map) (n : ForkChoiceNode) (slot : Slot)
    (hn : ValidStatus n) {t t' : Store map} {a : ForkChoiceNode}
    (h : (getAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n slot).run t
      = .ok (a, t')) :
    NodeBelow store a n := by
  rw [getAncestor_eq_fuelLoop] at h
  refine fuelLoop_run_inv (fun m => ValidStatus m ∧ NodeBelow store m n)
    (fun a => NodeBelow store a n) n _ ?_ ?_ NodeBelow.refl _ n t t' a ⟨hn, NodeBelow.refl⟩ h
  · intro m q s s' ⟨hm, hmn⟩ hst
    obtain ⟨hqm, hq⟩ := ancStep_run_next_below store slot m q hm hst
    exact ⟨hq, NodeBelow.trans store q m n hqm hmn⟩
  · intro m d s s' ⟨_, hmn⟩ hst
    unfold ancStep at hst
    obtain ⟨b, t1, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
    split at hst
    · obtain ⟨_, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
      cases run_pure_eq_ok _ _ _ _ hst
    · have := run_pure_eq_ok _ _ _ _ hst
      injection this with this
      subst this
      exact hmn

/-- Take a node `n` with a valid status and a decided node `d`. A successful `isAncestor` run
of `n` against `d` that returns `true` puts `n` below `d`. -/
theorem isAncestor_run_true_below (store : Store map) (n d : ForkChoiceNode) (hn : ValidStatus n)
    (hd : d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending) {t t' : Store map}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n d).run t
      = .ok (true, t')) :
    NodeBelow store d n := by
  unfold isAncestor at h
  obtain ⟨b, t1, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨a, t2, ha, h⟩ := run_bind_eq_ok _ _ _ _ h
  have habove := getAncestor_run_above store n b.slot hn ha
  split at h
  · cases run_pure_eq_ok _ _ _ _ h
  · rename_i hroot
    have hv := (run_pure_eq_ok _ _ _ _ h).symm
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hroot
    simp only [Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with hs | hs
    · rw [← node_eq_of_root_status a d hroot hs]
      exact habove
    · exact absurd hs hd

/-- The supported node of a message has a valid status. -/
theorem getSupportedNode_run_valid (store : Store map) (lm : LatestMessage) {u u' : Store map}
    {n : ForkChoiceNode}
    (h : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u
      = .ok (n, u')) :
    ValidStatus n ∧ n.root = lm.root := by
  simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey] at h
  split at h
  · simp only [pure_bind] at h
    rw [run_pure_eq_ok _ _ _ _ h]
    refine ⟨?_, rfl⟩
    split
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · simp only [EthCLLib.Proofs.run_bind] at h
    cases h

/-- An index that the store puts on `full` has a latest message and is not an equivocator.
The supported node of the message lies below `full r`. -/
theorem storeSide_full_below (store : Store map) (r : Root) (i : ValidatorIndex)
    (h : storeSide store r i.toNat = .full) :
    ∃ (lm : LatestMessage) (n : ForkChoiceNode) (u u' : Store map),
      FcMap.lookup store.latestMessages i = some lm ∧
      store.equivocatingIndices.contains i = false ∧
      (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u
        = .ok (n, u') ∧
      NodeBelow store (.full r) n := by
  have hF : supportsVal store (.full r) i = true := by
    unfold storeSide at h
    rw [UInt64.ofNat_toNat] at h
    split at h
    · assumption
    · split at h <;> cases h
  unfold supportsVal at hF
  split at hF
  · rename_i b u hb
    subst hF
    unfold supports at hb
    split at hb
    · cases run_pure_eq_ok _ _ _ _ hb
    · rename_i lm hlm
      split at hb
      · cases run_pure_eq_ok _ _ _ _ hb
      · rename_i heq
        obtain ⟨n, v, hn, ha⟩ := run_bind_eq_ok _ _ _ _ hb
        obtain ⟨hvalid, -⟩ := getSupportedNode_run_valid store lm hn
        refine ⟨lm, n, _, _, hlm, by simpa using heq, hn, ?_⟩
        exact isAncestor_run_true_below store n _ hvalid
          (fun h => payloadStatus_full_ne_pending h) ha
  · cases hF

/-- A latest message whose supported node lies below `full r` is from a slot after the slot
of `r`. The lemma needs a block at the message root with a slot no greater than the message
slot. -/
theorem fullSupport_slot_gt (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (lm : LatestMessage)
    (hmsg : ∀ b, FcMap.lookup store.blocks lm.root = some b → b.slot ≤ lm.slot)
    {u u' : Store map} {n : ForkChoiceNode}
    (hsup : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u
      = .ok (n, u'))
    (hbelow : NodeBelow store (.full r) n) :
    rb.slot < lm.slot := by
  obtain ⟨-, hroot⟩ := getSupportedNode_run_valid store lm hsup
  rcases NodeBelow.slot_gt store hslots r rb hrb n hbelow with hn | ⟨b, hb, hlt⟩
  · -- `n` is `full r`, so the message root is `r` and the decided branch ran.
    subst hn
    have hr : lm.root = r := hroot.symm
    simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey, hr, hrb,
      pure_bind] at hsup
    have hn := run_pure_eq_ok _ _ _ _ hsup
    by_cases hs : rb.slot < lm.slot
    · exact hs
    · rw [if_neg hs] at hn
      have := congrArg ForkChoiceNode.payloadStatus hn
      exact absurd this payloadStatus_full_ne_pending
  · rw [hroot] at hb
    exact UInt64.lt_of_lt_of_le hlt (hmsg b hb)

end

end EthCLSpecs.Proofs.Heze
