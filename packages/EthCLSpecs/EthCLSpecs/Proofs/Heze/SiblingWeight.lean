import EthCLSpecs.Proofs.Heze.HeadReach
import EthCLSpecs.Proofs.Heze.FullSupport
import EthCLSpecs.Proofs.Heze.PayloadRaceRefines

/-!
# `EthCLSpecs.Proofs.Heze.SiblingWeight`: two children of one node share no support

`PayloadRaceRefines.lean` proves that no latest message supports both the EMPTY and the FULL
node of one block. The `getHead` walk compares every pair of viable children of a node. So this
module proves the general fact: no latest message supports two distinct children of one node of
the node tree.

- `NodeBelow.comparable`: two ancestors of one node lie on one chain. Each node has one parent
  (`NodeEdge.parent_unique`).
- `NodeBelow.walkPot_le`: the walk potential (`HeadReach.lean`) does not rise along a path. So
  the node tree has no cycle.
- `NodeEdge.siblings_disjoint`: no node lies below two distinct children of one node.
- `isAncestor_run_true_below_any`: `is_ancestor` (`gloas/fork-choice.md:406`) answers `true`
  only for a node below its target, at a pending target too.
- `supportsVal_siblings_exclusive`: the score of two distinct children counts disjoint sets of
  indices.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Store Root ForkChoiceNode BeaconBlock ValidatorIndex isAncestor)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- **No node lies below two distinct children of one node.** The two children are on one
chain (`NodeBelow.comparable`). Each node has one parent, so the parent of the lower child lies
below the upper child. The edge from that parent to the upper child then closes a cycle. The
walk potential falls along each edge, so no cycle exists. -/
theorem NodeEdge.siblings_disjoint [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {x a z m : ForkChoiceNode} (hxa : NodeEdge store x a)
    (hxz : NodeEdge store x z) (hne : a ≠ z) (hx : (FcMap.lookup store.blocks x.root).isSome)
    (ham : NodeBelow store a m) (hzm : NodeBelow store z m) : False := by
  -- Below the upper child `u`, the lower child `w` reaches the parent `x` of `u`. The edge from
  -- `x` to `w` lowers the potential, so `x` cannot lie below `w`.
  have key : ∀ u w, NodeEdge store x u → NodeEdge store x w → u ≠ w →
      NodeBelow store w u → False := by
    intro u w hxu hxw huw hwu
    cases hwu with
    | refl => exact huw rfl
    | step p _ hwp hpu =>
      have hpx : p = x := NodeEdge.parent_unique store p x u hpu hxu
      subst hpx
      obtain ⟨hw, hlt⟩ := NodeEdge.walkPot_lt store hslots hxw hx
      have hle := (NodeBelow.walkPot_le store hslots hwp hw).2
      omega
  rcases NodeBelow.comparable store a z m ham hzm with h | h
  · exact key z a hxz hxa (Ne.symm hne) h
  · exact key a z hxa hxz hne h

/-- **`is_ancestor` answers `true` only below its target.** A pending target counts every
node of its root: the walk reaches a node at the target root, and the pending node of that
root is above each of its three nodes. -/
theorem isAncestor_run_true_below_any (store : Store map) (n d : ForkChoiceNode)
    (hn : ValidStatus n) {t t' : Store map}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n d).run t
      = .ok (true, t')) :
    NodeBelow store d n := by
  by_cases hd : d.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
  · have hdd : d = .pending d.root := node_eq_of_root_status _ _ rfl hd
    unfold isAncestor at h
    obtain ⟨b, t1, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨a, t2, ha, h⟩ := run_bind_eq_ok _ _ _ _ h
    have habove := getAncestor_run_above store n b.slot hn ha
    have hva : ValidStatus a := by
      -- The walk returns a node of the tree: an ancestor of a valid node keeps a valid status.
      rw [getAncestor_eq_fuelLoop] at ha
      exact EthCLLib.Proofs.fuelLoop_run_inv ValidStatus ValidStatus n _
        (fun m q s s' hm hst => (ancStep_run_next_below store b.slot m q hm hst).2)
        (fun m dd s s' hm hst => by
          unfold ancStep at hst
          obtain ⟨_, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
          split at hst
          · obtain ⟨_, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
            cases run_pure_eq_ok _ _ _ _ hst
          · have := run_pure_eq_ok _ _ _ _ hst
            injection this with this
            exact this ▸ hm) hn _ n t1 t2 a hn ha
    split at h
    · cases run_pure_eq_ok _ _ _ _ h
    · rename_i hroot
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hroot
      have hpa : NodeBelow store (.pending a.root) a := by
        rcases hva with hs | hs | hs
        · have e := node_eq_of_root_status a (.pending a.root) rfl hs
          rw [e]
          exact .refl
        · have e := node_eq_of_root_status a (.empty a.root) rfl hs
          rw [e]
          exact .step _ _ .refl (NodeEdge.empty _)
        · have e := node_eq_of_root_status a (.full a.root) rfl hs
          rw [e]
          exact .step _ _ .refl (NodeEdge.full _)
      rw [hdd, ← hroot]
      exact NodeBelow.trans store _ _ _ hpa habove
  · exact isAncestor_run_true_below store n d hn hd h

/-- The value of a successful `getSupportedNode` run does not depend on the runner state: it
reads the block at the message root. -/
theorem getSupportedNode_run_val (store : Store map) (lm : EthCLSpecs.Heze.LatestMessage)
    {u₁ u₁' u₂ u₂' : Store map} {m₁ m₂ : ForkChoiceNode}
    (h₁ : (EthCLSpecs.Heze.getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
      store lm).run u₁ = .ok (m₁, u₁'))
    (h₂ : (EthCLSpecs.Heze.getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
      store lm).run u₂ = .ok (m₂, u₂')) : m₁ = m₂ := by
  simp only [EthCLSpecs.Heze.getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey] at h₁ h₂
  split at h₁
  · rename_i b hb
    rw [hb] at h₂
    simp only [pure_bind] at h₁ h₂
    exact (run_pure_eq_ok _ _ _ _ h₁).trans (run_pure_eq_ok _ _ _ _ h₂).symm
  · simp only [EthCLLib.Proofs.run_bind] at h₁
    cases h₁

/-- A supported index has a message whose supported node lies below the target. -/
theorem supportsVal_below (store : Store map) (d : ForkChoiceNode) (i : ValidatorIndex)
    (h : supportsVal store d i = true) :
    ∃ (lm : EthCLSpecs.Heze.LatestMessage) (m : ForkChoiceNode) (u u' : Store map),
      FcMap.lookup store.latestMessages i = some lm ∧
      (EthCLSpecs.Heze.getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
        store lm).run u = .ok (m, u') ∧
      NodeBelow store d m := by
  unfold supportsVal at h
  split at h
  · rename_i b s hr
    subst h
    unfold supports at hr
    split at hr
    · cases run_pure_eq_ok _ _ _ _ hr
    · rename_i lm hl
      split at hr
      · cases run_pure_eq_ok _ _ _ _ hr
      · obtain ⟨m, u, hm, hr⟩ := run_bind_eq_ok _ _ _ _ hr
        obtain ⟨hv, -⟩ := getSupportedNode_run_valid store lm hm
        exact ⟨lm, m, _, u, hl, hm, isAncestor_run_true_below_any store m d hv hr⟩
  · cases h

/-- **Two distinct children count disjoint indices.** Take an index that both children count.
It has one message, so it has one supported node (`getSupportedNode_run_val`). That node lies
below both children (`supportsVal_below`). But no node lies below two distinct children of one
node (`NodeEdge.siblings_disjoint`). -/
theorem supportsVal_siblings_exclusive [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {x a z : ForkChoiceNode} (hxa : NodeEdge store x a)
    (hxz : NodeEdge store x z) (hne : a ≠ z) (hx : (FcMap.lookup store.blocks x.root).isSome)
    (i : ValidatorIndex) (ha : supportsVal store a i = true) (hz : supportsVal store z i = true) :
    False := by
  obtain ⟨lm, m, u, u', hl, hm, ham⟩ := supportsVal_below store a i ha
  obtain ⟨lm', m', w, w', hl', hm', hzm⟩ := supportsVal_below store z i hz
  rw [hl] at hl'
  injection hl' with hl'
  subst hl'
  have e := getSupportedNode_run_val store lm hm hm'
  subst e
  exact NodeEdge.siblings_disjoint store hslots hxa hxz hne hx ham hzm

end

end EthCLSpecs.Proofs.Heze
