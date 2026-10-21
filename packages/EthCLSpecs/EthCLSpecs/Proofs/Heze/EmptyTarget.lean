import EthCLSpecs.Proofs.Heze.FinalityLock

/-!
# `EthCLSpecs.Proofs.Heze.EmptyTarget`: the checkpoint block of a head on the EMPTY side

An honest validator names the checkpoint block of its head as the target of its vote. The
walk of `get_checkpoint_block` (`gloas/fork-choice.md:198`) climbs from the pending node of the
head root to an ancestor. This module puts that ancestor on the EMPTY side of `r` under two
conditions. The head is below `empty r`, and the block of the ancestor is later than the block
at `r` (`checkpointBlock_emptySide`).

## The node tree is a forest of chains

Each node has at most one parent (`NodeEdge.parent_unique`). So two nodes above one node lie
on one chain, and one of them is above the other (`NodeBelow.comparable`).

## Slots grow down the tree

Under `SlotsIncrease`, the block of a node has a slot no greater than the block of a node
below it (`NodeBelow.slot_le`). A successful `getParentPayloadStatus` run read the parent
block, so every node above a node with a block has a block too.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Store Root Epoch ForkChoiceNode BeaconBlock getCheckpointBlock)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- Two nodes above one node lie on one chain: one is above the other. The proof follows the
chain from `x` down to `n`. At each edge, the node `y` is the child itself, or `y` is above
the only parent of the child. -/
theorem NodeBelow.comparable (store : Store map) (x y n : ForkChoiceNode)
    (hx : NodeBelow store x n) (hy : NodeBelow store y n) :
    NodeBelow store x y ∨ NodeBelow store y x := by
  induction hx generalizing y with
  | refl => exact .inr hy
  | step p c _ hpc ih =>
    cases hy with
    | refl => exact .inl (NodeBelow.step p _ ‹_› hpc)
    | step q _ hyq hqc =>
      have e : q = p := NodeEdge.parent_unique store q p c hqc hpc
      subst e
      exact ih y hyq

/-- Under `SlotsIncrease`, the block of a node is no later than the block of a node below
it. The node above has a block when the node below has one. A decided child shares the root
of its parent. A pending child names its parent block, which `getParentPayloadStatus` read. -/
theorem NodeBelow.slot_le (store : Store map) (hslots : SlotsIncrease store)
    (m n : ForkChoiceNode) (h : NodeBelow store m n) (nb : BeaconBlock)
    (hnb : FcMap.lookup store.blocks n.root = some nb) :
    ∃ mb, FcMap.lookup store.blocks m.root = some mb ∧ mb.slot ≤ nb.slot := by
  induction h generalizing nb with
  | refl => exact ⟨nb, hnb, UInt64.le_refl _⟩
  | step p c _ hpc ih =>
    rcases NodeEdge.cases_on_child store p c hpc with
      ⟨hp, -⟩ | ⟨y, b, s, s', hc, hb, hparent, hs⟩
    · -- `c` is decided, and `p` is the pending node of the same root.
      have hroot : p.root = c.root := by rw [hp]; rfl
      exact ih nb (hroot ▸ hnb)
    · -- `c` is `pending y`: the block of `p` is the parent of the block at `y`.
      subst hc
      have e : b = nb := Option.some.inj (hb.symm.trans hnb)
      subst e
      obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent store s s' b _ hs
      obtain ⟨mb, hmb, hle⟩ := ih pb (hparent ▸ hpb)
      exact ⟨mb, hmb, UInt64.le_trans hle (UInt64.le_of_lt (hslots y b pb hb hpb))⟩

/-- A node above `empty r`, other than `empty r`, is above `pending r`: the only edge into
`empty r` starts at `pending r`. -/
theorem NodeBelow.above_empty (store : Store map) (r : Root) (m : ForkChoiceNode)
    (h : NodeBelow store m (.empty r)) : m = .empty r ∨ NodeBelow store m (.pending r) := by
  cases h with
  | refl => exact .inl rfl
  | step p _ hp hpe =>
    have e : p = .pending r := NodeEdge.parent_unique store p _ _ hpe (NodeEdge.empty r)
    subst e
    exact .inr hp

/-- The checkpoint block of a head below `empty r` is a stored block. The head root has a
block: the head is `empty r`, or its block is later than `rb` (`NodeBelow.slot_gt_empty`). The
walk returns a node above the pending node of the head root. That node has a block too
(`NodeBelow.slot_le`). -/
theorem checkpointBlock_block (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (head : ForkChoiceNode)
    (hhead : NodeBelow store (.empty r) head) (e : Epoch) (c : Root) (s s' : Store map)
    (hrun : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store
      head.root e).run s = .ok (c, s')) :
    ∃ cb, FcMap.lookup store.blocks c = some cb := by
  unfold getCheckpointBlock at hrun
  -- The checked start slot of the epoch, then the walk.
  obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
  obtain ⟨m, t, hm, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
  have hmc : m.root = c := (run_pure_eq_ok _ _ _ _ hrun).symm
  have habove : NodeBelow store m (.pending head.root) :=
    getAncestor_run_above store _ _ (Or.inl rfl) hm
  have hhb : ∃ hb, FcMap.lookup store.blocks head.root = some hb := by
    rcases NodeBelow.slot_gt_empty store hslots r rb hrb head hhead with h | ⟨b, hb, -⟩
    · subst h
      exact ⟨rb, hrb⟩
    · exact ⟨b, hb⟩
  obtain ⟨hb, hhb⟩ := hhb
  obtain ⟨mb, hmb, -⟩ := NodeBelow.slot_le store hslots m _ habove hb hhb
  exact ⟨mb, hmc ▸ hmb⟩

/-- **The checkpoint block of a head below `empty r` is on the EMPTY side, when it is later
than `r`.** The walk returns a node `m` of the root `c` above the pending node `P` of the head
root (`getAncestor_run_above`). The node `P` is below `empty r`, unless the head is `empty r`.
Then `m` and `empty r` lie on one chain (`NodeBelow.comparable`). A node at or above
`empty r` has a block no later than `rb` (`NodeBelow.slot_le`). So `m` is below `empty r`,
and so is the pending node of `c`. -/
theorem checkpointBlock_emptySide (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (head : ForkChoiceNode)
    (hhead : NodeBelow store (.empty r) head) (e : Epoch) (c : Root) (s s' : Store map)
    (hrun : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store
      head.root e).run s = .ok (c, s'))
    (cb : BeaconBlock) (hcb : FcMap.lookup store.blocks c = some cb) (hlt : rb.slot < cb.slot) :
    OnEmptySide store r c := by
  unfold getCheckpointBlock at hrun
  -- The checked start slot of the epoch, then the walk.
  obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
  obtain ⟨m, t, hm, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
  -- `m.root = c`: `getCheckpointBlock` returns the root of the node it reached.
  have hmc : m.root = c := (run_pure_eq_ok _ _ _ _ hrun).symm
  have habove : NodeBelow store m (.pending head.root) :=
    getAncestor_run_above store _ _ (Or.inl rfl) hm
  -- A node at or above `pending r` has a block no later than `rb`, so it is not `m`.
  have hnot : ¬ NodeBelow store m (.pending r) := fun h => by
    obtain ⟨mb, hmb, hle⟩ := NodeBelow.slot_le store hslots m _ h rb hrb
    rw [hmc, hcb] at hmb
    cases hmb
    exact absurd hle (UInt64.not_le.mpr hlt)
  have hne : m ≠ .empty r := fun h => by
    have : c = r := hmc.symm.trans (congrArg ForkChoiceNode.root h)
    subst this
    rw [hcb] at hrb
    cases hrb
    exact UInt64.lt_irrefl _ hlt
  -- The pending node of the head root is below `empty r`.
  have hP : NodeBelow store (.empty r) (.pending head.root) := by
    by_cases hps : head.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
    · rw [← node_eq_of_root_status head (.pending head.root) rfl hps]
      exact hhead
    · by_cases he : head = .empty r
      · exfalso
        subst he
        exact hnot habove
      · exact NodeBelow.pending_of_decided store r head hhead he hps
  rcases NodeBelow.comparable store _ _ _ hP habove with hbelow | habove'
  · -- `m` is below `empty r`, so the pending node of `c` is.
    unfold OnEmptySide
    rw [← hmc]
    by_cases hps : m.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
    · rw [← node_eq_of_root_status m (.pending m.root) rfl hps]
      exact hbelow
    · exact NodeBelow.pending_of_decided store r m hbelow hne hps
  · rcases NodeBelow.above_empty store r m habove' with h | h
    · exact absurd h hne
    · exact absurd h hnot

end

end EthCLSpecs.Proofs.Heze
