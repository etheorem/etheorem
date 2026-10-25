import EthCLSpecs.Proofs.Heze.PayloadRaceExec
import EthCLSpecs.Proofs.Heze.HeadBelowJustified

/-!
# `EthCLSpecs.Proofs.Heze.FinalityLock`: a finalized checkpoint locks the payload race

A block `r` has two decided nodes in the node tree, `empty r` and `full r`
(`gloas/fork-choice.md`, `get_node_children`). A block `c` is on the EMPTY side of `r` when its
pending node lies below `empty r` (`OnEmptySide`). It is on the FULL side when its pending
node lies below `full r` (`OnFullSide`).

## The two sides are disjoint

Each node has at most one parent (`NodeEdge.parent_unique`). So a node below both `empty r`
and `full r` would put one of the two nodes below the other. The only parent of a decided
node is `pending r`. Under `SlotsIncrease`, each block below a decided node of `r` has a
greater slot than the block at `r`. So `pending r` is not below `full r` or `empty r`.
`below_emptySide_not_full` states the result for every node below a block on the EMPTY side.

## The checkpoint block

`get_checkpoint_block` (`:198`) walks `get_ancestor` from the pending node of a root. The
walk returns an ancestor of its start (`getAncestor_run_above`). So a run that returns the
root `f` found a node of `f` above the start. When `f` is on the EMPTY side, the start is on
the EMPTY side too (`emptySide_of_checkpointBlock`).

## The lock

An honest node finalizes a checkpoint on the EMPTY side of `r`. Then each later head avoids
the FULL side, or one of two other cases holds (`honestNode_finality_lock`):

- Two distinct blocks or headers share a root (`RootCollision`).
- The justified checkpoint of the later store does not lead to the finalized root at the
  finalized epoch (`Conflicting`). The store updates its justified and finalized checkpoints
  separately, so this theorem does not exclude the case.

Otherwise the justified root is on the EMPTY side, and `get_head` starts its walk there
(`getHead_run_below_justified`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState LawfulFcMap run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  getHead getCheckpointBlock ExecutionPayload Transaction ExecutionRequests SignedInclusionList)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The block `c` lies on the EMPTY side of `r`: its pending node is below `empty r`. -/
def OnEmptySide (store : Store map) (r c : Root) : Prop :=
  NodeBelow store (.empty r) (.pending c)

/-- The block `c` lies on the FULL side of `r`: its pending node is below `full r`. -/
def OnFullSide (store : Store map) (r c : Root) : Prop :=
  NodeBelow store (.full r) (.pending c)

/-- The start of an edge has one of the three payload statuses. A pending node starts the
edges to its decided nodes. A block edge starts at the status that `getParentPayloadStatus`
returns, which is EMPTY or FULL. -/
theorem NodeEdge.validStatus_parent (store : Store map) (p c : ForkChoiceNode)
    (h : NodeEdge store p c) : ValidStatus p := by
  rcases NodeEdge.cases_on_child store p c h with ⟨hp, -⟩ | ⟨-, b, s, s', -, -, -, hs⟩
  · exact Or.inl (by rw [hp]; rfl)
  · rcases getParentPayloadStatus_run_decided store s s' b _ hs with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- The top node of a chain is the bottom node, or it has one of the three payload
statuses. -/
theorem NodeBelow.eq_or_validStatus (store : Store map) (x y : ForkChoiceNode)
    (h : NodeBelow store x y) : x = y ∨ ValidStatus x := by
  induction h with
  | refl => exact Or.inl rfl
  | step p _ _ hpc ih =>
    rcases ih with rfl | hx
    · exact Or.inr (NodeEdge.validStatus_parent store _ _ hpc)
    · exact Or.inr hx

/-- Under `SlotsIncrease`, no node below `empty r` is below `full r`.

The induction follows the chain down from `empty r`. At `empty r`, its only parent is
`pending r`, and `pending r` is not below `full r`. A lower node `c` below `full r` is `full r`
itself, or its only parent is below `full r` too. The node `full r` has the parent
`pending r`, which is not below `empty r`. -/
theorem NodeBelow.empty_not_full (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (n : ForkChoiceNode)
    (hn : NodeBelow store (.empty r) n) : ¬ NodeBelow store (.full r) n := by
  -- `pending r` is below neither decided node: its block would have a slot above its own.
  have hpend : ∀ d : ForkChoiceNode, d.root = r →
      d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending →
      ¬ NodeBelow store d (.pending r) := by
    intro d hd hdec h
    rcases NodeBelow.slot_gt_decided store hslots d hdec rb (hd ▸ hrb) _ h with he | ⟨b, hb, hlt⟩
    · exact hdec (congrArg ForkChoiceNode.payloadStatus he).symm
    · rw [show (ForkChoiceNode.pending r).root = r from rfl, hrb] at hb
      cases hb
      exact UInt64.lt_irrefl _ hlt
  induction hn with
  | refl =>
    intro h
    cases h with
    | step p _ hp hpe =>
      have : p = .pending r := NodeEdge.parent_unique store p _ _ hpe (NodeEdge.empty r)
      subst this
      exact hpend (.full r) rfl payloadStatus_full_ne_pending hp
  | step p c hp hpc ih =>
    intro h
    cases h with
    | refl =>
      have : p = .pending r := NodeEdge.parent_unique store p _ _ hpc (NodeEdge.full r)
      subst this
      exact hpend (.empty r) rfl payloadStatus_empty_ne_pending hp
    | step q _ hq hqc => exact ih (NodeEdge.parent_unique store p q c hpc hqc ▸ hq)

/-- Under `SlotsIncrease`, a node below a block on the EMPTY side of `r` is not below
`full r`. -/
theorem below_emptySide_not_full (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (c : Root)
    (n : ForkChoiceNode) (hc : OnEmptySide store r c)
    (hn : NodeBelow store (.pending c) n) : ¬ NodeBelow store (.full r) n :=
  NodeBelow.empty_not_full store hslots r rb hrb n (NodeBelow.trans store _ _ _ hc hn)

/-- Under `SlotsIncrease`, a block on the EMPTY side of `r` is not on the FULL side. -/
theorem onEmptySide_not_full (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) (c : Root)
    (hc : OnEmptySide store r c) : ¬ OnFullSide store r c :=
  below_emptySide_not_full store hslots r rb hrb c _ hc NodeBelow.refl

/-- The checkpoints `j` and `f` conflict in `store`: no run of `getCheckpointBlock` from the
root of `j` at the epoch of `f` returns the root of `f`. A walk that rejects counts as a
conflict. -/
def Conflicting (store : Store map) (j f : Checkpoint) : Prop :=
  ∀ s s', (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store j.root
    f.epoch).run s ≠ .ok (f.root, s')

/-- A checkpoint block on the EMPTY side of `r` puts its start on the EMPTY side.

The walk returns a node `m` of the root `f` above the pending node of `j`. The node `m` is the
start itself, or it has a valid status. Each valid node of `f` is `pending f` or one of its
children, so it lies below `empty r`. -/
theorem emptySide_of_checkpointBlock (store : Store map) (r : Root) (j f : Checkpoint)
    (hf : OnEmptySide store r f.root) (s s' : Store map)
    (h : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store j.root
      f.epoch).run s = .ok (f.root, s')) :
    OnEmptySide store r j.root := by
  unfold getCheckpointBlock at h
  -- The checked start slot of the epoch, then the walk.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨m, t, hm, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- `m.root = f.root`: `getCheckpointBlock` returns the root of the node it reached.
  have hroot : m.root = f.root := (run_pure_eq_ok _ _ _ _ h).symm
  have habove : NodeBelow store m (.pending j.root) :=
    getAncestor_run_above store _ _ (Or.inl rfl) hm
  rcases NodeBelow.eq_or_validStatus store _ _ habove with he | hs
  · -- The walk stopped at its start, so `j` and `f` share the root.
    have : j.root = f.root := (congrArg ForkChoiceNode.root he).symm.trans hroot
    unfold OnEmptySide
    rw [this]
    exact hf
  · refine NodeBelow.trans store _ m _ ?_ habove
    rcases hs with hs | hs | hs
    · rw [node_eq_of_root_status m (.pending f.root) hroot hs]
      exact hf
    · rw [node_eq_of_root_status m (.empty f.root) hroot hs]
      exact NodeBelow.step _ _ hf (NodeEdge.empty f.root)
    · rw [node_eq_of_root_status m (.full f.root) hroot hs]
      exact NodeBelow.step _ _ hf (NodeEdge.full f.root)

variable [Config] [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] [LawfulFcMap map Root]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- The finality lock. An honest node starts at the anchor store `s0` and runs a trace to
`s`. The store `s` holds the block `rb` at `r`, and the finalized block of `s` is on the
EMPTY side of `r`. The anchor is no later than `rb`. A second trace runs from `s` to `s'`.
Then one of three cases holds:

- The head that `getHead` returns at `s'` is not below `full r`.
- A root collision exists.
- The justified checkpoint of `s'` conflicts with the finalized checkpoint of `s`.

`SlotInv` holds at `s` and `s'` (`NodeTrace.slotInv`). `NodeBelow.transfer` moves the EMPTY
side from `s` to `s'`. When the checkpoints do not conflict, the justified root is on the
EMPTY side too (`emptySide_of_checkpointBlock`), and the head is below it. -/
theorem honestNode_finality_lock {anchorState : BeaconState} {a : BeaconBlock}
    {s0 s s' : Store map} {es es' : List TraceEvent}
    {arr arr' : List (SignedInclusionList × UInt64)}
    (hanchor : EthCLSpecs.Heze.getForkchoiceStore (pureState anchorState) a = .ok s0)
    (hself : a.parentRoot ≠ htr a)
    (h1 : NodeTrace s0 es arr s) (h2 : NodeTrace s es' arr' s')
    (hev : ∀ e, TraceEvent.handler e ∈ es ++ es' → e.NotAtAnchorParent a)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup s.blocks r = some rb)
    (hslot : a.slot ≤ rb.slot)
    (hside : OnEmptySide s r s.finalizedCheckpoint.root)
    (runner t : Store map) (head : ForkChoiceNode)
    (hhead : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s').run runner
      = .ok (head, t)) :
    RootCollision ∨ Conflicting s' s'.justifiedCheckpoint s.finalizedCheckpoint ∨
      ¬ NodeBelow s' (.full r) head := by
  by_cases hrc : RootCollision
  · exact Or.inl hrc
  have h0 := SlotInv.anchor anchorState a s0 hanchor hself
  have hinv : SlotInv a s :=
    (NodeTrace.slotInv hw h1 h0 fun e he => hev e (List.mem_append_left _ he)).resolve_right hrc
  have hinv' : SlotInv a s' := (NodeTrace.slotInv hw (h1.append h2) h0 hev).resolve_right hrc
  by_cases hcol : HtrCollision BeaconBlock
  · exact Or.inl (Or.inr hcol)
  -- The finalized block is in `s`, so it stays in `s'`.
  have hfin : ∃ x, FcMap.lookup s'.blocks s.finalizedCheckpoint.root = some x := by
    rcases NodeBelow.slot_gt_empty s hinv.slots r rb hrb _ hside with he | ⟨x, hx, -⟩
    · exact absurd (congrArg ForkChoiceNode.payloadStatus he) payloadStatus_empty_ne_pending.symm
    · exact NodeTrace.blocks_persist h2 _ x hx
  have hside' : OnEmptySide s' r s.finalizedCheckpoint.root :=
    NodeBelow.transfer s s' hinv.slots r rb hrb a
      (fun _ _ _ hx hy => SlotInv.block_eq hinv hinv' hcol hx hy)
      (fun k x hx => hinv'.parentIn k x hx) hslot _ hside (Or.inr hfin)
  by_cases hconf : Conflicting s' s'.justifiedCheckpoint s.finalizedCheckpoint
  · exact Or.inr (Or.inl hconf)
  -- Not conflicting: some run of the walk returns the finalized root.
  obtain ⟨u, u', hu⟩ : ∃ u u', (getCheckpointBlock
      (StoreTransition := ForkChoiceStoreRun (Store map)) s' s'.justifiedCheckpoint.root
      s.finalizedCheckpoint.epoch).run u = .ok (s.finalizedCheckpoint.root, u') :=
    Classical.byContradiction fun hne => hconf fun u u' hu => hne ⟨u, u', hu⟩
  have hj := emptySide_of_checkpointBlock s' r _ _ hside' u u' hu
  obtain ⟨rb', hrb'⟩ := NodeTrace.blocks_persist h2 r rb hrb
  exact Or.inr (Or.inr (below_emptySide_not_full s' hinv'.slots r rb' hrb' _ head hj
    (getHead_run_below_justified s' runner t head hhead)))

end

end EthCLSpecs.Proofs.Heze
