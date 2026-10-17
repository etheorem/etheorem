import EthCLSpecs.Proofs.Heze.InclusionDichotomy

/-!
# `EthCLSpecs.Proofs.Heze.HeadAvoidsFull`: the head does not extend a failed payload

`PayloadTiebreak.lean` proves one step of the `getHead` walk. Take a block from the
previous slot with an unverified payload or a recorded `false` answer. At the pending
node of that block, the walk continues from the EMPTY node, when the EMPTY node is
viable. This module lifts the step to the whole walk. The head that `getHead` returns is
not the FULL node of the block, and it is not below it. So the head does not extend the
payload. The theorem holds whether or not the walk reaches the block.

## The node tree

`NodeEdge store p c` states that `c` is a child of `p`, with the three cases of
`get_node_children` (`consensus-specs/specs/gloas/fork-choice.md:614-628`):

- A pending node has its EMPTY node as a child.
- A pending node has its FULL node as a child.
- A decided node has a pending node as a child for each block in the store whose parent
  root is the node's root and whose parent payload status (`getParentPayloadStatus`) is
  the node's status.

The relation is wider than `getNodeChildren`. It ignores the payload verification and the
viable node list that `getHead` filters by. So "not below the FULL node" in this relation
is a stronger statement than "not below it in the tree that `getHead` walks".
`NodeBelow store anc n` is the reflexive, transitive closure: `n` is `anc`, or it lies
below `anc`.

Each node has at most one parent (`NodeEdge.parent_unique`). A decided node has the
pending node of its root. A pending node has the decided node that its block's parent
root and parent payload status name. This fact keeps the walk out of the subtree. A walk
that enters the subtree below the FULL node must first visit the FULL node. The walk can
reach the FULL node only from the pending node of the block. There the step goes to
EMPTY.

## The viable node list

`get_head` keeps only the children in the list that `get_filtered_node_tree` returns
(`consensus-specs/specs/gloas/fork-choice.md:638-672`). The list can hold the FULL node of
the block and not its EMPTY node. That happens when the FULL node is a viable leaf and
every branch below the EMPTY node fails the checkpoint checks of `filter_node_tree`. Then
`get_head` moves to the FULL node, whatever the inclusion-list answer. So the theorems
take `EmptyViableWithFull`: in every list that `getFilteredNodeTree` returns, the FULL node
of the block is there only with the EMPTY node.

## The walk

`getHead` reads the viable node list. With an empty list, it returns the EMPTY node of the
justified root. Otherwise it runs `fuelLoop` over `headLoopBody`
(`getHead_eq_fuelLoop_headLoopBody`). A `.next` step moves to a viable child of the
current node (`headLoopBody_run_next_edge`). `getNodeChildren` returns children in the
node tree (`getNodeChildren_run_edge`), and the `betterOf` fold returns one of them
(`betterOf_run_mem`). A `.done` step returns the current node (`headLoopBody_run_done`).
`headLoop_run_avoids_full` keeps "not below the FULL node" as a loop invariant with
`fuelLoop_run_inv`.

`getNodeChildren` reads the blocks through `FcMap.fold`. The step from a fold entry to a
lookup is `LawfulFcMap.mem_fold_push`, so the walk theorems take `[LawfulFcMap map Root]`.

The loop threads a runner state through its steps. The steps read only the `store`
argument. So the step at the pending node must hold at any runner state. The
`PayloadTiebreak.lean` lemmas take their hypotheses at `store` and conclude at any runner
state (`getCurrentSlot_run_state`).

## The start of the walk

The walk starts at the pending node of the justified root, and its fuel-out value is the
same node. `getHead_run_avoids_full` assumes that this node is not below the FULL node.
The EMPTY node of the justified root is then not below it either
(`not_nodeBelow_empty_of_pending`). `not_nodeBelow_full_of_slot_le` gives the assumption
from slots. It needs `SlotsIncrease`: each block in the store has a greater slot than its
parent. Then a node whose block has a slot no greater than the slot of the block is not
below the FULL node. `SlotsIncrease.lean` proves `SlotsIncrease` along a trace of handler
runs.

## What the theorems say about the chain

`nodeBelow_full_of_full_child` shows that the relation covers the case that matters: a
block on the FULL edge of the block is below the FULL node. So a head that is not below
the FULL node is not such a block, and no block below one.

`inclusionList_missing_tx_head_avoids_full` composes the result with
`inclusionList_missing_tx`. Take a missing transaction with no valid omission, under
`DichotomyHypotheses`. At every `LaterStore` that satisfies `EmptyViableWithFull`, the
head avoids the payload.

The theorems are about one store. No theorem here models the proposer.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  run_bind_eq_ok run_pure_eq_ok forIn_run_inv foldlM_run_mem fuelLoop_run_inv LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap Step fuelLoop CryptoBackend ExecutionEngine)
open EthCLSpecs.Heze (Preset Config Store BeaconState Root ForkChoiceNode BeaconBlock
  ExecutionPayload ExecutionRequests Transaction InclusionList SignedInclusionList
  SignedExecutionPayloadEnvelope ValidatorIndex getCurrentSlot isPayloadVerified
  getParentPayloadStatus getNodeChildren getFilteredNodeTree getHead
  onExecutionPayloadEnvelope)

/-- The three payload statuses are distinct. The statuses are `UInt8` constants, so
`decide` evaluates them. -/
theorem payloadStatus_empty_ne_pending :
    EthCLSpecs.Heze.Const.payloadStatusEmpty ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
  decide

/-- The three payload statuses are distinct. -/
theorem payloadStatus_full_ne_pending :
    EthCLSpecs.Heze.Const.payloadStatusFull ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
  decide

/-- The three payload statuses are distinct. -/
theorem payloadStatus_empty_ne_full :
    EthCLSpecs.Heze.Const.payloadStatusEmpty ≠ EthCLSpecs.Heze.Const.payloadStatusFull := by
  decide

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- One edge of the node tree of `store`: `c` is a child of `p`. The three constructors
are the three cases of `get_node_children`, without the payload verification and without
the viable-node filter of `get_head`. The `block` case asks for one successful run of
`getParentPayloadStatus` that returns the status of `p`. The runner states `s` and `s'`
do not matter: the value of a successful run depends only on `store` and the block
(`getParentPayloadStatus_run_val`). -/
inductive NodeEdge (store : Store map) : ForkChoiceNode → ForkChoiceNode → Prop
  | empty (root : Root) : NodeEdge store (.pending root) (.empty root)
  | full (root : Root) : NodeEdge store (.pending root) (.full root)
  | block (parent : ForkChoiceNode) (root : Root) (b : BeaconBlock) (s s' : Store map) :
      FcMap.lookup store.blocks root = some b →
      b.parentRoot = parent.root →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run s
        = .ok (parent.payloadStatus, s') →
      NodeEdge store parent (.pending root)

/-- `n` is `anc` or lies below it in the node tree of `store`: a chain of `NodeEdge`
steps leads from `anc` to `n`. -/
inductive NodeBelow (store : Store map) (anc : ForkChoiceNode) : ForkChoiceNode → Prop
  | refl : NodeBelow store anc anc
  | step (p c : ForkChoiceNode) : NodeBelow store anc p → NodeEdge store p c →
      NodeBelow store anc c

omit [HasherTag] in
/-- Two nodes with the same root and the same payload status are equal. -/
theorem node_eq_of_root_status (p q : ForkChoiceNode) (hroot : p.root = q.root)
    (hstatus : p.payloadStatus = q.payloadStatus) : p = q := by
  cases p
  cases q
  simp_all

/-- The value of a successful `getParentPayloadStatus` run does not depend on the runner
state. -/
theorem getParentPayloadStatus_run_val (store s₁ s₁' s₂ s₂' : Store map) (b : BeaconBlock)
    (v₁ v₂ : UInt8)
    (h₁ : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
      store b).run s₁ = .ok (v₁, s₁'))
    (h₂ : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
      store b).run s₂ = .ok (v₂, s₂')) :
    v₁ = v₂ := by
  simp only [getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey] at h₁ h₂
  split at h₁
  · rename_i parent hparent
    rw [hparent] at h₂
    simp only [pure_bind] at h₁ h₂
    exact (run_pure_eq_ok _ _ _ _ h₁).trans (run_pure_eq_ok _ _ _ _ h₂).symm
  · simp only [run_bind] at h₁
    cases h₁

/-- The two shapes of an edge. An edge that ends at an EMPTY or FULL node starts at the
pending node of the same root. An edge that ends at a pending node comes from a block. -/
theorem NodeEdge.cases_on_child (store : Store map) (p c : ForkChoiceNode)
    (h : NodeEdge store p c) :
    (p = .pending c.root ∧ (c = .empty c.root ∨ c = .full c.root)) ∨
      ∃ (root : Root) (b : BeaconBlock) (s s' : Store map),
        c = .pending root ∧ FcMap.lookup store.blocks root = some b ∧
        b.parentRoot = p.root ∧
        (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store b).run s = .ok (p.payloadStatus, s') := by
  cases h with
  | empty root => exact Or.inl ⟨rfl, Or.inl rfl⟩
  | full root => exact Or.inl ⟨rfl, Or.inr rfl⟩
  | block _ root b s s' hb hparent hstatus =>
    exact Or.inr ⟨root, b, s, s', rfl, hb, hparent, hstatus⟩

/-- Every node has at most one parent in the node tree. A decided node has the pending
node of its root. A pending node has the node that its block's parent root and parent
payload status name. -/
theorem NodeEdge.parent_unique (store : Store map) (p q c : ForkChoiceNode)
    (hp : NodeEdge store p c) (hq : NodeEdge store q c) : p = q := by
  rcases NodeEdge.cases_on_child store p c hp with
    ⟨hp', hcp⟩ | ⟨rp, bp, sp, sp', hcp, hbp, hrp, hsp⟩
  · rcases NodeEdge.cases_on_child store q c hq with ⟨hq', _⟩ | ⟨rq, _, _, _, hcq, _⟩
    · exact hp'.trans hq'.symm
    · -- `c` is EMPTY or FULL on one side and PENDING on the other.
      exfalso
      have hstatus := congrArg ForkChoiceNode.payloadStatus hcq
      rcases hcp with hc | hc <;> rw [hc] at hstatus
      · exact payloadStatus_empty_ne_pending hstatus
      · exact payloadStatus_full_ne_pending hstatus
  · rcases NodeEdge.cases_on_child store q c hq with
      ⟨_, hcq⟩ | ⟨rq, bq, sq, sq', hcq, hbq, hrq, hsq⟩
    · exfalso
      have hstatus := congrArg ForkChoiceNode.payloadStatus hcp
      rcases hcq with hc | hc <;> rw [hc] at hstatus
      · exact payloadStatus_empty_ne_pending hstatus
      · exact payloadStatus_full_ne_pending hstatus
    · have hroot : rp = rq := by
        have := congrArg ForkChoiceNode.root (hcp.symm.trans hcq)
        exact this
      subst hroot
      have hb : bp = bq := Option.some.inj (hbp.symm.trans hbq)
      subst hb
      apply node_eq_of_root_status
      · exact hrp.symm.trans hrq
      · exact getParentPayloadStatus_run_val store sp sp' sq sq' bp _ _ hsp hsq

/-- A block on the FULL edge of `r` is below the FULL node of `r`: its pending node is a
child of that FULL node. So a theorem that excludes the nodes below the FULL node of `r`
excludes every block that extends the payload of `r`. -/
theorem nodeBelow_full_of_full_child (store : Store map) (r c : Root) (b : BeaconBlock)
    (s s' : Store map) (hb : FcMap.lookup store.blocks c = some b) (hparent : b.parentRoot = r)
    (hstatus : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
      store b).run s = .ok (EthCLSpecs.Heze.Const.payloadStatusFull, s')) :
    NodeBelow store (.full r) (.pending c) :=
  NodeBelow.step _ _ NodeBelow.refl (NodeEdge.block (.full r) c b s s' hb hparent hstatus)

/-- The EMPTY node of `j` is below the FULL node of `r` only through the pending node of
`j`, its one parent. So when the pending node of `j` is not below the FULL node, the EMPTY
node of `j` is not below it either. -/
theorem not_nodeBelow_empty_of_pending (store : Store map) (r j : Root)
    (h : ¬ NodeBelow store (.full r) (.pending j)) :
    ¬ NodeBelow store (.full r) (.empty j) := by
  intro hbelow
  generalize hn : ForkChoiceNode.empty j = n at hbelow
  cases hbelow with
  | refl => exact payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus hn)
  | step p c hp hpc =>
    subst hn
    exact h (NodeEdge.parent_unique store p _ _ hpc (NodeEdge.empty j) ▸ hp)

/-- Every block in `store` whose parent is in `store` has a greater slot than its
parent. -/
def SlotsIncrease (store : Store map) : Prop :=
  ∀ (root : Root) (b pb : BeaconBlock), FcMap.lookup store.blocks root = some b →
    FcMap.lookup store.blocks b.parentRoot = some pb → pb.slot < b.slot

/-- Slots grow below the FULL node of `r`, under `SlotsIncrease`. Every node below the
FULL node, other than the FULL node itself, has a block with a greater slot than the
block at `r`. -/
theorem NodeBelow.slot_gt (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rootBlock : BeaconBlock) (hblock : FcMap.lookup store.blocks r = some rootBlock)
    (n : ForkChoiceNode) (h : NodeBelow store (.full r) n) :
    n = .full r ∨
      ∃ b : BeaconBlock, FcMap.lookup store.blocks n.root = some b ∧ rootBlock.slot < b.slot := by
  induction h with
  | refl => exact Or.inl rfl
  | step p c _ hpc ih =>
    right
    rcases NodeEdge.cases_on_child store p c hpc with ⟨hp, _⟩ | ⟨y, b, s, s', hc, hb, hparent, hs⟩
    · -- `c` is decided, and `p` is the pending node of the same root.
      rcases ih with hfull | ⟨pb, hpb, hlt⟩
      · exfalso
        have hstatus := congrArg ForkChoiceNode.payloadStatus (hfull.symm.trans hp)
        exact payloadStatus_full_ne_pending hstatus
      · have hroot : p.root = c.root := by rw [hp]; rfl
        exact ⟨pb, hroot ▸ hpb, hlt⟩
    · -- `c` is the pending node of a block whose parent root is the root of `p`.
      subst hc
      have hparentBlock : ∃ pb : BeaconBlock, FcMap.lookup store.blocks b.parentRoot = some pb ∧
          rootBlock.slot ≤ pb.slot := by
        rcases ih with hfull | ⟨pb, hpb, hlt⟩
        · refine ⟨rootBlock, ?_, UInt64.le_refl _⟩
          rw [hparent, hfull]
          exact hblock
        · exact ⟨pb, hparent ▸ hpb, UInt64.le_of_lt hlt⟩
      obtain ⟨pb, hpb, hle⟩ := hparentBlock
      exact ⟨b, hb, UInt64.lt_of_le_of_lt hle (hslots y b pb hb hpb)⟩

/-- A sufficient condition from slots, under `SlotsIncrease`. Take a node other than the
FULL node of `r`, whose block has a slot no greater than the block at `r`. That node is
not below the FULL node of `r`. This discharges the justified-root hypothesis of
`getHead_run_avoids_full`. -/
theorem not_nodeBelow_full_of_slot_le (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rootBlock : BeaconBlock) (hblock : FcMap.lookup store.blocks r = some rootBlock)
    (n : ForkChoiceNode) (nb : BeaconBlock) (hnb : FcMap.lookup store.blocks n.root = some nb)
    (hle : nb.slot ≤ rootBlock.slot) (hne : n ≠ .full r) :
    ¬ NodeBelow store (.full r) n := by
  intro h
  rcases NodeBelow.slot_gt store hslots r rootBlock hblock n h with hfull | ⟨b, hb, hlt⟩
  · exact hne hfull
  · have hb' : b = nb := Option.some.inj (hb.symm.trans hnb)
    subst hb'
    exact absurd hle (UInt64.not_le.mpr hlt)

variable [Config]

/-- The FULL node of `root` is in a viable node list only with the EMPTY node of `root`.
The statement covers every successful run of `getFilteredNodeTree` at `store`, from any
runner state.

The spec does not make this true, so it stays a premise. `filter_node_tree` decides each
child of the pending node from that child's own subtree. The FULL node stays in the list
when a block built on the payload passes the justified and finalized checks. The EMPTY node
drops out when it has children and none of them passes. As a leaf, it drops out when the
block at `root` fails the checks. Then `get_head` moves from the pending node of `root` to its
FULL node. -/
def EmptyViableWithFull (store : Store map) (root : Root) : Prop :=
  ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
    (getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t
      = .ok (nodes, t') →
    nodes.contains (.full root) = true → nodes.contains (.empty root) = true

/-- `betterOf` returns one of its two arguments. -/
theorem betterOf_run_mem (store : Store map) (a b x : ForkChoiceNode) (s s' : Store map)
    (h : (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store a b).run s
      = .ok (x, s')) :
    x = a ∨ x = b := by
  unfold getHead.betterOf at h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · exact Or.inl (run_pure_eq_ok _ _ _ _ h)
  · split at h
    · exact Or.inr (run_pure_eq_ok _ _ _ _ h)
    · split at h
      · exact Or.inl (run_pure_eq_ok _ _ _ _ h)
      · exact Or.inr (run_pure_eq_ok _ _ _ _ h)
      · rw [run_pure_eq_ok _ _ _ _ h]
        split
        · exact Or.inl rfl
        · exact Or.inr rfl

omit [Config] in
/-- Every child that `getNodeChildren` returns is a child of the node in the node tree. -/
theorem getNodeChildren_run_edge [LawfulFcMap map Root] (store s s' : Store map)
    (n : ForkChoiceNode) (cs : Array ForkChoiceNode)
    (h : (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store n).run
      s = .ok (cs, s')) :
    ∀ c ∈ cs, NodeEdge store n c := by
  simp only [getNodeChildren] at h
  split at h
  · -- A pending node: its EMPTY node, and its FULL node when the payload is verified.
    rename_i hpending
    have hn : n = ForkChoiceNode.pending n.root :=
      node_eq_of_root_status _ _ rfl (beq_iff_eq.mp hpending)
    split at h
    · rw [run_pure_eq_ok _ _ _ _ h]
      intro c hc
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
      rw [hn]
      rcases hc with hc | hc <;> subst hc
      · exact NodeEdge.empty n.root
      · exact NodeEdge.full n.root
    · rw [run_pure_eq_ok _ _ _ _ h]
      intro c hc
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
      rw [hn]
      subst hc
      exact NodeEdge.empty n.root
  · -- A decided node: the loop over the block entries keeps the pending nodes of the
    -- blocks on its edge.
    obtain ⟨r, s1, hloop, hret⟩ := run_bind_eq_ok _ _ _ _ h
    rw [run_pure_eq_ok _ _ _ _ hret]
    rw [← Array.forIn_toList] at hloop
    refine forIn_run_inv (fun r => ∀ c ∈ r, NodeEdge store n c) _ _ ?_ #[] s s1 r
      (by simp) hloop
    intro entry hentry acc t t' st hacc hbody
    obtain ⟨root, b⟩ := entry
    have hlookup : FcMap.lookup store.blocks root = some b :=
      (LawfulFcMap.mem_fold_push store.blocks root b).mp hentry
    dsimp only at hbody
    split at hbody
    · rename_i hparent
      obtain ⟨ps, t2, hps, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
      split at hbody
      · rename_i hstatus
        rw [run_pure_eq_ok _ _ _ _ hbody]
        intro c hc
        rcases Array.mem_push.mp hc with hc | hc
        · exact hacc c hc
        · subst hc
          have hps' : ps = n.payloadStatus := (beq_iff_eq.mp hstatus).symm
          exact NodeEdge.block n root b t t2 hlookup (beq_iff_eq.mp hparent) (hps' ▸ hps)
      · rw [run_pure_eq_ok _ _ _ _ hbody]
        exact hacc
    · rw [run_pure_eq_ok _ _ _ _ hbody]
      exact hacc

/-- A `.next` step of the `getHead` loop moves to a child of the current node, and that
child is in the viable node list. -/
theorem headLoopBody_run_next_edge [LawfulFcMap map Root] (store s s' : Store map)
    (nodes : Array ForkChoiceNode) (n c : ForkChoiceNode)
    (h : (headLoopBody store nodes n).run s = .ok (.next c, s')) :
    NodeEdge store n c ∧ nodes.contains c = true := by
  unfold headLoopBody headFold at h
  obtain ⟨cs, s1, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hedge := getNodeChildren_run_edge store s s1 n cs hcs
  have hmem : ∀ x ∈ cs.filter nodes.contains,
      NodeEdge store n x ∧ nodes.contains x = true := by
    intro x hx
    obtain ⟨hx, hv⟩ := Array.mem_filter.mp hx
    exact ⟨hedge x hx, hv⟩
  dsimp only at h
  split at h
  · have := run_pure_eq_ok _ _ _ _ h
    cases this
  · rename_i hne
    obtain ⟨best, s2, hfold, h⟩ := run_bind_eq_ok _ _ _ _ h
    have hc : c = best := by
      have := run_pure_eq_ok _ _ _ _ h
      injection this
    subst hc
    rw [← Array.foldlM_toList] at hfold
    have hpos : 0 < (cs.filter nodes.contains).size := by
      rcases Nat.eq_zero_or_pos (cs.filter nodes.contains).size with h0 | h0
      · exact absurd (Array.isEmpty_iff_size_eq_zero.mpr h0) (by simpa using hne)
      · exact h0
    rcases foldlM_run_mem _ (betterOf_run_mem store) (cs.filter nodes.contains).toList _ _ s1
        s2 hfold with hx | hx
    · rw [hx, getElem!_pos (cs.filter nodes.contains) 0 hpos]
      exact hmem _ (Array.getElem_mem hpos)
    · exact hmem _ (Array.mem_toList_iff.mp hx)

/-- A `.done` step of the `getHead` loop returns the current node. -/
theorem headLoopBody_run_done (store s s' : Store map) (nodes : Array ForkChoiceNode)
    (n d : ForkChoiceNode)
    (h : (headLoopBody store nodes n).run s = .ok (.done d, s')) :
    d = n := by
  unfold headLoopBody at h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  dsimp only at h
  split at h
  · exact Step.done.inj (run_pure_eq_ok _ _ _ _ h)
  · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    have := run_pure_eq_ok _ _ _ _ h
    cases this

/-- The `getHead` loop avoids the FULL node and every node below it. The block is from
the previous slot, and its payload is unverified or recorded `false`. The FULL node is in
the viable node list `nodes` only with the EMPTY node (`hviable`). The loop starts at
`start`, and its fuel-out value is `exhausted`. Neither is below the FULL node.

The invariant is "not below the FULL node". A `.next` step goes to a viable child `c` of
the current node `n`. Suppose `c` is below the FULL node. If `c` is the FULL node, then
`n` is its only parent, the pending node of the block. The FULL node is viable, so the
EMPTY node is viable, and the step goes to EMPTY. So `c` is EMPTY. If `c` is strictly
below, then its only parent `n` is below as well, against the invariant. -/
theorem headLoop_run_avoids_full [LawfulFcMap map Root] (store : Store map)
    (nodes : Array ForkChoiceNode) (root : Root) (rootBlock : BeaconBlock)
    (hblock : FcMap.lookup store.blocks root = some rootBlock)
    (hcurrentslot : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run store = .ok (rootBlock.slot + 1, store))
    (hnooverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot))
    (hfull : isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false)
    (hviable : nodes.contains (.full root) = true → nodes.contains (.empty root) = true)
    (fuel : Nat) (start exhausted head : ForkChoiceNode) (s s' : Store map)
    (hstart : ¬ NodeBelow store (.full root) start)
    (hexhausted : ¬ NodeBelow store (.full root) exhausted)
    (hrun : (fuelLoop fuel start exhausted (headLoopBody store nodes)).run s
      = .ok (head, s')) :
    ¬ NodeBelow store (.full root) head := by
  refine fuelLoop_run_inv (fun n => ¬ NodeBelow store (.full root) n)
    (fun n => ¬ NodeBelow store (.full root) n) exhausted _ ?_ ?_ hexhausted fuel start s s'
    head hstart hrun
  · intro n c t t' hn hstep hbelow
    obtain ⟨hedge, hc⟩ := headLoopBody_run_next_edge store t t' nodes n c hstep
    cases hbelow with
    | refl =>
      -- `c` is FULL, so `n` is the pending node of `root`. The FULL node is viable, so the
      -- EMPTY node is too, and the step goes to EMPTY.
      have hn' : n = .pending root :=
        NodeEdge.parent_unique store n _ _ hedge (NodeEdge.full root)
      subst hn'
      have hempty := getHeadStep_run_eq_empty_of_recorded_unsatisfied store t nodes root
        rootBlock hblock hcurrentslot hnooverflow hfull (hviable hc)
      rw [hempty] at hstep
      injection hstep with hstep
      injection hstep with hstep
      injection hstep with hstep
      exact payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus hstep)
    | step p _ hp hpc =>
      exact hn (NodeEdge.parent_unique store p n c hpc hedge ▸ hp)
  · intro n d t t' hn hstep
    rw [headLoopBody_run_done store t t' nodes n d hstep]
    exact hn

/-- `getHead` avoids the FULL node and every node below it. The block is from the
previous slot, and its payload is unverified or recorded `false`. The FULL node is viable
only with the EMPTY node (`EmptyViableWithFull`). The walk starts at the pending node of
the justified root. So the theorem assumes that this node is not below the FULL node. The
fuel-out value of the loop is the same node. With no viable node, `getHead` returns the
EMPTY node of the justified root, which is not below the FULL node either. -/
theorem getHead_run_avoids_full [LawfulFcMap map Root] (store : Store map) (root : Root)
    (rootBlock : BeaconBlock)
    (hblock : FcMap.lookup store.blocks root = some rootBlock)
    (hcurrentslot : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run store = .ok (rootBlock.slot + 1, store))
    (hnooverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot))
    (hfull : isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false)
    (hviable : EmptyViableWithFull store root)
    (hjustified : ¬ NodeBelow store (.full root) (.pending store.justifiedCheckpoint.root))
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) store).run runnerStore
      = .ok (head, s')) :
    ¬ NodeBelow store (.full root) head := by
  rw [getHead_eq_fuelLoop_headLoopBody] at hrun
  obtain ⟨nodes, s1, hnodes, hloop⟩ := run_bind_eq_ok _ _ _ _ hrun
  dsimp only at hloop
  split at hloop
  · -- No viable node: the EMPTY node of the justified root.
    rw [run_pure_eq_ok _ _ _ _ hloop]
    exact not_nodeBelow_empty_of_pending store root _ hjustified
  · exact headLoop_run_avoids_full store nodes root rootBlock hblock hcurrentslot hnooverflow
      hfull (hviable nodes runnerStore s1 hnodes) _ _ _ head s1 s' hjustified hjustified hloop

/-- `getHead_run_avoids_full` under `UnsatisfiedPayload`: at a store that records the
answer `false` for a block from the previous slot, the head avoids the FULL node of the
block and every node below it, when the FULL node is viable only with the EMPTY node. -/
theorem unsatisfiedPayload_getHead_avoids_full [LawfulFcMap map Root] (store : Store map)
    (root : Root) (rootBlock : BeaconBlock) (h : UnsatisfiedPayload store root rootBlock)
    (hviable : EmptyViableWithFull store root)
    (hjustified : ¬ NodeBelow store (.full root) (.pending store.justifiedCheckpoint.root))
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) store).run runnerStore
      = .ok (head, s')) :
    ¬ NodeBelow store (.full root) head :=
  getHead_run_avoids_full store root rootBlock h.block h.currentSlot h.noOverflow
    (fun _ => h.unsatisfied) hviable hjustified runnerStore s' head hrun

variable [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]

/-- The head for one missing transaction. Under the hypotheses of
`inclusionList_missing_tx`, the envelope handler succeeds. Take a `LaterStore` whose
justified root is not below the FULL node of `r`, and where the FULL node of `r` is
viable only with its EMPTY node. There `getHead` returns a head that is not below the
FULL node of `r`. So the head does not extend the payload of `r`. -/
theorem inclusionList_missing_tx_head_avoids_full [LawfulFcMap map Root]
    [LawfulFcMap map (EthCLSpecs.Heze.Slot × Root)] [LawfulFcMap map ValidatorIndex]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state : BeaconState}
    {block : BeaconBlock} {dependentRoot : Root} {postRunnerStore : Store map}
    {before after : List (SignedInclusionList × Bool)} {signed : SignedInclusionList}
    {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state block dependentRoot
      postRunnerStore before after signed il)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ∀ s : Store map, LaterStore s post signedEnv.message.beaconBlockRoot rootBlock →
        EmptyViableWithFull s signedEnv.message.beaconBlockRoot →
        ¬ NodeBelow s (.full signedEnv.message.beaconBlockRoot)
          (.pending s.justifiedCheckpoint.root) →
        ∀ (runnerStore s' : Store map) (head : ForkChoiceNode),
          (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s).run runnerStore
            = .ok (head, s') →
          ¬ NodeBelow s (.full signedEnv.message.beaconBlockRoot) head := by
  obtain ⟨post, hrun, -, hunsat⟩ := inclusionList_missing_tx rootBlock h htx hmissing hinvalid
  exact ⟨post, hrun, fun s hlater hviable hjustified runnerStore s' head hhead =>
    unsatisfiedPayload_getHead_avoids_full s _ rootBlock (hunsat s hlater) hviable hjustified
      runnerStore s' head hhead⟩

end

end EthCLSpecs.Proofs.Heze
