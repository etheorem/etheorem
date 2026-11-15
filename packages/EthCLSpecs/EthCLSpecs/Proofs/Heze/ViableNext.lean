import EthCLSpecs.Proofs.Heze.FinalityCheck

/-!
# `EthCLSpecs.Proofs.Heze.ViableNext`: the viable node list of `filter_node_tree`

`get_head` walks only the nodes that `get_filtered_node_tree` keeps
(`consensus-specs/specs/phase0/fork-choice.md:427-467`, Gloas `fork-choice.md:595-605`).
`filter_node_tree` keeps a node when it has children and a child keeps a node, or when it has
no children and its block passes the leaf check: the voting source is the store's justified
epoch or at most two epochs old, and the finalized checkpoint lies on the branch.

This module states the walk as membership facts about one successful run.

- `filterNodeTree_go_succ_eq` splits one step of the walk into the children read, the
  fold over the children, and the leaf check `leafOk`.
- `goFold_run_mem` reads the fold: a node is in the fold result when it is in the result of
  one child, and every child's walk succeeds.
- `filterNodeTree_go_mem_self` says when the walk keeps its own node, and
  `filterNodeTree_go_mem_child` that every other node it keeps comes from a child.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok run_pure_eq_ok_state StateFree
  pureState runPure except_bind_ok pureState_inj)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd htr fuelLoop)
open EthCLSpecs.Heze (Preset Config Store ForkChoiceNode getNodeChildren getCurrentStoreEpoch
  getVotingSource getCheckpointBlock updateCheckpoints getParentPayloadStatus isPayloadVerified)

variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- The leaf check of `filter_node_tree` (`phase0/fork-choice.md:441-467`), as a `Bool`: the
voting source of the node's block is the store's justified epoch, or within two epochs of the
current epoch, and the finalized checkpoint block of the branch is the store's finalized root.
The body copies the leaf branch of `filterNodeTree.go`; `filterNodeTree_go_succ_eq` ties the
two together. -/
def leafOk (store : Store map) (node : ForkChoiceNode) :
    ForkChoiceStoreRun (Store map) Bool := do
  let currentEpoch ← getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map)) store
  let votingSource ← getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store
    node.root
  let justifiedWithoutHorizon :=
    store.justifiedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
      || votingSource.epoch == store.justifiedCheckpoint.epoch
  let correctJustified ← if justifiedWithoutHorizon then pure true else do
    let horizon ← checkedAdd votingSource.epoch 2 "filter_node_tree: voting_source.epoch + 2"
    pure (decide (horizon ≥ currentEpoch))
  let finalizedBlock ← getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
    store node.root store.finalizedCheckpoint.epoch
  let correctFinalized :=
    store.finalizedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
      || store.finalizedCheckpoint.root == finalizedBlock
  pure (correctJustified && correctFinalized)

/-- The step of the walk over the children of a node: append each child's walk. -/
abbrev goStep (store : Store map) (k : Nat) (acc : Array ForkChoiceNode) (child : ForkChoiceNode) :
    ForkChoiceStoreRun (Store map) (Array ForkChoiceNode) := do
  pure (acc ++ (← EthCLSpecs.Heze.filterNodeTree.go
    (StoreTransition := ForkChoiceStoreRun (Store map)) store k child))

/-- One step of the walk: read the children; with children, fold their walks and keep the
node when the fold keeps any node; without children, keep the node when `leafOk` holds. -/
theorem filterNodeTree_go_succ_eq (store : Store map) (k : Nat) (n : ForkChoiceNode) :
    EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store (k + 1) n =
      (do
        let children ← getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
          store n
        if !children.isEmpty then
          let viableNodes ← children.foldlM (init := (#[] : Array ForkChoiceNode))
            (goStep store k)
          if !viableNodes.isEmpty then pure (viableNodes.push n) else pure #[]
        else do
          let b ← leafOk store n
          if b then pure #[n] else pure #[]) := by
  simp only [EthCLSpecs.Heze.filterNodeTree.go, leafOk, goStep, bind_assoc, pure_bind]
  -- The leaf branch: the spec's `if` on the justified test binds its own continuation, and
  -- `leafOk` returns the `Bool` first. Split the test and both sides agree.
  congr 1
  funext children
  split
  · rfl
  · congr 1
    funext currentEpoch
    congr 1
    funext votingSource
    split <;> simp only [bind_assoc, pure_bind]

omit [Config] in
/-- `getNodeChildren` reads no runner state. -/
theorem getNodeChildren_stateFree (store : Store map) (n : ForkChoiceNode) :
    StateFree (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store n) := by
  unfold EthCLSpecs.Heze.getNodeChildren EthCLSpecs.Heze.getParentPayloadStatus
  free_solve

/-- `leafOk` reads no runner state. -/
theorem leafOk_stateFree (store : Store map) (n : ForkChoiceNode) :
    StateFree (leafOk store n) := by
  unfold leafOk EthCLSpecs.Heze.getCurrentStoreEpoch EthCLSpecs.Heze.getCurrentSlot
    EthCLSpecs.Heze.getSlotsSinceGenesis EthCLSpecs.Heze.getVotingSource
    EthCLSpecs.Heze.getCheckpointBlock EthCLSpecs.Heze.getAncestor
    EthCLSpecs.Heze.getParentPayloadStatus EthCLLib.Spec.liftErr EthCLLib.Spec.checkedAdd
  -- The `let`s of the body elaborate as `have` join points, which `free_solve` does not
  -- step into; `dsimp only` inlines them first.
  dsimp only
  free_solve

/-- The fold over the children. From a successful run, the runner state is unchanged, each
child's walk succeeds, and a node is in the result when it is in the start value or in the
result of one child. -/
theorem goFold_run (store : Store map) (k : Nat) :
    ∀ (cs : List ForkChoiceNode) (acc vs : Array ForkChoiceNode) (t t' : Store map),
      (cs.foldlM (goStep store k) acc).run t = .ok (vs, t') →
      t' = t ∧ (∀ c ∈ cs, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
          (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t = .ok (ys, t)) ∧
        ∀ x, x ∈ vs ↔ x ∈ acc ∨ ∃ c ∈ cs, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
          (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t = .ok (ys, t) ∧
          x ∈ ys := by
  intro cs
  induction cs with
  | nil =>
    intro acc vs t t' h
    obtain ⟨h1, h2⟩ := run_pure_eq_ok_state h
    subst h1 h2
    exact ⟨rfl, fun c hc => absurd hc List.not_mem_nil, fun x => by simp⟩
  | cons c cs ih =>
    intro acc vs t t' h
    rw [List.foldlM_cons] at h
    obtain ⟨acc', t1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨ys, t2, hgo, hpure⟩ := run_bind_eq_ok _ _ _ _ hstep
    obtain ⟨hacc, ht⟩ := run_pure_eq_ok_state hpure
    subst hacc ht
    obtain ⟨ht2, hgo'⟩ := (filterNodeTree_go_stateFree store k c).run_eq hgo
    subst ht2
    obtain ⟨ht', hall, hmem⟩ := ih _ _ _ _ hrest
    refine ⟨ht', ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨ys, hgo⟩
      · exact hall d hd
    · intro x
      rw [hmem x, Array.mem_append]
      constructor
      · rintro ((hx | hx) | ⟨d, hd, zs, hz, hx⟩)
        · exact .inl hx
        · exact .inr ⟨c, List.mem_cons_self, ys, hgo, hx⟩
        · exact .inr ⟨d, List.mem_cons_of_mem _ hd, zs, hz, hx⟩
      · rintro (hx | ⟨d, hd, zs, hz, hx⟩)
        · exact .inl (.inl hx)
        · rcases List.mem_cons.mp hd with rfl | hd
          · rw [hgo] at hz
            injection hz with hz
            injection hz with hz
            subst hz
            exact .inl (.inr hx)
          · exact .inr ⟨d, hd, zs, hz, hx⟩

/-- One step of the walk, from a successful run. The runner state is unchanged, and the
children read succeeds. With children, each child's walk succeeds, and a node is kept when
it is the node itself and some child keeps a node, or a child keeps it. Without children, the
node is kept when `leafOk` holds, and nothing else is kept. -/
theorem filterNodeTree_go_succ_run (store : Store map) (k : Nat) (n : ForkChoiceNode)
    (t t' : Store map) (xs : Array ForkChoiceNode)
    (h : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (k + 1) n).run t = .ok (xs, t')) :
    t' = t ∧ ∃ cs, (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store
        n).run t = .ok (cs, t) ∧
      ((cs.isEmpty = false ∧
          (∀ c ∈ cs.toList, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
            (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t = .ok (ys, t)) ∧
          ∀ x, x ∈ xs ↔
            (x = n ∧ ∃ c ∈ cs.toList, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
              (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t
                = .ok (ys, t) ∧ ∃ y, y ∈ ys) ∨
            ∃ c ∈ cs.toList, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
              (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t
                = .ok (ys, t) ∧ x ∈ ys) ∨
        (cs.isEmpty = true ∧ ∃ b, (leafOk store n).run t = .ok (b, t) ∧
          ∀ x, x ∈ xs ↔ x = n ∧ b = true)) := by
  rw [filterNodeTree_go_succ_eq] at h
  obtain ⟨cs, t1, hcs, hk⟩ := run_bind_eq_ok _ _ _ _ h
  clear h
  obtain ⟨ht1, -⟩ := (getNodeChildren_stateFree store n).run_eq hcs
  subst t1
  split at hk
  · -- Children: the fold over their walks.
    rename_i hne
    have hne' : cs.isEmpty = false := by simpa using hne
    obtain ⟨vs, t2, hfold, hv⟩ := run_bind_eq_ok _ _ _ _ hk
    clear hk
    rw [← Array.foldlM_toList] at hfold
    obtain ⟨ht2, hall, hmem⟩ := goFold_run store k cs.toList #[] vs t t2 hfold
    subst t2
    -- A node of the fold result comes from one child's walk.
    have hfrom : ∀ x, x ∈ vs ↔ ∃ c ∈ cs.toList, ∃ ys, (EthCLSpecs.Heze.filterNodeTree.go
        (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t
          = .ok (ys, t) ∧ x ∈ ys := by
      intro x
      rw [hmem x]
      simp
    split at hv
    · rename_i hvs
      obtain ⟨rfl, rfl⟩ := run_pure_eq_ok_state hv
      refine ⟨rfl, cs, hcs, .inl ⟨hne', hall, fun x => ?_⟩⟩
      rw [Array.mem_push, hfrom x]
      have hsome : ∃ y, y ∈ vs := by
        rcases Array.exists_mem_of_ne_empty vs (by simpa using hvs) with ⟨y, hy⟩
        exact ⟨y, hy⟩
      constructor
      · rintro (hx | rfl)
        · exact .inr hx
        · obtain ⟨y, hy⟩ := hsome
          obtain ⟨c, hc, ys, hys, hy⟩ := (hfrom y).mp hy
          exact .inl ⟨rfl, c, hc, ys, hys, y, hy⟩
      · rintro (⟨rfl, -⟩ | hx)
        · exact .inr rfl
        · exact .inl hx
    · rename_i hvs
      obtain ⟨hxs, ht'⟩ := run_pure_eq_ok_state hv
      subst hxs t'
      have hvs' : vs = #[] := by simpa using hvs
      refine ⟨rfl, cs, hcs, .inl ⟨hne', hall, fun x => ?_⟩⟩
      -- Every child's walk keeps nothing: its nodes are nodes of the empty fold result.
      have hnone : ∀ c ∈ cs.toList, ∀ ys, (EthCLSpecs.Heze.filterNodeTree.go
          (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t
            = .ok (ys, t) → ∀ y, y ∉ ys := by
        intro c hc ys hys y hy
        have := (hfrom y).mpr ⟨c, hc, ys, hys, hy⟩
        rw [hvs'] at this
        simp at this
      constructor
      · intro hx
        simp at hx
      · rintro (⟨-, c, hc, ys, hys, y, hy⟩ | ⟨c, hc, ys, hys, hx⟩)
        · exact absurd hy (hnone c hc ys hys y)
        · exact absurd hx (hnone c hc ys hys x)
  · -- No children: the leaf check.
    rename_i hempty
    have hempty' : cs.isEmpty = true := by simpa using hempty
    obtain ⟨b, t2, hb, hl⟩ := run_bind_eq_ok _ _ _ _ hk
    clear hk
    obtain ⟨ht2, -⟩ := (leafOk_stateFree store n).run_eq hb
    subst t2
    split at hl
    · rename_i hbt
      obtain ⟨rfl, rfl⟩ := run_pure_eq_ok_state hl
      exact ⟨rfl, cs, hcs, .inr ⟨hempty', b, hb, fun x => by simp [hbt]⟩⟩
    · rename_i hbf
      obtain ⟨rfl, rfl⟩ := run_pure_eq_ok_state hl
      exact ⟨rfl, cs, hcs, .inr ⟨hempty', b, hb, fun x => by simp [hbf]⟩⟩

/-! ## The children of `r` and their leaves -/

omit [Config] in
/-- A child of a decided node is the pending node of a stored block whose parent root is the
node's root. The EMPTY and FULL edges start at pending nodes only. -/
theorem NodeEdge.of_decided {store : Store map} {d c : ForkChoiceNode} (h : NodeEdge store d c)
    (hd : d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending) :
    ∃ root b, c = .pending root ∧ FcMap.lookup store.blocks root = some b ∧
      b.parentRoot = d.root := by
  cases h with
  | empty root => exact absurd rfl hd
  | full root => exact absurd rfl hd
  | block parent root b s s' hl hp _ => exact ⟨root, b, rfl, hl, hp⟩

variable [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root]

omit [Config] in
/-- A decided node whose root no stored block names as its parent has no children. -/
theorem getNodeChildren_run_decided_empty (store : Store map) (d : ForkChoiceNode)
    (hd : d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending)
    (hnone : ∀ k b, FcMap.lookup store.blocks k = some b → b.parentRoot ≠ d.root)
    (t t' : Store map) (cs : Array ForkChoiceNode)
    (h : (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store d).run t
      = .ok (cs, t')) :
    cs.isEmpty = true := by
  have hedge := getNodeChildren_run_edge store t t' d cs h
  rcases cs with ⟨_ | ⟨c, l⟩⟩
  · rfl
  · exfalso
    obtain ⟨root, b, -, hl, hp⟩ := NodeEdge.of_decided (hedge c (by simp)) hd
    exact hnone root b hl hp

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The children of a pending node include its EMPTY node. -/
theorem getNodeChildren_run_pending_empty (store : Store map) (root : EthCLSpecs.Heze.Root)
    (t t' : Store map) (cs : Array ForkChoiceNode)
    (h : (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store
      (.pending root)).run t = .ok (cs, t')) :
    ForkChoiceNode.empty root ∈ cs := by
  simp only [EthCLSpecs.Heze.getNodeChildren] at h
  split at h
  · split at h
    · rw [run_pure_eq_ok _ _ _ _ h]
      simp [ForkChoiceNode.empty, ForkChoiceNode.pending]
    · rw [run_pure_eq_ok _ _ _ _ h]
      simp [ForkChoiceNode.empty, ForkChoiceNode.pending]
  · rename_i hne
    exact absurd (by rfl) hne

/-- The walk at the pending node of a block `c` with no child blocks. It keeps a node only when
the leaf check of `c` holds, and with fuel at least 2 it keeps the pending node then. -/
theorem go_pending_leafBlock (store : Store map) (c : EthCLSpecs.Heze.Root)
    (hnone : ∀ k b, FcMap.lookup store.blocks k = some b → b.parentRoot ≠ c) (j : Nat)
    (t : Store map) (ws : Array ForkChoiceNode)
    (h : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store j (.pending c)).run t = .ok (ws, t)) :
    ((∃ y, y ∈ ws) → (leafOk store (.pending c)).run t = .ok (true, t)) ∧
      (2 ≤ j → (leafOk store (.pending c)).run t = .ok (true, t) → ForkChoiceNode.pending c ∈ ws) := by
  -- The walk at a decided node of `c`: no children, so the leaf check decides.
  have hdec : ∀ (d : ForkChoiceNode), d.root = c →
      d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending → ∀ i us,
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store i d).run t = .ok (us, t) →
      ((∃ y, y ∈ us) → (leafOk store (.pending c)).run t = .ok (true, t)) ∧
        (1 ≤ i → (leafOk store (.pending c)).run t = .ok (true, t) → d ∈ us) := by
    intro d hdr hds i us hus
    cases i with
    | zero =>
      simp only [EthCLSpecs.Heze.filterNodeTree.go] at hus
      rw [run_pure_eq_ok _ _ _ _ hus]
      exact ⟨fun ⟨y, hy⟩ => by simp at hy, fun h1 => absurd h1 (by omega)⟩
    | succ i =>
      obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store i d t t us hus
      have hcs0 := getNodeChildren_run_decided_empty store d hds
        (fun k b hl hp => hnone k b hl (hp.trans hdr)) t t cs hcs
      rcases hcase with ⟨hne, -⟩ | ⟨-, b, hb, hmem⟩
      · rw [hcs0] at hne; cases hne
      · -- `leafOk` reads only the root, so the decided node and `pending c` agree.
        have hb' : (leafOk store (.pending c)).run t = .ok (b, t) := by
          rw [← hb]; cases d; subst hdr; rfl
        refine ⟨fun ⟨y, hy⟩ => ?_, fun _ hl => (hmem d).mpr ⟨rfl, ?_⟩⟩
        · obtain ⟨-, hbt⟩ := (hmem y).mp hy
          rw [hb', hbt]
        · rw [hl] at hb'
          injection hb' with hb'
          injection hb' with hb'
          exact hb'.symm
  cases j with
  | zero =>
    simp only [EthCLSpecs.Heze.filterNodeTree.go] at h
    rw [run_pure_eq_ok _ _ _ _ h]
    exact ⟨fun ⟨y, hy⟩ => by simp at hy, fun h2 => absurd h2 (by omega)⟩
  | succ j =>
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store j (.pending c) t t ws h
    have hE := getNodeChildren_run_pending_empty store c t t cs hcs
    have hedge := getNodeChildren_run_edge store t t (.pending c) cs hcs
    -- Every child of `pending c` is a decided node of `c`.
    have hchild : ∀ x ∈ cs, x.root = c ∧
        x.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
      intro x hx
      cases hedge x hx with
      | empty root => exact ⟨rfl, payloadStatus_empty_ne_pending⟩
      | full root => exact ⟨rfl, payloadStatus_full_ne_pending⟩
      | block parent root b s s' _ _ hs =>
        exact absurd rfl (getParentPayloadStatus_run_ne_pending store s s' b _ hs)
    rcases hcase with ⟨-, hall, hmem⟩ | ⟨hemp, -⟩
    · refine ⟨fun ⟨y, hy⟩ => ?_, fun h2 hl => (hmem _).mpr (.inl ⟨rfl, ?_⟩)⟩
      · rcases (hmem y).mp hy with ⟨-, x, hx, us, hus, hne⟩ | ⟨x, hx, us, hus, hy⟩
        · obtain ⟨hxr, hxs⟩ := hchild x (Array.mem_toList_iff.mp hx)
          exact (hdec x hxr hxs j us hus).1 hne
        · obtain ⟨hxr, hxs⟩ := hchild x (Array.mem_toList_iff.mp hx)
          exact (hdec x hxr hxs j us hus).1 ⟨y, hy⟩
      · obtain ⟨us, hus⟩ := hall _ (Array.mem_toList_iff.mpr hE)
        refine ⟨_, Array.mem_toList_iff.mpr hE, us, hus, _,
          (hdec _ rfl payloadStatus_empty_ne_pending j us hus).2 (by omega) hl⟩
    · rw [Array.isEmpty_iff] at hemp
      rw [hemp] at hE
      simp at hE

/-- **The EMPTY node of `r` survives the walk when the FULL node does**, at one fuel `k` for
both. The child blocks of `r` have no child blocks (`hleaf`), each passes the leaf check
exactly when `r` does (`hok`), and with a child block the fuel is at least 3 (`hfuel`).

The FULL node survives through a leaf: its own leaf check is the check of `r`, or a child
block's walk keeps a node, whose check is the check of `r` by `hok`. Either way `r` passes.
Then the EMPTY node survives as a leaf, or through any child block, whose walk keeps its
pending node (`go_pending_leafBlock`). -/
theorem go_empty_of_full (store : Store map) (r : EthCLSpecs.Heze.Root)
    (hleaf : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r →
      ∀ k b, FcMap.lookup store.blocks k = some b → b.parentRoot ≠ c)
    (hok : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r → ∀ t,
      (leafOk store (.pending c)).run t = (leafOk store (.pending r)).run t)
    (k : Nat) (hfuel : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r → 3 ≤ k)
    (t : Store map) (ys zs : Array ForkChoiceNode)
    (hfull : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store k (.full r)).run t = .ok (ys, t))
    (hempty : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store k (.empty r)).run t = .ok (zs, t))
    (hmem : ForkChoiceNode.full r ∈ ys) :
    ForkChoiceNode.empty r ∈ zs := by
  cases k with
  | zero =>
    simp only [EthCLSpecs.Heze.filterNodeTree.go] at hfull
    rw [run_pure_eq_ok _ _ _ _ hfull] at hmem
    simp at hmem
  | succ k =>
    -- The block `r` passes the leaf check.
    have hr : (leafOk store (.pending r)).run t = .ok (true, t) := by
      obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store k (.full r) t t ys hfull
      have hedge := getNodeChildren_run_edge store t t (.full r) cs hcs
      rcases hcase with ⟨-, -, hm⟩ | ⟨-, b, hb, hm⟩
      · have hsome : ∃ c ∈ cs.toList, ∃ ws, (EthCLSpecs.Heze.filterNodeTree.go
            (StoreTransition := ForkChoiceStoreRun (Store map)) store k c).run t = .ok (ws, t) ∧
            ∃ y, y ∈ ws := by
          rcases (hm _).mp hmem with ⟨-, c, hc, ws, hws, hne⟩ | ⟨c, hc, ws, hws, hy⟩
          · exact ⟨c, hc, ws, hws, hne⟩
          · exact ⟨c, hc, ws, hws, _, hy⟩
        obtain ⟨c, hc, ws, hws, hne⟩ := hsome
        obtain ⟨root, cb, rfl, hl, hp⟩ :=
          NodeEdge.of_decided (hedge c (Array.mem_toList_iff.mp hc)) payloadStatus_full_ne_pending
        have h1 := (go_pending_leafBlock store root (hleaf root cb hl hp) k t ws hws).1 hne
        rw [hok root cb hl hp t] at h1
        exact h1
      · obtain ⟨-, hbt⟩ := (hm _).mp hmem
        rw [hbt] at hb
        exact hb
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store k (.empty r) t t zs hempty
    have hedge := getNodeChildren_run_edge store t t (.empty r) cs hcs
    rcases hcase with ⟨hne, hall, hm⟩ | ⟨-, b, hb, hm⟩
    · -- A child block of `r` on the EMPTY edge: its walk keeps its pending node.
      rcases cs with ⟨_ | ⟨c, l⟩⟩
      · cases hne
      · have hc : c ∈ (⟨c :: l⟩ : Array ForkChoiceNode) := by simp
        obtain ⟨root, cb, rfl, hl, hp⟩ :=
          NodeEdge.of_decided (hedge _ hc) payloadStatus_empty_ne_pending
        have hk3 := hfuel root cb hl hp
        obtain ⟨ws, hws⟩ := hall _ (Array.mem_toList_iff.mpr hc)
        have hin := (go_pending_leafBlock store root (hleaf root cb hl hp) k t ws hws).2
          (by omega) (by rw [hok root cb hl hp t]; exact hr)
        exact (hm _).mpr (.inl ⟨rfl, _, Array.mem_toList_iff.mpr hc, ws, hws, _, hin⟩)
    · -- A leaf: its check is the check of `r`.
      have hb' : (leafOk store (.pending r)).run t = .ok (b, t) := hb
      rw [hr] at hb'
      injection hb' with hb'
      injection hb' with hb'
      exact (hm _).mpr ⟨rfl, hb'.symm⟩

/-- The fuel budget of the walk at node `n` with fuel `K`, for the list `P` of block roots
on the path to `n`: a pending node keeps `2 * |keys| + 2`, a decided node one less. Each step
spends one unit of fuel, and each step to a new block adds two units through `P`. -/
def Budget (store : Store map) (K : Nat) (n : ForkChoiceNode) (P : List EthCLSpecs.Heze.Root) :
    Prop :=
  if n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending then
    2 * (FcMap.keys store.blocks).length + 2 ≤ K + 2 * P.length
  else 2 * (FcMap.keys store.blocks).length + 1 ≤ K + 2 * P.length

/-- **The walk keeps the EMPTY node of `r` when it keeps the FULL node.** The walk runs from
any node `n` other than `full r`, with fuel `K` within its budget (`Budget`) for the path `P`
of distinct block roots to `n`, all no later than the block of `n`. The child blocks of `r`
have no child blocks, and each passes the leaf check exactly when `r` does.

A node that the walk keeps other than `n` comes from a child's walk. When the child is
`full r`, `n` is `pending r`, its children include `empty r`, and the budget leaves at least
3 units of fuel below `pending r` when `r` has a child block: that block is not on the path,
so the path is shorter than the key list. `go_empty_of_full` then applies. Otherwise the
child keeps the budget, and the induction applies to it. -/
theorem go_empty_of_full_walk (store : Store map) (r : EthCLSpecs.Heze.Root)
    (hslots : SlotsIncrease store)
    (hleaf : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r →
      ∀ k b, FcMap.lookup store.blocks k = some b → b.parentRoot ≠ c)
    (hok : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r → ∀ t,
      (leafOk store (.pending c)).run t = (leafOk store (.pending r)).run t) :
    ∀ (K : Nat) (n : ForkChoiceNode) (P : List EthCLSpecs.Heze.Root) (nb : EthCLSpecs.Heze.BeaconBlock)
      (t : Store map) (xs : Array ForkChoiceNode),
      FcMap.lookup store.blocks n.root = some nb → P.Nodup →
      (∀ x ∈ P, ∃ bx, FcMap.lookup store.blocks x = some bx ∧ bx.slot ≤ nb.slot) →
      n.root ∈ P → Budget store K n P →
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store K n).run t = .ok (xs, t) →
      n ≠ .full r → ForkChoiceNode.full r ∈ xs → ForkChoiceNode.empty r ∈ xs := by
  intro K
  induction K with
  | zero =>
    intro n P nb t xs _ _ _ _ _ h _ hmem
    simp only [EthCLSpecs.Heze.filterNodeTree.go] at h
    rw [run_pure_eq_ok _ _ _ _ h] at hmem
    simp at hmem
  | succ K ih =>
    intro n P nb t xs hnb hP hPs hnP hbud h hne hmem
    have hPin : ∀ x ∈ P, ∃ bx, FcMap.lookup store.blocks x = some bx := fun x hx =>
      let ⟨bx, hbx, _⟩ := hPs x hx; ⟨bx, hbx⟩
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t xs h
    have hedge := getNodeChildren_run_edge store t t n cs hcs
    rcases hcase with ⟨-, hall, hm⟩ | ⟨-, b, -, hm⟩
    · rcases (hm _).mp hmem with ⟨heq, -⟩ | ⟨c, hc, ys, hys, hfy⟩
      · exact absurd heq.symm hne
      · have hc' : c ∈ cs := Array.mem_toList_iff.mp hc
        by_cases hcf : c = .full r
        · -- The child is `full r`, so `n` is `pending r`.
          subst hcf
          have hn : n = .pending r :=
            NodeEdge.parent_unique store n _ _ (hedge _ hc') (NodeEdge.full r)
          subst hn
          have hE := getNodeChildren_run_pending_empty store r t t cs hcs
          obtain ⟨zs, hzs⟩ := hall _ (Array.mem_toList_iff.mpr hE)
          have hfuel : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r →
              3 ≤ K := by
            intro c cb hl hp
            -- The child block is later than every block of the path, so it is not on it.
            have hlt : nb.slot < cb.slot := hslots c cb nb hl (hp ▸ hnb)
            have hcP : c ∉ P := by
              intro hcP
              obtain ⟨bx, hbx, hle⟩ := hPs c hcP
              rw [hl] at hbx
              cases hbx
              exact absurd hle (UInt64.not_le.mpr hlt)
            have hlen := length_le_keys store (c :: P) (List.nodup_cons.mpr ⟨hcP, hP⟩)
              (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact ⟨cb, hl⟩
                · exact hPin x hx)
            simp only [Budget, ForkChoiceNode.pending, ite_true] at hbud
            simp only [List.length_cons] at hlen
            omega
          have := go_empty_of_full store r hleaf hok K hfuel t ys zs hys hzs hfy
          exact (hm _).mpr (.inr ⟨_, Array.mem_toList_iff.mpr hE, zs, hzs, this⟩)
        · -- Another child: it keeps the budget; the induction applies to it.
          by_cases hpend : n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
          · -- A decided child of the same root.
            have hcr : c.root = n.root ∧
                c.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
              cases hedge c hc' with
              | empty root => exact ⟨rfl, payloadStatus_empty_ne_pending⟩
              | full root => exact ⟨rfl, payloadStatus_full_ne_pending⟩
              | block parent root b s s' _ _ hs =>
                exact absurd hpend (getParentPayloadStatus_run_ne_pending store s s' b _ hs)
            have hbud' : Budget store K c P := by
              simp only [Budget, hpend, ite_true] at hbud
              simp only [Budget, hcr.2, ite_false]
              omega
            have := ih c P nb t ys (hcr.1 ▸ hnb) hP hPs (hcr.1 ▸ hnP) hbud' hys hcf hfy
            exact (hm _).mpr (.inr ⟨c, hc, ys, hys, this⟩)
          · -- A pending child of a new block.
            obtain ⟨root, cb, rfl, hl, hp⟩ := NodeEdge.of_decided (hedge c hc') hpend
            have hlt : nb.slot < cb.slot := hslots root cb nb hl (hp ▸ hnb)
            have hcP : root ∉ P := by
              intro hcP
              obtain ⟨bx, hbx, hle⟩ := hPs root hcP
              rw [hl] at hbx
              cases hbx
              exact absurd hle (UInt64.not_le.mpr hlt)
            have hbud' : Budget store K (.pending root) (root :: P) := by
              simp only [Budget, hpend, ite_false] at hbud
              simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_cons]
              omega
            have hPs' : ∀ x ∈ root :: P, ∃ bx, FcMap.lookup store.blocks x = some bx ∧
                bx.slot ≤ cb.slot := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨cb, hl, UInt64.le_refl _⟩
              · obtain ⟨bx, hbx, hle⟩ := hPs x hx
                exact ⟨bx, hbx, UInt64.le_trans hle (UInt64.le_of_lt hlt)⟩
            have := ih (.pending root) (root :: P) cb t ys hl
              (List.nodup_cons.mpr ⟨hcP, hP⟩) hPs' List.mem_cons_self hbud' hys hcf hfy
            exact (hm _).mpr (.inr ⟨_, hc, ys, hys, this⟩)
    · -- A leaf keeps only itself, which is not `full r`.
      obtain ⟨heq, -⟩ := (hm _).mp hmem
      exact absurd heq.symm hne

/-- The derived `BEq` of `ForkChoiceNode` compares both fields with their lawful `BEq`, so it
is lawful. `Array.contains_iff_mem` needs this to read `contains` as membership. -/
instance : LawfulBEq ForkChoiceNode where
  eq_of_beq {a b} h := by
    rcases a with ⟨ra, sa⟩
    rcases b with ⟨rb, sb⟩
    have h' : (ra == rb && sa == sb) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    rw [h'.1, h'.2]
  rfl {a} := by
    rcases a with ⟨ra, sa⟩
    show (ra == ra && sa == sa) = true
    simp

/-- **`EmptyViableWithFull` from the children of `r`.** The justified root has a block in the
store, block slots increase along parent links, the child blocks of `r` have no child blocks,
and each passes the leaf check exactly when `r` does. Then in the viable node list the FULL
node of `r` comes only with the EMPTY node. The walk starts at the pending node of the
justified root with fuel `2 * |keys| + 2`, which is its budget for the one-root path. -/
theorem emptyViableWithFull_of_children (store : Store map) (r : EthCLSpecs.Heze.Root)
    (hslots : SlotsIncrease store) {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (hleaf : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r →
      ∀ k b, FcMap.lookup store.blocks k = some b → b.parentRoot ≠ c)
    (hok : ∀ c cb, FcMap.lookup store.blocks c = some cb → cb.parentRoot = r → ∀ t,
      (leafOk store (.pending c)).run t = (leafOk store (.pending r)).run t) :
    EmptyViableWithFull store r := by
  intro nodes t t' hrun hfull
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  have hbud : Budget store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root) [store.justifiedCheckpoint.root] := by
    simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_singleton]
    omega
  have hne : ForkChoiceNode.pending store.justifiedCheckpoint.root ≠ .full r := fun h =>
    payloadStatus_full_ne_pending (congrArg ForkChoiceNode.payloadStatus h).symm
  rw [Array.contains_iff_mem] at hfull ⊢
  exact go_empty_of_full_walk store r hslots hleaf hok _ _ [store.justifiedCheckpoint.root] jb
    t nodes hj (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact ⟨jb, hj, UInt64.le_refl _⟩)
    (List.mem_singleton_self _) hbud hrun' hne hfull

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- Two nodes pass the leaf check together when the voting source and the finalized
checkpoint block of their roots read the same. `leafOk` reads nothing else of the node. -/
theorem leafOk_eq_of_reads (store : Store map) (n m : ForkChoiceNode)
    (hv : ∀ u, (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store
      n.root).run u = (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map))
      store m.root).run u)
    (hc : ∀ u, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store
      n.root store.finalizedCheckpoint.epoch).run u =
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store m.root
        store.finalizedCheckpoint.epoch).run u) :
    leafOk store n = leafOk store m := by
  -- A `StateT` value is a function of the runner state, so equal runs give equal values.
  have hv' : getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store n.root =
      getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store m.root :=
    funext hv
  have hc' : getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store n.root
      store.finalizedCheckpoint.epoch =
      getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store m.root
        store.finalizedCheckpoint.epoch := funext hc
  simp only [leafOk, hv', hc']

/-- The finalized test of the leaf check on the root `x`: the finalized epoch is genesis, or
the checkpoint block of `x` at the finalized epoch is the finalized root. -/
def finRead (store : Store map) (x : EthCLSpecs.Heze.Root) : ForkChoiceStoreRun (Store map) Bool :=
  (fun fb => store.finalizedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
      || store.finalizedCheckpoint.root == fb) <$>
    getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store x
      store.finalizedCheckpoint.epoch

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `leafOk` reads the checkpoint block only through the finalized test. -/
theorem leafOk_eq_finRead (store : Store map) (n : ForkChoiceNode) :
    leafOk store n = (do
      let currentEpoch ← getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map))
        store
      let votingSource ← getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store
        n.root
      let correctJustified ← if store.justifiedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch then pure true else do
        let horizon ← checkedAdd votingSource.epoch 2 "filter_node_tree: voting_source.epoch + 2"
        pure (decide (horizon ≥ currentEpoch))
      let correctFinalized ← finRead store n.root
      pure (correctJustified && correctFinalized)) := by
  simp only [leafOk, finRead, map_eq_pure_bind, bind_assoc, pure_bind]

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- Two nodes pass the leaf check together when their voting sources read the same and their
finalized tests read the same. -/
theorem leafOk_eq_of_fin (store : Store map) (n m : ForkChoiceNode)
    (hv : ∀ u, (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store
      n.root).run u = (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map))
      store m.root).run u)
    (hf : ∀ u, (finRead store n.root).run u = (finRead store m.root).run u) :
    leafOk store n = leafOk store m := by
  have hv' : getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store n.root =
      getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store m.root :=
    funext hv
  have hf' : finRead store n.root = finRead store m.root := funext hf
  rw [leafOk_eq_finRead, leafOk_eq_finRead, hv', hf']

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The finalized test from the checkpoint block reads: equal reads, or two successful reads
that the test does not tell apart. -/
theorem finRead_eq_of (store : Store map) (x y : EthCLSpecs.Heze.Root) (u : Store map)
    (h : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store x
        store.finalizedCheckpoint.epoch).run u =
        (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store y
          store.finalizedCheckpoint.epoch).run u ∨
      ∃ fx fy, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store x
          store.finalizedCheckpoint.epoch).run u = .ok (fx, u) ∧
        (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store y
          store.finalizedCheckpoint.epoch).run u = .ok (fy, u) ∧
        (store.finalizedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
          || store.finalizedCheckpoint.root == fx) =
        (store.finalizedCheckpoint.epoch == EthCLSpecs.Heze.Const.genesisEpoch
          || store.finalizedCheckpoint.root == fy)) :
    (finRead store x).run u = (finRead store y).run u := by
  unfold finRead
  rw [StateT.run_map, StateT.run_map]
  rcases h with h | ⟨fx, fy, hx, hy, hxy⟩
  · rw [h]
  · rw [hx, hy]
    simp only [Functor.map, Except.map]
    rw [hxy]

/-! ## A kept node keeps the path above it -/

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A node below `n` is `n`, or below a child of `n`. -/
theorem NodeBelow.head {store : Store map} {n m : ForkChoiceNode} (h : NodeBelow store n m) :
    m = n ∨ ∃ c, NodeEdge store n c ∧ NodeBelow store c m := by
  induction h with
  | refl => exact .inl rfl
  | step p c hp hpc ih =>
    rcases ih with rfl | ⟨d, hd, hdp⟩
    · exact .inr ⟨c, hpc, .refl⟩
    · exact .inr ⟨d, hd, .step p c hdp hpc⟩

omit [Config] in
/-- Every child of a node in the node tree that the children read can return is in its
result: the EMPTY child of a pending node, its FULL child when the payload is verified, and
the pending node of each stored block on the edge. -/
theorem getNodeChildren_run_mem (store : Store map) (n c : ForkChoiceNode) (hedge : NodeEdge store n c)
    (hfull : ∀ x, n = .pending x → c = .full x → isPayloadVerified store x = true)
    (t t' : Store map) (cs : Array ForkChoiceNode)
    (h : (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store n).run t
      = .ok (cs, t')) :
    c ∈ cs := by
  cases hedge with
  | empty root => exact getNodeChildren_run_pending_empty store root t t' cs h
  | full root =>
    have hv := hfull root rfl rfl
    have hv' : isPayloadVerified store (ForkChoiceNode.pending root).root = true := hv
    simp only [EthCLSpecs.Heze.getNodeChildren] at h
    split at h
    · -- `simp` already took the verified branch, using `hv'`.
      rw [run_pure_eq_ok _ _ _ _ h]
      simp [ForkChoiceNode.full, ForkChoiceNode.pending]
    · rename_i hne
      exact absurd (by rfl) hne
  | block parent root b s s' hl hp hs =>
    have hps := getParentPayloadStatus_run_ne_pending store s s' b _ hs
    simp only [EthCLSpecs.Heze.getNodeChildren] at h
    split at h
    · rename_i hpend
      exact absurd (beq_iff_eq.mp hpend) hps
    · obtain ⟨r', t1, hloop, hret⟩ := run_bind_eq_ok _ _ _ _ h
      rw [run_pure_eq_ok _ _ _ _ hret]
      rw [← Array.forIn_toList] at hloop
      -- The entry of `root` is in the fold. Each step of the loop keeps what is pushed, and
      -- the step at that entry pushes `pending root`.
      have hentry : (root, b) ∈ (FcMap.fold (fun acc r b => acc.push (r, b))
          (#[] : Array (EthCLSpecs.Heze.Root × EthCLSpecs.Heze.BeaconBlock)) store.blocks).toList :=
        (EthCLLib.Proofs.LawfulFcMap.mem_fold_push store.blocks root b).mpr hl
      clear h hret
      revert hloop hentry
      generalize (FcMap.fold (fun acc r b => acc.push (r, b))
          (#[] : Array (EthCLSpecs.Heze.Root × EthCLSpecs.Heze.BeaconBlock)) store.blocks).toList = l
      generalize (#[] : Array ForkChoiceNode) = acc
      intro hloop hentry
      induction l generalizing acc t with
      | nil => exact absurd hentry List.not_mem_nil
      | cons e l ih =>
        rw [List.forIn_cons] at hloop
        obtain ⟨st, t2, hst, hrest⟩ := run_bind_eq_ok _ _ _ _ hloop
        obtain ⟨root', b'⟩ := e
        -- The step yields the accumulator, with `pending root'` pushed on the edge.
        have hstep : ∃ acc', st = .yield acc' ∧ (∀ x ∈ acc, x ∈ acc') ∧
            ((root', b') = (root, b) → ForkChoiceNode.pending root ∈ acc') := by
          dsimp only at hst
          split at hst
          · rename_i hpar
            obtain ⟨ps', t3, hps', hst⟩ := run_bind_eq_ok _ _ _ _ hst
            split at hst
            · rw [run_pure_eq_ok _ _ _ _ hst]
              refine ⟨_, rfl, fun x hx => Array.mem_push_of_mem _ hx, fun heq => ?_⟩
              injection heq with h1
              subst h1
              exact Array.mem_push_self
            · rename_i hne
              rw [run_pure_eq_ok _ _ _ _ hst]
              refine ⟨_, rfl, fun x hx => hx, fun heq => ?_⟩
              injection heq with h1 h2
              subst h1 h2
              exfalso
              have hv := getParentPayloadStatus_run_val store _ _ _ _ b' _ _ hps' hs
              exact hne (by rw [hv]; exact beq_self_eq_true _)
          · rename_i hpar
            rw [run_pure_eq_ok _ _ _ _ hst]
            refine ⟨_, rfl, fun x hx => hx, fun heq => ?_⟩
            injection heq with h1 h2
            subst h1 h2
            exact absurd (by rw [hp]; exact beq_self_eq_true _) hpar
        obtain ⟨acc', rfl, -, hpush⟩ := hstep
        rcases List.mem_cons.mp hentry with heq | hin
        · -- The entry: pushed here, and the rest of the loop only pushes.
          have hin' := hpush heq.symm
          refine EthCLLib.Proofs.forIn_run_inv (fun a => ForkChoiceNode.pending root ∈ a) _ l
            ?_ acc' t2 t1 r' hin' hrest
          intro a _ q s s' st' hq hs'
          split at hs'
          · obtain ⟨_, _, -, hs'⟩ := run_bind_eq_ok _ _ _ _ hs'
            split at hs'
            · rw [run_pure_eq_ok _ _ _ _ hs']
              exact Array.mem_push_of_mem _ hq
            · rw [run_pure_eq_ok _ _ _ _ hs']
              exact hq
          · rw [run_pure_eq_ok _ _ _ _ hs']
            exact hq
        · exact ih t2 acc' hrest hin

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- An edge followed by a path is a path. -/
theorem NodeBelow.of_edge {store : Store map} {n c y : ForkChoiceNode} (he : NodeEdge store n c)
    (h : NodeBelow store c y) : NodeBelow store n y := by
  induction h with
  | refl => exact .step _ _ .refl he
  | step p d _ hpd ih => exact .step p d ih hpd

/-- A node is kept by its own walk at every fuel within its budget. -/
def KeptAt (store : Store map) (x : ForkChoiceNode) : Prop :=
  ∀ (K : Nat) (P : List EthCLSpecs.Heze.Root) (xb : EthCLSpecs.Heze.BeaconBlock) (t : Store map)
    (ys : Array ForkChoiceNode),
    FcMap.lookup store.blocks x.root = some xb → P.Nodup →
    (∀ y ∈ P, ∃ yb, FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ xb.slot) →
    x.root ∈ P → Budget store K x P →
    (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store K x).run t = .ok (ys, t) → x ∈ ys

/-- **A kept node is kept by the walk of each ancestor.** The walk from `n` descends along the
path to `x`: each child on the path is in the children read (`getNodeChildren_run_mem`, a
FULL child on the path has its payload verified), its walk keeps `x` by induction, and the
walk of `n` keeps every node that a child's walk keeps. The budget passes down the path as in
`go_empty_of_full_walk`. -/
theorem go_keeps_desc (store : Store map) (hslots : SlotsIncrease store) (x : ForkChoiceNode)
    (hx : KeptAt store x) :
    ∀ (K : Nat) (n : ForkChoiceNode) (P : List EthCLSpecs.Heze.Root) (nb : EthCLSpecs.Heze.BeaconBlock)
      (t : Store map) (xs : Array ForkChoiceNode),
      FcMap.lookup store.blocks n.root = some nb → P.Nodup →
      (∀ y ∈ P, ∃ yb, FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ nb.slot) →
      n.root ∈ P → Budget store K n P →
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store K n).run t = .ok (xs, t) →
      NodeBelow store n x →
      (∀ z, NodeBelow store n (.full z) → NodeBelow store (.full z) x →
        isPayloadVerified store z = true) →
      x ∈ xs := by
  intro K
  induction K with
  | zero =>
    intro n P nb t xs hnb hP hPs hnP hbud h hbelow hver
    -- A budget of zero fuel needs a path longer than the key list.
    have hlen := length_le_keys store P hP fun y hy =>
      let ⟨yb, hyb, _⟩ := hPs y hy; ⟨yb, hyb⟩
    unfold Budget at hbud
    split at hbud <;> omega
  | succ K ih =>
    intro n P nb t xs hnb hP hPs hnP hbud h hbelow hver
    rcases NodeBelow.head hbelow with rfl | ⟨c, hedge, hcx⟩
    · exact hx _ P nb t xs hnb hP hPs hnP hbud h
    · obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t xs h
      have hc : c ∈ cs := getNodeChildren_run_mem store n c hedge (fun z hn hc' => by
        subst hn hc'
        exact hver z (.step _ _ .refl (NodeEdge.full z)) hcx) t t cs hcs
      rcases hcase with ⟨-, hall, hm⟩ | ⟨hemp, -⟩
      · obtain ⟨ys, hys⟩ := hall c (Array.mem_toList_iff.mpr hc)
        -- The budget of the child, as in `go_empty_of_full_walk`.
        have hver' : ∀ z, NodeBelow store c (.full z) → NodeBelow store (.full z) x →
            isPayloadVerified store z = true :=
          fun z hcz hzx => hver z (NodeBelow.of_edge hedge hcz) hzx
        -- The child's walk keeps `x`, so the walk of `n` keeps it.
        have hxc : x ∈ ys := by
          by_cases hpend : n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
          · -- A decided child of the same root keeps the path.
            have hcr : c.root = n.root ∧
                c.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
              cases hedge with
              | empty root => exact ⟨rfl, payloadStatus_empty_ne_pending⟩
              | full root => exact ⟨rfl, payloadStatus_full_ne_pending⟩
              | block parent root b s s' _ _ hs =>
                exact absurd hpend (getParentPayloadStatus_run_ne_pending store s s' b _ hs)
            have hbud' : Budget store K c P := by
              simp only [Budget, hpend, ite_true] at hbud
              simp only [Budget, hcr.2, ite_false]
              omega
            exact ih c P nb t ys (hcr.1 ▸ hnb) hP hPs (hcr.1 ▸ hnP) hbud' hys hcx hver'
          · -- A pending child of a new block adds its root to the path.
            obtain ⟨root, cb, rfl, hl, hp⟩ := NodeEdge.of_decided hedge hpend
            have hlt : nb.slot < cb.slot := hslots root cb nb hl (hp ▸ hnb)
            have hcP : root ∉ P := by
              intro hcP
              obtain ⟨bx, hbx, hle⟩ := hPs root hcP
              rw [hl] at hbx
              cases hbx
              exact absurd hle (UInt64.not_le.mpr hlt)
            have hbud' : Budget store K (.pending root) (root :: P) := by
              simp only [Budget, hpend, ite_false] at hbud
              simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_cons]
              omega
            have hPs' : ∀ y ∈ root :: P, ∃ yb, FcMap.lookup store.blocks y = some yb ∧
                yb.slot ≤ cb.slot := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨cb, hl, UInt64.le_refl _⟩
              · obtain ⟨yb, hyb, hle⟩ := hPs y hy
                exact ⟨yb, hyb, UInt64.le_trans hle (UInt64.le_of_lt hlt)⟩
            exact ih (.pending root) (root :: P) cb t ys hl (List.nodup_cons.mpr ⟨hcP, hP⟩) hPs'
              List.mem_cons_self hbud' hys hcx hver'
        exact (hm x).mpr (.inr ⟨c, Array.mem_toList_iff.mpr hc, ys, hys, hxc⟩)
      · rw [Array.isEmpty_iff] at hemp
        rw [hemp] at hc
        simp at hc

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **The budget passes to a child.** A decided child of a pending node keeps the root and the
path. A pending child of a decided node is a new block, later than every block of the path, so
it joins the path with two units of fuel. -/
theorem Budget.child (store : Store map) (hslots : SlotsIncrease store) {K : Nat}
    {n c : ForkChoiceNode} {P : List EthCLSpecs.Heze.Root} {nb : EthCLSpecs.Heze.BeaconBlock}
    (hnb : FcMap.lookup store.blocks n.root = some nb) (hP : P.Nodup)
    (hPs : ∀ y ∈ P, ∃ yb, FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ nb.slot)
    (hnP : n.root ∈ P) (hbud : Budget store (K + 1) n P) (hedge : NodeEdge store n c) :
    ∃ (P' : List EthCLSpecs.Heze.Root) (cb : EthCLSpecs.Heze.BeaconBlock),
      FcMap.lookup store.blocks c.root = some cb ∧ P'.Nodup ∧
      (∀ y ∈ P', ∃ yb, FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ cb.slot) ∧
      c.root ∈ P' ∧ Budget store K c P' := by
  by_cases hpend : n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
  · have hcr : c.root = n.root ∧
        c.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
      cases hedge with
      | empty root => exact ⟨rfl, payloadStatus_empty_ne_pending⟩
      | full root => exact ⟨rfl, payloadStatus_full_ne_pending⟩
      | block parent root b s s' _ _ hs =>
        exact absurd hpend (getParentPayloadStatus_run_ne_pending store s s' b _ hs)
    refine ⟨P, nb, hcr.1 ▸ hnb, hP, hPs, hcr.1 ▸ hnP, ?_⟩
    simp only [Budget, hpend, ite_true] at hbud
    simp only [Budget, hcr.2, ite_false]
    omega
  · obtain ⟨root, cb, rfl, hl, hp⟩ := NodeEdge.of_decided hedge hpend
    have hlt : nb.slot < cb.slot := hslots root cb nb hl (hp ▸ hnb)
    have hcP : root ∉ P := by
      intro hcP
      obtain ⟨bx, hbx, hle⟩ := hPs root hcP
      rw [hl] at hbx
      cases hbx
      exact absurd hle (UInt64.not_le.mpr hlt)
    refine ⟨root :: P, cb, hl, List.nodup_cons.mpr ⟨hcP, hP⟩, ?_, List.mem_cons_self, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨cb, hl, UInt64.le_refl _⟩
      · obtain ⟨yb, hyb, hle⟩ := hPs y hy
        exact ⟨yb, hyb, UInt64.le_trans hle (UInt64.le_of_lt hlt)⟩
    · simp only [Budget, hpend, ite_false] at hbud
      simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_cons]
      omega

/-- **A strict ancestor of a kept node keeps itself.** The child on the path keeps the node
(`go_keeps_desc`), so its walk returns a node, and the ancestor is kept. -/
theorem go_keeps_anc (store : Store map) (hslots : SlotsIncrease store) (x : ForkChoiceNode)
    (hx : KeptAt store x) :
    ∀ (K : Nat) (n : ForkChoiceNode) (P : List EthCLSpecs.Heze.Root) (nb : EthCLSpecs.Heze.BeaconBlock)
      (t : Store map) (xs : Array ForkChoiceNode),
      FcMap.lookup store.blocks n.root = some nb → P.Nodup →
      (∀ y ∈ P, ∃ yb, FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ nb.slot) →
      n.root ∈ P → Budget store K n P →
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store K n).run t = .ok (xs, t) →
      NodeBelow store n x → n ≠ x →
      (∀ z, NodeBelow store n (.full z) → NodeBelow store (.full z) x →
        isPayloadVerified store z = true) →
      n ∈ xs := by
  intro K n P nb t xs hnb hP hPs hnP hbud h hbelow hne hver
  cases K with
  | zero =>
    have hlen := length_le_keys store P hP fun y hy =>
      let ⟨yb, hyb, _⟩ := hPs y hy; ⟨yb, hyb⟩
    unfold Budget at hbud
    split at hbud <;> omega
  | succ K =>
    rcases NodeBelow.head hbelow with heq | ⟨c, hedge, hcx⟩
    · exact absurd heq.symm hne
    · obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t xs h
      have hc : c ∈ cs := getNodeChildren_run_mem store n c hedge (fun z hn hc' => by
        subst hn hc'
        exact hver z (.step _ _ .refl (NodeEdge.full z)) hcx) t t cs hcs
      rcases hcase with ⟨-, hall, hm⟩ | ⟨hemp, -⟩
      · obtain ⟨ys, hys⟩ := hall c (Array.mem_toList_iff.mpr hc)
        obtain ⟨P', cb, hcb, hP', hPs', hcP', hbud'⟩ :=
          Budget.child store hslots hnb hP hPs hnP hbud hedge
        have hxc := go_keeps_desc store hslots x hx K c P' cb t ys hcb hP' hPs' hcP' hbud' hys hcx
          (fun z hcz hzx => hver z (NodeBelow.of_edge hedge hcz) hzx)
        exact (hm n).mpr (.inl ⟨rfl, c, Array.mem_toList_iff.mpr hc, ys, hys, x, hxc⟩)
      · rw [Array.isEmpty_iff] at hemp
        rw [hemp] at hc
        simp at hc

/-- **A node all of whose leaves pass the leaf check is kept.** A leaf passes. A node with
children keeps any child, by induction, so its walk returns a node and it is kept. The budget
passes down (`Budget.child`). -/
theorem kept_of_leaves (store : Store map) (hslots : SlotsIncrease store) (m : ForkChoiceNode)
    (hleaves : ∀ d, NodeBelow store m d → ∀ u cs,
      (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store d).run u
        = .ok (cs, u) → cs.isEmpty = true → (leafOk store d).run u = .ok (true, u)) :
    KeptAt store m := by
  suffices h : ∀ (K : Nat) (n : ForkChoiceNode), NodeBelow store m n → KeptAt store n from
    h 0 m .refl
  intro _ n hn K
  induction K generalizing n with
  | zero =>
    intro P xb t ys hxb hP hPs hxP hbud _
    have hlen := length_le_keys store P hP fun y hy =>
      let ⟨yb, hyb, _⟩ := hPs y hy; ⟨yb, hyb⟩
    unfold Budget at hbud
    split at hbud <;> omega
  | succ K ih =>
    intro P xb t ys hxb hP hPs hxP hbud hrun
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t ys hrun
    rcases hcase with ⟨hne, hall, hm⟩ | ⟨hemp, b, hb, hm⟩
    · -- With children: any child is kept, by induction.
      rcases cs with ⟨_ | ⟨c, l⟩⟩
      · cases hne
      · have hc : c ∈ (⟨c :: l⟩ : Array ForkChoiceNode) := by simp
        have hedge := getNodeChildren_run_edge store t t n _ hcs c hc
        obtain ⟨zs, hzs⟩ := hall c (Array.mem_toList_iff.mpr hc)
        obtain ⟨P', cb, hcb, hP', hPs', hcP', hbud'⟩ :=
          Budget.child store hslots hxb hP hPs hxP hbud hedge
        have hcz := ih c (NodeBelow.step _ _ hn hedge) P' cb t zs hcb hP' hPs' hcP' hbud' hzs
        exact (hm n).mpr (.inl ⟨rfl, c, Array.mem_toList_iff.mpr hc, zs, hzs, c, hcz⟩)
    · -- A leaf: it passes the check.
      have htrue := hleaves n hn t cs hcs hemp
      rw [hb] at htrue
      injection htrue with htrue
      injection htrue with htrue
      exact (hm n).mpr ⟨rfl, htrue⟩

/-- Every node that the walk from `n` keeps is below `n`. -/
theorem go_result_below (store : Store map) :
    ∀ (K : Nat) (n : ForkChoiceNode) (t : Store map) (xs : Array ForkChoiceNode),
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store K n).run t = .ok (xs, t) → ∀ x ∈ xs, NodeBelow store n x := by
  intro K
  induction K with
  | zero =>
    intro n t xs h x hx
    simp only [EthCLSpecs.Heze.filterNodeTree.go] at h
    rw [run_pure_eq_ok _ _ _ _ h] at hx
    simp at hx
  | succ K ih =>
    intro n t xs h x hx
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t xs h
    have hedge := getNodeChildren_run_edge store t t n cs hcs
    rcases hcase with ⟨-, -, hm⟩ | ⟨-, b, -, hm⟩
    · rcases (hm x).mp hx with ⟨rfl, -⟩ | ⟨c, hc, ys, hys, hxc⟩
      · exact .refl
      · exact NodeBelow.of_edge (hedge c (Array.mem_toList_iff.mp hc)) (ih c t ys hys x hxc)
    · obtain ⟨rfl, -⟩ := (hm x).mp hx
      exact .refl

/-- **EMPTY `r` is viable when a node below it is kept.** The node keeps EMPTY `r`
(`go_keeps_anc`), and the walk from the justified root keeps EMPTY `r` (`go_keeps_desc`). The
path from the justified root through EMPTY `r` crosses FULL nodes only at verified payloads. -/
theorem emptyViable_of_kept (store : Store map) (hslots : SlotsIncrease store)
    {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (r : EthCLSpecs.Heze.Root) (x : ForkChoiceNode) (hx : KeptAt store x)
    (hrx : NodeBelow store (.empty r) x) (hne : x ≠ .empty r)
    (hJr : NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r))
    (hver : ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) x → isPayloadVerified store z = true) :
    EmptyViableWithFull store r := by
  intro nodes t t' hrun _
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  have hbud : Budget store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root) [store.justifiedCheckpoint.root] := by
    simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_singleton]
    omega
  -- EMPTY `r` keeps itself, being a strict ancestor of the kept node.
  have hke : KeptAt store (.empty r) := by
    intro K P xb u ys hxb hP hPs hxP hbud' hys
    exact go_keeps_anc store hslots x hx K (.empty r) P xb u ys hxb hP hPs hxP hbud' hys hrx
      (Ne.symm hne) (fun z hz hzx => hver z (NodeBelow.trans store _ _ _ hJr hz) hzx)
  rw [Array.contains_iff_mem]
  exact go_keeps_desc store hslots (.empty r) hke _ _ [store.justifiedCheckpoint.root] jb t nodes hj
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun y hy => by rw [List.mem_singleton.mp hy]; exact ⟨jb, hj, UInt64.le_refl _⟩)
    (List.mem_singleton_self _) hbud hrun' hJr
    (fun z hz hze => hver z hz (NodeBelow.trans store _ _ _ hze hrx))

/-! ## The store at the slot after `r` -/

section Race
variable [EthCLLib.Spec.CryptoBackend]

/-! ### The unrealized justifications along a trace

Only `onBlock` writes `unrealizedJustifications`, through `computePulledUpTip` at the root of
the new block. The other handlers keep the map. -/

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.CryptoBackend] in
/-- `onTick` keeps the unrealized justifications. -/
theorem onTick_keeps_unrealized (v : _) (time : UInt64) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications) v
      (EthCLSpecs.Heze.onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        time) := by
  unfold EthCLSpecs.Heze.onTick
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `onAttestation` keeps the unrealized justifications. -/
theorem onAttestation_keeps_unrealized (v : _) (att : EthCLSpecs.Heze.Attestation)
    (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications) v
      (EthCLSpecs.Heze.onAttestation (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) att isFromBlock) := by
  unfold EthCLSpecs.Heze.onAttestation
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [Config] in
/-- `onAttesterSlashing` keeps the unrealized justifications. -/
theorem onAttesterSlashing_keeps_unrealized (v : _) (asl : EthCLSpecs.Heze.AttesterSlashing) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications) v
      (EthCLSpecs.Heze.onAttesterSlashing (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) asl) := by
  unfold EthCLSpecs.Heze.onAttesterSlashing
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `onPayloadAttestationMessage` keeps the unrealized justifications. -/
theorem onPayloadAttestationMessage_keeps_unrealized (v : _)
    (msg : EthCLSpecs.Heze.PayloadAttestationMessage) (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications) v
      (EthCLSpecs.Heze.onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold EthCLSpecs.Heze.onPayloadAttestationMessage
  keeps_solve

variable [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `onExecutionPayloadEnvelope` keeps the unrealized justifications. -/
theorem onExecutionPayloadEnvelope_keeps_unrealized (v : _)
    (signedEnv : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications) v
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold EthCLSpecs.Heze.onExecutionPayloadEnvelope
  keeps_solve

omit [Preset] [HasherTag] [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- An insert of the value already at a key keeps every lookup. -/
theorem lookup_insert_same {V : Type} (m : map EthCLSpecs.Heze.Root V) (k : EthCLSpecs.Heze.Root)
    (x : V) (hx : FcMap.lookup m k = some x) (k' : EthCLSpecs.Heze.Root) :
    FcMap.lookup (FcMap.insert m k x) k' = FcMap.lookup m k' := by
  by_cases hk : k = k'
  · subst hk
    rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self, hx]
  · exact EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk

/-- Each unrealized justification of the store, other than the one at the anchor root `a0`,
is the pull-up of the stored state at its root: the justified checkpoint that
`process_justification_and_finalization` gives on the state of the block
(`compute_pulled_up_tip`, `phase0/fork-choice.md:770-785`). `get_forkchoice_store` writes the
anchor checkpoint at the anchor root instead. The states of `blockStates` are uncached
boxes. -/
def UnrealInv (a0 : EthCLSpecs.Heze.Root) (s : Store map) : Prop :=
  BlockStatesPure s ∧
    ∀ k j, FcMap.lookup s.unrealizedJustifications k = some j → k = a0 ∨
      ∃ v pulled, FcMap.lookup s.blockStates k = some (pureState v) ∧
        runPure (EthCLSpecs.Heze.processJustificationAndFinalization
          (StateTransition := HezeRun)) v = .ok ((), pulled) ∧
        j = pulled.currentJustifiedCheckpoint

/-- A handler event keeps `UnrealInv`. `onBlock` on a new block writes the state of the block
and its pull-up at one root. The envelope handler stores back the state it read. The other
handlers keep both maps. -/
theorem UnrealInv.handler {a0 : EthCLSpecs.Heze.Root} {pre post : Store map}
    (hp : UnrealInv a0 pre) (e : HandlerEvent)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) : UnrealInv a0 post := by
  obtain ⟨hpure, hu⟩ := hp
  refine ⟨hpure.handler e h, ?_⟩
  -- A handler that keeps both maps keeps the second half.
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      EthCLLib.Proofs.KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications)
        pre.unrealizedJustifications x →
      x.run pre = .ok ((), post) → ∀ k j, FcMap.lookup post.unrealizedJustifications k = some j →
        k = a0 ∨ ∃ v pulled, FcMap.lookup post.blockStates k = some (pureState v) ∧
          runPure (EthCLSpecs.Heze.processJustificationAndFinalization
            (StateTransition := HezeRun)) v = .ok ((), pulled) ∧
          j = pulled.currentJustifiedCheckpoint := by
    intro x hx hxu hrun k j hj
    have hm := hx pre () post rfl hrun
    injection hm with _ hbs
    have hum : post.unrealizedJustifications = pre.unrealizedJustifications :=
      hxu pre () post rfl hrun
    rw [hum] at hj
    rw [hbs]
    exact hu k j hj
  cases e with
  | tick time =>
    exact hkeep _ (onTick_keeps_blockMaps _ time) (onTick_keeps_unrealized _ time) h
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock)
      (onAttestation_keeps_unrealized _ att isFromBlock) h
  | attesterSlashing asl =>
    exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl)
      (onAttesterSlashing_keeps_unrealized _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock)
      (onPayloadAttestationMessage_keeps_unrealized _ msg isFromBlock) h
  | envelope signedEnv =>
    obtain ⟨-, v, hv, hstates⟩ := onExecutionPayloadEnvelope_run_ok signedEnv pre post hpure h
    have hum : post.unrealizedJustifications = pre.unrealizedJustifications :=
      onExecutionPayloadEnvelope_keeps_unrealized _ signedEnv pre () post rfl h
    intro k j hj
    rw [hum] at hj
    rcases hu k j hj with h0 | ⟨v', pulled, hv', hjf, rfl⟩
    · exact .inl h0
    · exact .inr ⟨v', pulled, by rw [hstates, lookup_insert_same _ _ _ hv]; exact hv', hjf, rfl⟩
  | block sb =>
    cases hknown : FcMap.contains pre.blocks (htr sb.message)
    · obtain ⟨pv, w, u, -, -, -, hbsu, -, hpull, hunr⟩ :=
        onBlock_run_ckpt sb pre post hpure hknown h
      obtain ⟨-, -, -, -, -, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
      obtain ⟨pulled, hjf, -, pbs, -, -, -, punr⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
      have hu1 : (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).unrealizedJustifications = pre.unrealizedJustifications := by
        rw [← hunr]
        simp only [updateCheckpoints]
        repeat' split
        all_goals rfl
      intro k j hj
      rw [punr, hu1] at hj
      rw [pbs, bs1, hbsu]
      by_cases hk : htr sb.message = k
      · subst hk
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self] at hj
        injection hj with hj
        exact .inr ⟨w, pulled, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _, hjf, hj.symm⟩
      · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk] at hj
        rcases hu k j hj with h0 | ⟨v', pulled', hv', hjf', rfl⟩
        · exact .inl h0
        · exact .inr ⟨v', pulled', by
            rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk]; exact hv', hjf', rfl⟩
    · rw [onBlock_run_of_known sb pre post hknown h]
      exact hu

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- The anchor store meets `UnrealInv` at the anchor root: its only unrealized justification
sits at the anchor root. -/
theorem UnrealInv.anchor (v : EthCLSpecs.Heze.BeaconState) (a : EthCLSpecs.Heze.BeaconBlock)
    (s0 : Store map) (h : EthCLSpecs.Heze.getForkchoiceStore (pureState v) a = .ok s0) :
    UnrealInv (htr a) s0 := by
  refine ⟨BlockStatesPure.anchor v a s0 h, ?_⟩
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  intro k j hj
  by_cases hk : htr a = k
  · exact .inl hk.symm
  · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk,
      EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hj
    cases hj

/-- `UnrealInv` along a trace. -/
theorem NodeTrace.unrealInv {a0 : EthCLSpecs.Heze.Root} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) (h0 : UnrealInv a0 s0) : UnrealInv a0 s := by
  induction h with
  | nil => exact h0
  | handler e _ hrun ih => exact ih.handler e hrun
  | inclusionList signed _ _ hrun _ ih =>
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    obtain ⟨hp1, hp2⟩ := ih
    exact ⟨fun k => hp1 k, hp2⟩

/-- Every stored block root has an unrealized justification. `on_block` writes both at the new
root (`compute_pulled_up_tip`), and the anchor store holds both at the anchor root. -/
def UnrealKeys (s : Store map) : Prop :=
  ∀ k b, FcMap.lookup s.blocks k = some b → (FcMap.lookup s.unrealizedJustifications k).isSome

/-- A handler event keeps `UnrealKeys`. -/
theorem UnrealKeys.handler {pre post : Store map} (hpure : BlockStatesPure pre)
    (hp : UnrealKeys pre) (e : HandlerEvent)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) : UnrealKeys post := by
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      EthCLLib.Proofs.KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      EthCLLib.Proofs.KeepsAt (fun st : Store map => st.unrealizedJustifications)
        pre.unrealizedJustifications x →
      x.run pre = .ok ((), post) → UnrealKeys post := by
    intro x hx hxu hrun k b hk
    have hm := hx pre () post rfl hrun
    injection hm with hb _
    have hum : post.unrealizedJustifications = pre.unrealizedJustifications :=
      hxu pre () post rfl hrun
    rw [hb] at hk
    rw [hum]
    exact hp k b hk
  cases e with
  | tick time =>
    exact hkeep _ (onTick_keeps_blockMaps _ time) (onTick_keeps_unrealized _ time) h
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock)
      (onAttestation_keeps_unrealized _ att isFromBlock) h
  | attesterSlashing asl =>
    exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl)
      (onAttesterSlashing_keeps_unrealized _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock)
      (onPayloadAttestationMessage_keeps_unrealized _ msg isFromBlock) h
  | envelope signedEnv =>
    obtain ⟨hblocks, -⟩ := onExecutionPayloadEnvelope_run_ok signedEnv pre post hpure h
    have hum : post.unrealizedJustifications = pre.unrealizedJustifications :=
      onExecutionPayloadEnvelope_keeps_unrealized _ signedEnv pre () post rfl h
    intro k b hk
    rw [hblocks] at hk
    rw [hum]
    exact hp k b hk
  | block sb =>
    cases hknown : FcMap.contains pre.blocks (htr sb.message)
    · obtain ⟨pv, w, u, -, -, hbu, hbsu, -, hpull, hunr⟩ :=
        onBlock_run_ckpt sb pre post hpure hknown h
      obtain ⟨-, -, -, -, b1, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
      obtain ⟨pulled, -, pb, -, -, -, -, punr⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
      have hu1 : (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).unrealizedJustifications = pre.unrealizedJustifications := by
        rw [← hunr]
        simp only [updateCheckpoints]
        repeat' split
        all_goals rfl
      intro k b hk
      rw [pb, b1, hbu] at hk
      rw [punr, hu1]
      by_cases hk0 : htr sb.message = k
      · subst hk0
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
        rfl
      · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk0] at hk ⊢
        exact hp k b hk
    · rw [onBlock_run_of_known sb pre post hknown h]
      exact hp

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- The anchor store meets `UnrealKeys`. -/
theorem UnrealKeys.anchor (v : EthCLSpecs.Heze.BeaconState) (a : EthCLSpecs.Heze.BeaconBlock)
    (s0 : Store map) (h : EthCLSpecs.Heze.getForkchoiceStore (pureState v) a = .ok s0) :
    UnrealKeys s0 := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  intro k b hk
  by_cases hka : htr a = k
  · subst hka
    show (FcMap.lookup (FcMap.insert FcMap.empty (htr a) _) (htr a)).isSome = true
    rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
    rfl
  · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hka,
      EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
    cases hk

/-- `UnrealKeys` along a trace from a store with pure block states. -/
theorem NodeTrace.unrealKeys {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) (hp0 : BlockStatesPure s0) (h0 : UnrealKeys s0) :
    UnrealKeys s := by
  induction h with
  | nil => exact h0
  | @handler events arrs pre post e htr' hrun ih =>
    exact (ih).handler (htr'.blockStatesPure hp0) e hrun
  | inclusionList signed _ _ hrun _ ih =>
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    exact fun k b hk => ih k b hk

/-! ### A FULL parent edge has a verified payload -/

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.CryptoBackend]
  [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] [Config] in
/-- The parent status read depends on the store only through the parent's block. -/
theorem getParentPayloadStatus_run_congr {s₁ s₂ : Store map} (b : EthCLSpecs.Heze.BeaconBlock)
    (h : FcMap.lookup s₁.blocks b.parentRoot = FcMap.lookup s₂.blocks b.parentRoot)
    (u : Store map) :
    (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) s₁ b).run u =
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) s₂ b).run u := by
  simp only [EthCLSpecs.Heze.getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey, h]

/-- Every stored block whose parent edge is FULL has its parent's payload verified. `on_block`
asserts it (`gloas/fork-choice.md:1058-1061`), and payloads are never removed. -/
def FullVerified (s : Store map) : Prop :=
  ∀ k b u u', FcMap.lookup s.blocks k = some b →
    (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) s b).run u
      = .ok (EthCLSpecs.Heze.Const.payloadStatusFull, u') →
    isPayloadVerified s b.parentRoot = true

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Spec.CryptoBackend] in
/-- `onTick` keeps the payloads. -/
theorem onTick_keeps_payloads (v : _) (time : UInt64) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) v
      (EthCLSpecs.Heze.onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        time) := by
  unfold EthCLSpecs.Heze.onTick
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- `onAttestation` keeps the payloads. -/
theorem onAttestation_keeps_payloads (v : _) (att : EthCLSpecs.Heze.Attestation)
    (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) v
      (EthCLSpecs.Heze.onAttestation (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) att isFromBlock) := by
  unfold EthCLSpecs.Heze.onAttestation
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [Config] in
/-- `onAttesterSlashing` keeps the payloads. -/
theorem onAttesterSlashing_keeps_payloads (v : _) (asl : EthCLSpecs.Heze.AttesterSlashing) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) v
      (EthCLSpecs.Heze.onAttesterSlashing (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) asl) := by
  unfold EthCLSpecs.Heze.onAttesterSlashing
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- `onPayloadAttestationMessage` keeps the payloads. -/
theorem onPayloadAttestationMessage_keeps_payloads (v : _)
    (msg : EthCLSpecs.Heze.PayloadAttestationMessage) (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) v
      (EthCLSpecs.Heze.onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold EthCLSpecs.Heze.onPayloadAttestationMessage
  keeps_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- `onBlock` keeps the payloads. -/
theorem onBlock_keeps_payloads (v : _) (sb : EthCLSpecs.Heze.SignedBeaconBlock) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) v
      (EthCLSpecs.Heze.onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        sb) := by
  unfold EthCLSpecs.Heze.onBlock
  keeps_solve

/-- The envelope handler keeps the block map and adds a payload: every verified payload stays
verified. -/
theorem onExecutionPayloadEnvelope_payloads_mono
    (signedEnv : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope) (pre post : Store map)
    (h : (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post))
    (k : EthCLSpecs.Heze.Root) (hk : isPayloadVerified pre k = true) :
    isPayloadVerified post k = true := by
  unfold EthCLSpecs.Heze.onExecutionPayloadEnvelope at h
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · obtain ⟨store', _, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    have hstore' : store'.payloads = pre.payloads :=
      (?_ : EthCLLib.Proofs.Returns (fun st : Store map => st.payloads) pre.payloads _) _ _ _ hrec
    · have ht := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
      subst ht
      unfold EthCLSpecs.Heze.isPayloadVerified at hk ⊢
      show FcMap.contains (FcMap.insert store'.payloads _ _) k = true
      rw [EthCLLib.Proofs.LawfulFcMap.contains_eq_isSome_lookup] at hk ⊢
      rw [hstore']
      by_cases hkr : signedEnv.message.beaconBlockRoot = k
      · subst hkr
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
        rfl
      · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hkr]
        exact hk
    · keeps_solve

/-- A handler event keeps `FullVerified`, under `SlotInv` before and after. A new block on a
FULL edge passed the `on_block` assert on its parent's payload. An older block keeps its parent:
its parent was stored before (`SlotInv.parentIn`), or it is the anchor, whose parent is never
stored. Payloads are never removed. -/
theorem FullVerified.handler {a : EthCLSpecs.Heze.BeaconBlock} {pre post : Store map}
    (hslot : SlotInv a pre) (hslot' : SlotInv a post) (hp : FullVerified pre) (e : HandlerEvent)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) : FullVerified post := by
  -- A handler that keeps the blocks and the payloads keeps the invariant.
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      EthCLLib.Proofs.KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      EthCLLib.Proofs.KeepsAt (fun st : Store map => st.payloads) pre.payloads x →
      x.run pre = .ok ((), post) → FullVerified post := by
    intro x hx hxp hrun k b u u' hk hs
    have hm := hx pre () post rfl hrun
    injection hm with hb _
    have hpl : post.payloads = pre.payloads := hxp pre () post rfl hrun
    rw [hb] at hk
    rw [getParentPayloadStatus_run_congr (s₂ := pre) b (by rw [hb]) u] at hs
    unfold EthCLSpecs.Heze.isPayloadVerified
    rw [hpl]
    exact hp k b u u' hk hs
  cases e with
  | tick time => exact hkeep _ (onTick_keeps_blockMaps _ time) (onTick_keeps_payloads _ time) h
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock)
      (onAttestation_keeps_payloads _ att isFromBlock) h
  | attesterSlashing asl =>
    exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl)
      (onAttesterSlashing_keeps_payloads _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock)
      (onPayloadAttestationMessage_keeps_payloads _ msg isFromBlock) h
  | envelope signedEnv =>
    obtain ⟨hblocks, -⟩ := onExecutionPayloadEnvelope_run_ok signedEnv pre post hslot.statesPure h
    intro k b u u' hk hs
    rw [hblocks] at hk
    rw [getParentPayloadStatus_run_congr (s₂ := pre) b (by rw [hblocks]) u] at hs
    exact onExecutionPayloadEnvelope_payloads_mono signedEnv pre post h _ (hp k b u u' hk hs)
  | block sb =>
    cases hknown : FcMap.contains pre.blocks (htr sb.message)
    · obtain ⟨pv, w, u0, hps, -, hbu, hbsu, -, hpull, -⟩ :=
        onBlock_run_ckpt sb pre post hslot.statesPure hknown h
      obtain ⟨-, -, -, -, b1, bs1⟩ :=
        updateCheckpoints_ckpt u0 w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u0 w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
      obtain ⟨-, -, pb, -⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
      have hpb : post.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message := by
        rw [pb, b1, hbu]
      have hpl : post.payloads = pre.payloads := onBlock_keeps_payloads pre.payloads sb pre () post rfl h
      -- A stored root of `pre` is not the new root.
      have hold : ∀ x xb, FcMap.lookup pre.blocks x = some xb → x ≠ htr sb.message := by
        intro x xb hx hxn
        subst hxn
        have hc : FcMap.contains pre.blocks (htr sb.message) = true := by
          rw [EthCLLib.Proofs.LawfulFcMap.contains_eq_isSome_lookup, hx]
          rfl
        rw [hknown] at hc
        cases hc
      intro k b u u' hk hs
      rw [hpb] at hk
      unfold EthCLSpecs.Heze.isPayloadVerified
      rw [hpl]
      by_cases hk0 : htr sb.message = k
      · -- The new block: the `on_block` assert on its parent's payload.
        subst hk0
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self] at hk
        injection hk with hk
        subst hk
        obtain ⟨pbk, hpbk⟩ := hslot.stateKeys _ (by rw [hps]; rfl)
        have hpne := hold _ _ hpbk
        rw [getParentPayloadStatus_run_congr (s₂ := pre) sb.message (by
          rw [hpb, EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hpne)]) u] at hs
        obtain ⟨full, -, hfull, hver, -, -⟩ := onBlock_run_ok_asserts sb pre post hknown h
        unfold EthCLSpecs.Heze.isParentNodeFull at hfull
        obtain ⟨v, s2, hv, hfull⟩ := run_bind_eq_ok _ _ _ _ hfull
        have hvf := getParentPayloadStatus_run_val pre _ _ _ _ sb.message _ _ hv hs
        have hft : full = true := by
          rw [run_pure_eq_ok _ _ _ _ hfull, hvf]
          rfl
        rw [hft] at hver
        exact hver
      · -- An older block keeps its parent.
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk0] at hk
        rcases hslot.parentIn k b hk with rfl | ⟨pbk, hpbk⟩
        · -- The anchor: its parent is not stored, so the read fails.
          have hnone := hslot'.anchorParent
          simp only [EthCLSpecs.Heze.getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey,
            hnone] at hs
          cases hs
        · have hpne := hold _ _ hpbk
          rw [getParentPayloadStatus_run_congr (s₂ := pre) b (by
            rw [hpb, EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hpne)]) u] at hs
          exact hp k b u u' hk hs
    · rw [onBlock_run_of_known sb pre post hknown h]
      exact hp

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- The anchor store meets `FullVerified`: its only block is the anchor, whose parent is not
stored, so its parent status read fails. -/
theorem FullVerified.anchor (v : EthCLSpecs.Heze.BeaconState) (a : EthCLSpecs.Heze.BeaconBlock)
    (s0 : Store map) (h : EthCLSpecs.Heze.getForkchoiceStore (pureState v) a = .ok s0)
    (hself : a.parentRoot ≠ htr a) : FullVerified s0 := by
  have hslot := SlotInv.anchor v a s0 h hself
  intro k b u u' hk hs
  rcases hslot.parentIn k b hk with rfl | ⟨pb, hpb⟩
  · simp only [EthCLSpecs.Heze.getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey,
      hslot.anchorParent] at hs
    cases hs
  · -- The anchor store holds only the anchor, at its root.
    simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
    obtain ⟨_, -, h⟩ := except_bind_eq_ok h
    obtain ⟨_, -, h⟩ := except_bind_eq_ok h
    cases h
    have hb : k = htr a ∧ b = a := by
      by_cases hka : htr a = k
      · subst hka
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self] at hk
        exact ⟨rfl, (Option.some.inj hk).symm⟩
      · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hka,
          EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
        cases hk
    obtain ⟨-, rfl⟩ := hb
    have := hslot.anchorParent
    rw [hpb] at this
    cases this

/-- `FullVerified` with `SlotInv` along a trace, or a root collision. -/
theorem NodeTrace.fullVerified
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {a : EthCLSpecs.Heze.BeaconBlock} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) (h0 : SlotInv a s0) (hf0 : FullVerified s0)
    (hev : ∀ e, TraceEvent.handler e ∈ events → e.NotAtAnchorParent a) :
    (SlotInv a s ∧ FullVerified s) ∨ RootCollision := by
  revert hev
  induction h with
  | nil => intro _; exact .inl ⟨h0, hf0⟩
  | handler e _ hrun ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with ⟨hinv, hf⟩ | hc
    · rcases hinv.handler hw e (hev e (List.mem_append_right _ (List.mem_singleton_self _)))
          hrun with hinv' | hc
      · exact .inl ⟨hinv', hf.handler hinv hinv' e hrun⟩
      · exact .inr hc
    · exact .inr hc
  | inclusionList signed _ _ hrun _ ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with ⟨hinv, hf⟩ | hc
    · -- `onInclusionList` writes only the IL store.
      obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
      rw [hs']
      exact .inl ⟨hinv.of_blocks_eq rfl (fun _ hk => hk) hinv.statesPure,
        fun k b u u' hk hs => hf k b u u' hk hs⟩
    · exact .inr hc

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [Config] in
/-- Under `FullVerified`, a FULL node above a pending node has a verified payload: the path
leaves the FULL node through a block on a FULL edge. -/
theorem FullVerified.path {s : Store map} (hf : FullVerified s) (z : EthCLSpecs.Heze.Root)
    (T : EthCLSpecs.Heze.Root) (h : NodeBelow s (.full z) (.pending T)) :
    isPayloadVerified s z = true := by
  rcases NodeBelow.head h with heq | ⟨c, hedge, -⟩
  · exact absurd (congrArg ForkChoiceNode.payloadStatus heq) (Ne.symm payloadStatus_full_ne_pending)
  · cases hedge with
    | block parent root b u u' hl hp hs =>
      have hp' : b.parentRoot = z := hp
      rw [← hp']
      exact hf root b u u' hl hs

/-! ### The state of a block and the state of its parent -/

/-- Each block of the store other than the anchor `a0` has its parent's state and its own state
in `blockStates`, and the state transition of the block takes the first to the second. This is
what `on_block` records (`gloas/fork-choice.md:1079-1082`). -/
def StateLink (a0 : EthCLSpecs.Heze.Root) (s : Store map) : Prop :=
  ∀ k b, FcMap.lookup s.blocks k = some b → k ≠ a0 →
    ∃ (sb : EthCLSpecs.Heze.SignedBeaconBlock) (pv w : EthCLSpecs.Heze.BeaconState),
      sb.message = b ∧ FcMap.lookup s.blockStates b.parentRoot = some (pureState pv) ∧
      FcMap.lookup s.blockStates k = some (pureState w) ∧
      (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
        = .ok ((), pureState w)

omit [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- The anchor store meets `StateLink` at the anchor root: its only block is the anchor. -/
theorem StateLink.anchor (v : EthCLSpecs.Heze.BeaconState) (a : EthCLSpecs.Heze.BeaconBlock)
    (s0 : Store map) (h : EthCLSpecs.Heze.getForkchoiceStore (pureState v) a = .ok s0) :
    StateLink (htr a) s0 := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  intro k b hk hne
  rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hne),
    EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
  cases hk

/-- A handler event keeps `StateLink`, under `SlotInv`. `onBlock` on a new block adds the block
and its state at a new root; its parent has a state, so the parent is a stored block and not
the new root. The envelope handler stores back the state it read. The other handlers keep both
maps. -/
theorem StateLink.handler {a : EthCLSpecs.Heze.BeaconBlock} {a0 : EthCLSpecs.Heze.Root}
    {pre post : Store map} (hslot : SlotInv a pre) (hl : StateLink a0 pre) (e : HandlerEvent)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) : StateLink a0 post := by
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      EthCLLib.Proofs.KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      x.run pre = .ok ((), post) → StateLink a0 post := by
    intro x hx hrun
    have hm := hx pre () post rfl hrun
    injection hm with hb hbs
    intro k b hk hne
    rw [hb] at hk
    rw [hbs]
    exact hl k b hk hne
  cases e with
  | tick time => exact hkeep _ (onTick_keeps_blockMaps _ time) h
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) h
  | attesterSlashing asl => exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) h
  | envelope signedEnv =>
    obtain ⟨hblocks, v, hv, hstates⟩ :=
      onExecutionPayloadEnvelope_run_ok signedEnv pre post hslot.statesPure h
    intro k b hk hne
    rw [hblocks] at hk
    obtain ⟨sb, pv, w, hsb, hp, hw, ht⟩ := hl k b hk hne
    refine ⟨sb, pv, w, hsb, ?_, ?_, ht⟩
    · rw [hstates, lookup_insert_same _ _ _ hv]; exact hp
    · rw [hstates, lookup_insert_same _ _ _ hv]; exact hw
  | block sb =>
    cases hknown : FcMap.contains pre.blocks (htr sb.message)
    · obtain ⟨pv, w, u, hps, htrans, hbu, hbsu, -, hpull, -⟩ :=
        onBlock_run_ckpt sb pre post hslot.statesPure hknown h
      obtain ⟨-, -, -, -, b1, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl1 : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
      obtain ⟨-, -, pb, pbs, -⟩ := computePulledUpTip_run_ok _ w _ post hl1 hpull
      have hpb : post.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message := by
        rw [pb, b1, hbu]
      have hpbs : post.blockStates =
          FcMap.insert pre.blockStates (htr sb.message) (pureState w) := by
        rw [pbs, bs1, hbsu]
      -- A root with a state is a stored block, so it is not the new root.
      have hnot : ∀ k, (FcMap.lookup pre.blockStates k).isSome → k ≠ htr sb.message := by
        intro k hk hkn
        obtain ⟨x, hx⟩ := hslot.stateKeys k hk
        subst hkn
        have hc : FcMap.contains pre.blocks (htr sb.message) = true := by
          rw [EthCLLib.Proofs.LawfulFcMap.contains_eq_isSome_lookup, hx]
          rfl
        rw [hknown] at hc
        cases hc
      have hpar : sb.message.parentRoot ≠ htr sb.message := hnot _ (by rw [hps]; rfl)
      intro k b hk hne
      rw [hpb] at hk
      rw [hpbs]
      by_cases hk0 : htr sb.message = k
      · subst hk0
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self] at hk
        injection hk with hk
        subst hk
        refine ⟨sb, pv, w, rfl, ?_, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _, htrans⟩
        rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hpar)]
        exact hps
      · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk0] at hk
        obtain ⟨sb', pv', w', hsb, hp, hw, ht⟩ := hl k b hk hne
        have hpne : b.parentRoot ≠ htr sb.message := hnot _ (by rw [hp]; rfl)
        refine ⟨sb', pv', w', hsb, ?_, ?_, ht⟩
        · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hpne)]; exact hp
        · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne _ _ _ _ hk0]; exact hw
    · rw [onBlock_run_of_known sb pre post hknown h]
      exact hl

/-- `StateLink` with `SlotInv` along a trace, or a root collision. -/
theorem NodeTrace.stateLink
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {a : EthCLSpecs.Heze.BeaconBlock} {a0 : EthCLSpecs.Heze.Root} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) (h0 : SlotInv a s0) (hl0 : StateLink a0 s0)
    (hev : ∀ e, TraceEvent.handler e ∈ events → e.NotAtAnchorParent a) :
    (SlotInv a s ∧ StateLink a0 s) ∨ RootCollision := by
  revert hev
  induction h with
  | nil => intro _; exact .inl ⟨h0, hl0⟩
  | handler e _ hrun ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with ⟨hinv, hl⟩ | hc
    · rcases hinv.handler hw e (hev e (List.mem_append_right _ (List.mem_singleton_self _)))
          hrun with hinv' | hc
      · exact .inl ⟨hinv', hl.handler hinv e hrun⟩
      · exact .inr hc
    · exact .inr hc
  | inclusionList signed _ _ hrun _ ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with ⟨hinv, hl⟩ | hc
    · -- `onInclusionList` writes only the IL store.
      obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
      rw [hs']
      exact .inl ⟨hinv.of_blocks_eq rfl (fun _ hk => hk) hinv.statesPure, fun k b hk hne => hl k b hk hne⟩
    · exact .inr hc

/-! ### The justified checkpoint across `process_slot` -/

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [Config] [EthCLLib.Spec.CryptoBackend] in
/-- A successful `get_block_root` read: the epoch has a start slot, before the state slot and
within the ring buffer, and the root is the ring-buffer entry of that slot. -/
theorem getBlockRoot_run_vmod {u x : EthCLSpecs.Heze.BeaconState} {e : EthCLSpecs.Heze.Epoch}
    {r : EthCLSpecs.Heze.Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u) e) u
      = .ok (r, x)) :
    ∃ s, (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
        Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok s ∧
      s.toNat < u.slot.toNat ∧
      u.slot.toNat ≤ s.toNat + EthCLSpecs.Heze.Const.slotsPerHistoricalRoot ∧
      r = EthCLLib.Spec.vmodGet u.blockRoots s EthCLSpecs.Heze.Const.slotsPerHistoricalRoot := by
  cases hs : (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) with
  | error err =>
    unfold EthCLSpecs.Heze.getBlockRoot at h
    rw [hs] at h
    cases h
  | ok s =>
    have h' : runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
        (pureState u) s) u = .ok (r, x) := by
      unfold EthCLSpecs.Heze.getBlockRoot at h
      rw [hs] at h
      exact h
    obtain ⟨h1, h2, h3, -⟩ := getBlockRootAtSlot_run_ok h'
    exact ⟨s, rfl, h1, h2, h3⟩

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- **The justification step gives one justified checkpoint before and after `process_slot`**,
at the last slot of an epoch. `process_slot` writes the ring-buffer entry of the state slot,
the state root entry, the header, and the payload availability bit (`slotWrite`). The step
reads the balances and the participation, which `slotWrite` keeps, and the block roots of the
first slots of the previous and the current epoch. Those slots are less than
`SLOTS_PER_HISTORICAL_ROOT` before the state slot, so their entries differ from the one
`slotWrite` writes. This is why the pull-up of a block (`compute_pulled_up_tip`) and the epoch
processing of its child at the next epoch agree on the justified checkpoint. -/
theorem pjf_cj_slotWrite (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤
      EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    {u a b : EthCLSpecs.Heze.BeaconState}
    (ha : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) u = .ok ((), a))
    (hb : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) (slotWrite u) = .ok ((), b)) :
    a.currentJustifiedCheckpoint = b.currentJustifiedCheckpoint := by
  by_cases hg : EthCLSpecs.Heze.currentEpochOf (pureState u) ≤
      EthCLSpecs.Heze.Const.genesisEpoch + 1
  · -- The first two epochs: the step keeps both states, and `slotWrite` keeps the field.
    have hg' : EthCLSpecs.Heze.currentEpochOf (pureState (slotWrite u)) ≤
        EthCLSpecs.Heze.Const.genesisEpoch + 1 := hg
    rw [processJustificationAndFinalization_run_eq, ite_eq_left hg] at ha
    rw [processJustificationAndFinalization_run_eq, ite_eq_left hg'] at hb
    injection ha with ha
    injection ha with _ ha
    injection hb with hb
    injection hb with _ hb
    subst ha hb
    rfl
  · obtain ⟨pi, ci, tot, prev, curr, h1, h2, h3, h4, h5, hwa⟩ :=
      processJustificationAndFinalization_run_ok ha hg
    obtain ⟨pi', ci', tot', prev', curr', h1', h2', h3', h4', h5', hwb⟩ :=
      processJustificationAndFinalization_run_ok hb hg
    -- `slotWrite` keeps the five reads, so they return the same values.
    -- The reads on `slotWrite u` unfold to the reads on `u` (`rfl`), so `Eq.trans` matches them.
    have e1 : pi = pi' := Except.ok.inj (h1.symm.trans h1')
    subst e1
    have e2 : ci = ci' := Except.ok.inj (h2.symm.trans h2')
    subst e2
    have e3 : tot = tot' := Except.ok.inj (h3.symm.trans h3')
    subst e3
    have e4 : prev = prev' := Except.ok.inj (h4.symm.trans h4')
    subst e4
    have e5 : curr = curr' := Except.ok.inj (h5.symm.trans h5')
    subst e5
    obtain ⟨pr, cr, -, hca, -, -, hpa, hcca⟩ := weighJustificationAndFinalization_run_ok _ _ _ _ _ hwa
    obtain ⟨pr', cr', -, hcb, -, -, hpb, hccb⟩ :=
      weighJustificationAndFinalization_run_ok _ _ _ _ _ hwb
    -- A root read on `slotWrite u` reads the entry of `u`: the start slot is before the
    -- state slot and less than two epochs back.
    have hE : (EthCLSpecs.Heze.currentEpochOf (pureState u)).toNat =
        u.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := currentEpochOf_toNat u
    have hP := previousEpochOf_toNat_sub u
    have hspe := EthCLSpecs.Heze.Const.slotsPerEpochPos
    have hread : ∀ (e : EthCLSpecs.Heze.Epoch) (x y : EthCLSpecs.Heze.Root)
        (u1 u2 : EthCLSpecs.Heze.BeaconState),
        u.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤ e.toNat + 1 →
        runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u) e) u
          = .ok (x, u1) →
        runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun)
          (pureState (slotWrite u)) e) (slotWrite u) = .ok (y, u2) → x = y := by
      intro e x y u1 u2 he hx hy
      obtain ⟨s, hs, hlt, -, rfl⟩ := getBlockRoot_run_vmod hx
      obtain ⟨s', hs', -, -, rfl⟩ := getBlockRoot_run_vmod hy
      rw [hs] at hs'
      injection hs' with hs'
      subst hs'
      -- The start slot is `e * SLOTS_PER_EPOCH`, which fits, since the read succeeded.
      have hfit : e.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch < 2 ^ 64 :=
        Nat.lt_of_not_le fun hge => computeStartSlotAtEpoch_not_ok_of_ge hge hs
      have hsn : s.toNat = e.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch := by
        rw [computeStartSlotAtEpoch_ok_eq hs]
        exact epochStart_toNat e hfit
      -- The state slot is before the end of epoch `e + 1`, and two epochs fit in the ring.
      have hwin : u.slot.toNat < s.toNat + EthCLSpecs.Heze.Const.slotsPerHistoricalRoot := by
        have h1 := Nat.lt_div_mul_add (a := u.slot.toNat) hspe
        have h2 := Nat.mul_le_mul_right EthCLSpecs.Heze.Const.slotsPerEpoch he
        rw [Nat.succ_mul] at h2
        rw [hsn]
        omega
      change EthCLLib.Spec.vmodGet u.blockRoots s EthCLSpecs.Heze.Const.slotsPerHistoricalRoot _ =
        EthCLLib.Spec.vmodGet (u.blockRoots.set! (EthCLLib.Spec.umodIdx u.slot
          EthCLSpecs.Heze.Const.slotsPerHistoricalRoot) (htr (filledHeader u))) s
          EthCLSpecs.Heze.Const.slotsPerHistoricalRoot _
      rw [vmodGet_set!, ite_eq_right (mod_ne_of_lt hlt hwin)]
    rw [hca, hcb]
    -- The two tests read the same balances, so they agree; the roots agree by `hread`.
    split
    · rename_i hjc
      rw [hread _ cr cr' u (slotWrite u) (by rw [hE]; omega) (hcca hjc) (hccb hjc)]
      rfl
    · split
      · rename_i hjp
        rw [hread _ pr pr' u (slotWrite u) (by rw [hP]; omega) (hpa hjp) (hpb hjp)]
        rfl
      · rfl

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- **The justified checkpoint of a block one slot after its parent's state.** The transition
runs one slot step and the block step. When the slot step ends no epoch, it keeps the four
checkpoint fields. When it ends an epoch, it runs the justification step on `slotWrite` of the
parent state, which gives the justified checkpoint of the pull-up of the parent state
(`pjf_cj_slotWrite`). The block step keeps the fields. -/
theorem child_cj (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤
      EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    {sb : EthCLSpecs.Heze.SignedBeaconBlock} {pv w : EthCLSpecs.Heze.BeaconState}
    (ht : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
      = .ok ((), pureState w))
    (hslot : sb.message.slot.toNat = pv.slot.toNat + 1) (hlt : pv.slot.toNat + 1 < 2 ^ 64) :
    ((pv.slot.toNat + 1) % EthCLSpecs.Heze.Const.slotsPerEpoch ≠ 0 →
        w.currentJustifiedCheckpoint = pv.currentJustifiedCheckpoint) ∧
      ((pv.slot.toNat + 1) % EthCLSpecs.Heze.Const.slotsPerEpoch = 0 →
        ∀ pulled, runPure (EthCLSpecs.Heze.processJustificationAndFinalization
          (StateTransition := HezeRun)) pv = .ok ((), pulled) →
        w.currentJustifiedCheckpoint = pulled.currentJustifiedCheckpoint) := by
  have hle : sb.message.slot.toNat ≤ 2 ^ 64 - 1 := by omega
  obtain ⟨k, hrun⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1) hle pv w ht
  obtain ⟨m, h1, h2⟩ := hrun.split
  -- The block step ends the run.
  have hb : BlockStep sb true m w := by
    cases h2 with
    | block _ _ hstep hrest => cases hrest; exact hstep
  obtain ⟨hws, hbs⟩ := hb.slot
  -- Exactly one slot step: the block slot is one past the parent state slot.
  have hstep : SlotStep pv m := by
    match k, h1 with
    | 0, h1 =>
      cases h1
      omega
    | 1, h1 =>
      cases h1 with
      | slot _ hs hrest => cases hrest; exact hs
    | j + 2, h1 =>
      exfalso
      cases h1 with
      | slot hlt1 hs1 hrest1 =>
        cases hrest1 with
        | slot hlt2 hs2 hrest2 =>
          have e1 := hs1.slot (by omega)
          -- `hlt2` bounds the slot through the box view, which is the slot field by `rfl`.
          have e2 := hs2.slot (Nat.lt_of_lt_of_le (Nat.succ_lt_succ hlt2)
            (Nat.le_of_eq (by decide)))
          have e3 := (hrest2.slot_le (Nat.le_refl _)).1
          omega
  have hbck : ckView (pureState w) = ckView (pureState m) := by
    have e := processBlock_frame_ord hb.2.1
    simp only [ordView, Prod.mk.injEq] at e
    exact e.1
  refine ⟨fun hnb => ?_, fun hbd pulled hp => ?_⟩
  · have hm := hstep.ckView_of_not_boundary hlt hnb
    have := congrArg (fun x => x.2.1) (hbck.trans hm)
    exact this
  · obtain ⟨mid, hmid, hck⟩ := hstep.boundary hlt hbd
    have := congrArg (fun x => x.2.1) (hbck.trans hck)
    change w.currentJustifiedCheckpoint = mid.currentJustifiedCheckpoint at this
    rw [this]
    exact (pjf_cj_slotWrite hsph hp hmid).symm

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- The state after the transition of a block has the slot of the block. -/
theorem transition_slot {sb : EthCLSpecs.Heze.SignedBeaconBlock}
    {pv w : EthCLSpecs.Heze.BeaconState}
    (ht : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
      = .ok ((), pureState w)) :
    w.slot.toNat = sb.message.slot.toNat := by
  obtain ⟨k, hrun⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
    (by have := sb.message.slot.toNat_lt; omega) pv w ht
  obtain ⟨m, -, h2⟩ := hrun.split
  cases h2 with
  | block _ _ hstep hrest =>
    cases hrest
    obtain ⟨e1, e2⟩ := hstep.slot
    omega

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A `getOrThrow` read of a key with an entry returns the entry and keeps the store. -/
theorem getOrThrow_run_of_lookup {V : Type} (mp : map EthCLSpecs.Heze.Root V)
    (k : EthCLSpecs.Heze.Root) (v : V) (hk : FcMap.lookup mp k = some v) (s : Store map) :
    (FcMap.getOrThrow mp k : ForkChoiceStoreRun (Store map) V).run s = .ok (v, s) := by
  unfold FcMap.getOrThrow FcMap.getOrThrowKey
  rw [hk]
  rfl

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `get_voting_source` of a block from an earlier epoch reads the unrealized justification. -/
theorem getVotingSource_run_unreal (store : Store map) (x : EthCLSpecs.Heze.Root)
    (b : EthCLSpecs.Heze.BeaconBlock) (hb : FcMap.lookup store.blocks x = some b)
    (E : EthCLSpecs.Heze.Epoch) (u : Store map)
    (hE : (getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u
      = .ok (E, u))
    (hgt : E > EthCLSpecs.Heze.computeEpochAtSlot b.slot) (j : EthCLSpecs.Heze.Checkpoint)
    (hj : FcMap.lookup store.unrealizedJustifications x = some j) :
    (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store x).run u
      = .ok (j, u) := by
  unfold EthCLSpecs.Heze.getVotingSource
  rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hb, except_bind_ok]
  dsimp only
  rw [EthCLLib.Proofs.run_bind, hE, except_bind_ok]
  dsimp only
  rw [ite_eq_left hgt]
  exact getOrThrow_run_of_lookup _ _ _ hj u

omit [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload
  EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `get_voting_source` of a block from the current epoch reads the justified checkpoint of
its stored state. -/
theorem getVotingSource_run_state (store : Store map) (x : EthCLSpecs.Heze.Root)
    (b : EthCLSpecs.Heze.BeaconBlock) (hb : FcMap.lookup store.blocks x = some b)
    (E : EthCLSpecs.Heze.Epoch) (u : Store map)
    (hE : (getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u
      = .ok (E, u))
    (hle : ¬ E > EthCLSpecs.Heze.computeEpochAtSlot b.slot) (w : EthCLSpecs.Heze.BeaconState)
    (hw : FcMap.lookup store.blockStates x = some (pureState w)) :
    (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store x).run u
      = .ok (w.currentJustifiedCheckpoint, u) := by
  unfold EthCLSpecs.Heze.getVotingSource
  rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hb, except_bind_ok]
  dsimp only
  rw [EthCLLib.Proofs.run_bind, hE, except_bind_ok]
  dsimp only
  rw [ite_eq_right hle, EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hw,
    except_bind_ok]
  rfl

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- **The voting source of a child of `r` at the slot after `r` is the voting source of `r`.**
The current slot is `r.slot + 1`, the slot of the child. The child reads the justified
checkpoint of its state. Without an epoch boundary, `r` reads the justified checkpoint of its
own state, and the child's transition keeps it. At a boundary, `r` is from the previous epoch
and reads its unrealized justification, the pull-up of its state, which the child's epoch
processing computes too (`child_cj`). -/
theorem getVotingSource_child_eq
    (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (store : Store map) {a0 r c : EthCLSpecs.Heze.Root} {rb cb : EthCLSpecs.Heze.BeaconBlock}
    {cs : EthCLSpecs.Heze.Slot}
    (hcs : ∀ u, (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run u = .ok (cs, u))
    (hcsr : cs.toNat = rb.slot.toNat + 1) (hrb : FcMap.lookup store.blocks r = some rb)
    (hr0 : r ≠ a0) (hc : FcMap.lookup store.blocks c = some cb) (hp : cb.parentRoot = r)
    (hc0 : c ≠ a0) (hcslot : cb.slot.toNat = rb.slot.toNat + 1)
    (hlink : StateLink a0 store) (hunr : UnrealInv a0 store) (hkeys : UnrealKeys store) :
    ∀ u, (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store c).run u
      = (getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map)) store r).run u := by
  intro u
  have hE : (getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u
      = .ok (EthCLSpecs.Heze.computeEpochAtSlot cs, u) := by
    unfold EthCLSpecs.Heze.getCurrentStoreEpoch
    rw [EthCLLib.Proofs.run_bind, hcs u, except_bind_ok]
    rfl
  have hEn := computeEpochAtSlot_toNat cs
  have hcb := computeEpochAtSlot_toNat cb.slot
  have hrbn := computeEpochAtSlot_toNat rb.slot
  -- The two states: `r`'s and the child's.
  obtain ⟨sbr, pvr, wr, hsbr, -, hwr, htr_r⟩ := hlink r rb hrb hr0
  obtain ⟨sbc, pvc, wc, hsbc, hpc, hwc, htr_c⟩ := hlink c cb hc hc0
  rw [hp, hwr] at hpc
  injection hpc with hpc
  have hpc' := pureState_inj hpc
  subst hpc'
  have hwrs : wr.slot.toNat = rb.slot.toNat := by rw [transition_slot htr_r, hsbr]
  -- The child reads its own state.
  have hcle : ¬ EthCLSpecs.Heze.computeEpochAtSlot cs >
      EthCLSpecs.Heze.computeEpochAtSlot cb.slot := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hEn, hcb, hcsr, hcslot]
    exact Nat.lt_irrefl _
  rw [getVotingSource_run_state store c cb hc _ u hE hcle wc hwc]
  have hcc := child_cj hsph htr_c (by rw [hsbc, hcslot, hwrs]) (by
    have := cb.slot.toNat_lt
    omega)
  by_cases hbd : (wr.slot.toNat + 1) % EthCLSpecs.Heze.Const.slotsPerEpoch = 0
  · -- A boundary: `r` is from the previous epoch.
    have hgt : EthCLSpecs.Heze.computeEpochAtSlot cs > EthCLSpecs.Heze.computeEpochAtSlot rb.slot := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hEn, hrbn, hcsr, ← hwrs, succ_div_of_mod_eq hbd]
      exact Nat.lt_succ_self _
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hkeys r rb hrb)
    rw [getVotingSource_run_unreal store r rb hrb _ u hE hgt j hj]
    rcases hunr.2 r j hj with h0 | ⟨v, pulled, hv, hjf, rfl⟩
    · exact absurd h0 hr0
    · rw [hwr] at hv
      injection hv with hv
      have hv' := pureState_inj hv
      subst hv'
      rw [hcc.2 hbd pulled hjf]
  · -- No boundary: `r` is from the current epoch.
    have hle : ¬ EthCLSpecs.Heze.computeEpochAtSlot cs > EthCLSpecs.Heze.computeEpochAtSlot rb.slot := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hEn, hrbn, hcsr, ← hwrs, succ_div_of_mod_ne hbd]
      exact Nat.lt_irrefl _
    rw [getVotingSource_run_state store r rb hrb _ u hE hle wr hwr, hcc.1 hbd]

/-! ### The checkpoint block of a child and of its parent -/

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The walk step at a block no later than the target slot stops at the node. -/
theorem ancStep_run_done (store : Store map) (S : EthCLSpecs.Heze.Slot) (m : ForkChoiceNode)
    (b : EthCLSpecs.Heze.BeaconBlock) (hb : FcMap.lookup store.blocks m.root = some b)
    (hle : ¬ b.slot > S) (u : Store map) :
    (ancStep store S m).run u = .ok (.done m, u) := by
  unfold ancStep
  rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hb, except_bind_ok]
  dsimp only
  rw [ite_eq_right hle]
  rfl

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The walk step at a block later than the target slot runs the parent status read, and on
success steps to the parent node. -/
theorem ancStep_run_above_eq (store : Store map) (S : EthCLSpecs.Heze.Slot) (m : ForkChoiceNode)
    (b : EthCLSpecs.Heze.BeaconBlock) (hb : FcMap.lookup store.blocks m.root = some b)
    (hgt : b.slot > S) (u : Store map) :
    (ancStep store S m).run u =
      ((getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run u
        ).bind fun p => .ok (.next { root := b.parentRoot, payloadStatus := p.1 }, p.2) := by
  unfold ancStep
  rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hb, except_bind_ok]
  dsimp only
  rw [ite_eq_left hgt, EthCLLib.Proofs.run_bind]
  rfl

/-- The root and the store of a walk result. -/
abbrev rootOf (x : Except EthCLLib.Spec.StoreTransitionError (ForkChoiceNode × Store map)) :
    Except EthCLLib.Spec.StoreTransitionError (EthCLSpecs.Heze.Root × Store map) :=
  x.map fun p => (p.1.root, p.2)

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **Two `getAncestor` walks from one root end at one root.** The walk step reads only the
root of the node, so two walks from nodes with the same root take the same steps. The chain
`L` of roots below `x` with blocks later than the target slot has distinct roots (slots
decrease along parent links), so a fuel above its length is enough for both walks. -/
theorem anc_walk_root (store : Store map) (hslots : SlotsIncrease store)
    (S : EthCLSpecs.Heze.Slot) :
    ∀ (k : Nat) (x : EthCLSpecs.Heze.Root) (bx : EthCLSpecs.Heze.BeaconBlock),
      FcMap.lookup store.blocks x = some bx → bx.slot.toNat < k →
      ∃ L : List EthCLSpecs.Heze.Root, L.Nodup ∧
        (∀ y ∈ L, ∃ yb : EthCLSpecs.Heze.BeaconBlock,
          FcMap.lookup store.blocks y = some yb ∧ yb.slot ≤ bx.slot) ∧
        ∀ (f1 f2 : Nat) (m1 m2 e1 e2 : ForkChoiceNode) (u : Store map),
          m1.root = x → m2.root = x → L.length < f1 → L.length < f2 →
          rootOf ((fuelLoop f1 m1 e1 (ancStep store S)).run u) =
            rootOf ((fuelLoop f2 m2 e2 (ancStep store S)).run u) := by
  intro k
  induction k with
  | zero => intro x bx _ h; omega
  | succ k ih =>
    intro x bx hx hk
    by_cases hgt : bx.slot > S
    · -- A block above the target: the walk reads the parent status and moves to the parent.
      cases hpar : FcMap.lookup store.blocks bx.parentRoot with
      | none =>
        -- The parent read fails, at once for both walks.
        refine ⟨[x], List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun y hy => ⟨bx, by rw [List.mem_singleton.mp hy]; exact hx, UInt64.le_refl _⟩, ?_⟩
        intro f1 f2 m1 m2 e1 e2 u hm1 hm2 hf1 hf2
        obtain ⟨f1, rfl⟩ : ∃ f, f1 = f + 1 := ⟨f1 - 1, by simp at hf1; omega⟩
        obtain ⟨f2, rfl⟩ : ∃ f, f2 = f + 1 := ⟨f2 - 1, by simp at hf2; omega⟩
        simp only [fuelLoop, EthCLLib.Proofs.run_bind,
          ancStep_run_above_eq store S m1 bx (hm1 ▸ hx) hgt,
          ancStep_run_above_eq store S m2 bx (hm2 ▸ hx) hgt]
        cases hps : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
            store bx).run u with
        | error err => rfl
        | ok p =>
          obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent store u p.2 bx p.1 hps
          rw [hpar] at hpb
          cases hpb
      | some pb =>
        have hpslot : pb.slot < bx.slot := hslots x bx pb hx hpar
        obtain ⟨L, hnd, hL, hwalk⟩ := ih bx.parentRoot pb hpar (by
          have := UInt64.lt_iff_toNat_lt.mp hpslot
          omega)
        have hxL : x ∉ L := by
          intro hxL
          obtain ⟨yb, hyb, hle⟩ := hL x hxL
          rw [hx] at hyb
          cases hyb
          exact absurd (UInt64.lt_of_le_of_lt hle hpslot) (UInt64.lt_irrefl _)
        refine ⟨x :: L, List.nodup_cons.mpr ⟨hxL, hnd⟩, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨bx, hx, UInt64.le_refl _⟩
          · obtain ⟨yb, hyb, hle⟩ := hL y hy
            exact ⟨yb, hyb, UInt64.le_of_lt (UInt64.lt_of_le_of_lt hle hpslot)⟩
        · intro f1 f2 m1 m2 e1 e2 u hm1 hm2 hf1 hf2
          obtain ⟨f1, rfl⟩ : ∃ f, f1 = f + 1 := ⟨f1 - 1, by simp at hf1; omega⟩
          obtain ⟨f2, rfl⟩ : ∃ f, f2 = f + 1 := ⟨f2 - 1, by simp at hf2; omega⟩
          simp only [fuelLoop, EthCLLib.Proofs.run_bind,
            ancStep_run_above_eq store S m1 bx (hm1 ▸ hx) hgt,
            ancStep_run_above_eq store S m2 bx (hm2 ▸ hx) hgt]
          cases hps : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
              store bx).run u with
          | error err => rfl
          | ok p =>
            simp only [Except.bind, except_bind_ok]
            exact hwalk f1 f2 _ _ e1 e2 p.2 rfl rfl (by simp at hf1; omega)
              (by simp at hf2; omega)
    · -- A block at or below the target: both walks stop at their node.
      refine ⟨[], List.nodup_nil, fun y hy => absurd hy List.not_mem_nil, ?_⟩
      intro f1 f2 m1 m2 e1 e2 u hm1 hm2 hf1 hf2
      obtain ⟨f1, rfl⟩ : ∃ f, f1 = f + 1 := ⟨f1 - 1, by omega⟩
      obtain ⟨f2, rfl⟩ : ∃ f, f2 = f + 1 := ⟨f2 - 1, by omega⟩
      simp only [fuelLoop, EthCLLib.Proofs.run_bind,
        ancStep_run_done store S m1 bx (hm1 ▸ hx) hgt u,
        ancStep_run_done store S m2 bx (hm2 ▸ hx) hgt u, except_bind_ok]
      show Except.ok (m1.root, u) = Except.ok (m2.root, u)
      rw [hm1, hm2]

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The parent status read of a block whose parent is stored succeeds and keeps the store. -/
theorem getParentPayloadStatus_run_ok_of_parent (store : Store map)
    (b pb : EthCLSpecs.Heze.BeaconBlock) (hpb : FcMap.lookup store.blocks b.parentRoot = some pb)
    (u : Store map) :
    ∃ v, (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run u
      = .ok (v, u) := by
  unfold EthCLSpecs.Heze.getParentPayloadStatus
  rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hpb, except_bind_ok]
  exact ⟨_, rfl⟩

omit [Config] [EthCLLib.Spec.CryptoBackend] [EthCLLib.Spec.ExecutionEngine
  EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction EthCLSpecs.Heze.ExecutionRequests]
  [EthCLLib.Spec.DataAvailability] in
/-- **A child and its parent have one checkpoint block for an epoch that starts before the
child.** The walk from the child's pending node steps to its parent's node first, and from
there it matches the walk from the parent's pending node (`anc_walk_root`). The chain below
the parent has distinct roots other than the child's, so the walk from the child still has
fuel left after its first step. -/
theorem getCheckpointBlock_child_eq (store : Store map) (hslots : SlotsIncrease store)
    {r c : EthCLSpecs.Heze.Root} {rb cb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) (hc : FcMap.lookup store.blocks c = some cb)
    (hp : cb.parentRoot = r) (e : EthCLSpecs.Heze.Epoch) (S : EthCLSpecs.Heze.Slot)
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    (hlt : S < cb.slot) :
    ∀ u, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store c e).run u
      = (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store r e).run u := by
  intro u
  have hrc : rb.slot < cb.slot := hslots c cb rb hc (hp ▸ hrb)
  -- Both reads are the root of a `getAncestor` walk.
  have hread : ∀ x, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      store x e).run u = rootOf ((fuelLoop ((FcMap.keys store.blocks).length + 1)
        (ForkChoiceNode.pending x) (ForkChoiceNode.pending x) (ancStep store S)).run u) := by
    intro x
    unfold EthCLSpecs.Heze.getCheckpointBlock
    rw [hS]
    -- `liftErr (.ok S)` binds `S` at once.
    show (do
      let a ← EthCLSpecs.Heze.getAncestor (StoreTransition := ForkChoiceStoreRun (Store map))
        store (.pending x) S
      pure a.root).run u = _
    rw [getAncestor_eq_fuelLoop, EthCLLib.Proofs.run_bind]
    cases (fuelLoop ((FcMap.keys store.blocks).length + 1) (ForkChoiceNode.pending x)
        (ForkChoiceNode.pending x) (ancStep store S)).run u <;> rfl
  rw [hread c, hread r]
  -- The chain below `r`, and the fuel it leaves.
  obtain ⟨L, hnd, hL, hwalk⟩ := anc_walk_root store hslots S (rb.slot.toNat + 1) r rb hrb
    (Nat.lt_succ_self _)
  have hcL : c ∉ L := by
    intro hcL
    obtain ⟨yb, hyb, hle⟩ := hL c hcL
    rw [hc] at hyb
    cases hyb
    exact absurd (UInt64.lt_of_le_of_lt hle hrc) (UInt64.lt_irrefl _)
  have hlen := length_le_keys store (c :: L) (List.nodup_cons.mpr ⟨hcL, hnd⟩) (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨cb, hc⟩
    · obtain ⟨yb, hyb, -⟩ := hL x hx
      exact ⟨yb, hyb⟩)
  simp only [List.length_cons] at hlen
  -- The first step from the child goes to the parent's node.
  obtain ⟨ps, hps⟩ := getParentPayloadStatus_run_ok_of_parent store cb rb (hp ▸ hrb) u
  simp only [fuelLoop, EthCLLib.Proofs.run_bind,
    ancStep_run_above_eq store S (.pending c) cb hc hlt, hps, Except.bind, except_bind_ok]
  exact hwalk (FcMap.keys store.blocks).length ((FcMap.keys store.blocks).length + 1)
    { root := cb.parentRoot, payloadStatus := ps } (.pending r) _ _ u hp rfl (by omega) (by omega)

omit [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- **The finalized epoch of a store is the anchor's, or before the epoch of the clock.** A
finalized checkpoint other than the anchor checkpoint is the finalized checkpoint of a stored
chain state, or of its pull-up (`CkptInv.fSource`). In an ordered state the finalized epoch is
at most the previous epoch (`StateCkptOrd`). A pull-up writes the old current justified
checkpoint into the previous one, so its finalized epoch is at most that too. The state is no
later than the clock: it is the anchor state or the state of a stored block. -/
theorem finalized_epoch_le {A : EthCLSpecs.Heze.BeaconState} {a : EthCLSpecs.Heze.BeaconBlock}
    {s : Store map} (hinv : CkptInv A a s) (hord : StateCkptOrd A) {t : Nat}
    (hA : A.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤ t / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hblocks : ∀ k b, FcMap.lookup s.blocks k = some b → b.slot.toNat ≤ t) :
    s.finalizedCheckpoint =
        { epoch := EthCLSpecs.Heze.currentEpochOf (pureState A), root := htr a } ∨
      s.finalizedCheckpoint.epoch.toNat ≤ t / EthCLSpecs.Heze.Const.slotsPerEpoch - 1 := by
  rcases hinv.fSource with hanc | ⟨b, steps, v, hrun, hpath, -, hend, hc⟩
  · exact .inl hanc
  · right
    have hv := hrun.stateCkptOrd (Nat.le_refl _) hord
    -- The chain state is no later than the epoch of the clock.
    have hdiv : v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤
        t / EthCLSpecs.Heze.Const.slotsPerEpoch := by
      rcases hend with rfl | ⟨p, sb, vb, rfl⟩
      · cases hrun
        exact hA
      · obtain ⟨m, -, h2⟩ := hrun.split
        cases h2 with
        | block _ _ hstep hrest =>
          cases hrest
          obtain ⟨e1, e2⟩ := hstep.slot
          obtain ⟨k, hk⟩ := hpath.mem_lookup (x := sb.message) (by
            rw [blocksOf_append_block]
            exact List.mem_append_right _ (List.mem_singleton_self _))
          have := hblocks k sb.message hk
          exact Nat.div_le_div_right (by omega)
    have hprev := previousEpochOf_toNat_sub v
    -- The bound for `v`: finalized ≤ previous justified ≤ current justified ≤ previous epoch.
    have hord_v : v.finalizedCheckpoint.epoch.toNat ≤
        v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch - 1 := by
      obtain ⟨h1, h2, h3⟩ := hv
      rw [UInt64.le_iff_toNat_le] at h1 h2 h3
      omega
    rcases hc with hc | ⟨w, hw, hc⟩
    · rw [hc]
      change v.finalizedCheckpoint.epoch.toNat ≤ _
      omega
    · rw [hc]
      change w.finalizedCheckpoint.epoch.toNat ≤ _
      by_cases hg : EthCLSpecs.Heze.currentEpochOf (pureState v) ≤
          EthCLSpecs.Heze.Const.genesisEpoch + 1
      · rw [processJustificationAndFinalization_run_eq, ite_eq_left hg] at hw
        injection hw with hw
        injection hw with _ hw
        subst hw
        omega
      · -- The pull-up writes the old current justified checkpoint into the previous one.
        obtain ⟨o1, -, -, -⟩ := processJustificationAndFinalization_run_ord v w hv hw
        obtain ⟨_, _, _, _, _, -, -, -, -, -, hwj⟩ :=
          processJustificationAndFinalization_run_ok hw hg
        obtain ⟨-, -, hpj, -⟩ := weighJustificationAndFinalization_run_ok _ _ _ _ _ hwj
        rw [UInt64.le_iff_toNat_le, hpj] at o1
        obtain ⟨-, -, h3⟩ := hv
        rw [UInt64.le_iff_toNat_le] at h3
        omega

omit [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability] in
/-- **`hok`: a child of `r` and `r` pass the leaf check together, at the slot after `r`.** The
voting sources agree (`getVotingSource_child_eq`). For the finalized test: when the finalized
epoch starts before the child, the checkpoint blocks agree (`getCheckpointBlock_child_eq`).
Otherwise the finalized checkpoint is the anchor checkpoint (`finalized_epoch_le`: any other one
starts at least an epoch before the clock), both walks stop at once, and the anchor root is
neither block. -/
theorem leafOk_child_eq
    (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (store : Store map) {A : EthCLSpecs.Heze.BeaconState} {a : EthCLSpecs.Heze.BeaconBlock}
    (hinv : CkptInv A a store) (hord : StateCkptOrd A) (hlink : StateLink (htr a) store)
    (hunr : UnrealInv (htr a) store) (hkeys : UnrealKeys store)
    {r c : EthCLSpecs.Heze.Root} {rb cb : EthCLSpecs.Heze.BeaconBlock} {cs : EthCLSpecs.Heze.Slot}
    (hcs : ∀ u, (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run u = .ok (cs, u))
    (hcsr : cs.toNat = rb.slot.toNat + 1)
    (hA : A.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤
      cs.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hblocks : ∀ k b, FcMap.lookup store.blocks k = some b → b.slot.toNat ≤ cs.toNat)
    (hrb : FcMap.lookup store.blocks r = some rb) (hr0 : r ≠ htr a)
    (hc : FcMap.lookup store.blocks c = some cb) (hp : cb.parentRoot = r) (hc0 : c ≠ htr a) :
    ∀ u, (leafOk store (.pending c)).run u = (leafOk store (.pending r)).run u := by
  have hslots := hinv.slot.slots
  have hrc : rb.slot < cb.slot := hslots c cb rb hc (hp ▸ hrb)
  have hcslot : cb.slot.toNat = rb.slot.toNat + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hrc
    have := hblocks c cb hc
    omega
  rw [leafOk_eq_of_fin store (.pending c) (.pending r)
    (getVotingSource_child_eq hsph store hcs hcsr hrb hr0 hc hp hc0 hcslot hlink hunr hkeys)
    (fun u => finRead_eq_of store c r u ?_)]
  · intro u; rfl
  -- The finalized test.
  cases hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch store.finalizedCheckpoint.epoch :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) with
  | error err =>
    left
    unfold EthCLSpecs.Heze.getCheckpointBlock
    rw [hS]
    rfl
  | ok S =>
    by_cases hlt : S < cb.slot
    · exact .inl (getCheckpointBlock_child_eq store hslots hrb hc hp _ S hS hlt u)
    · right
      have hcle : ¬ cb.slot > S := hlt
      have hrle : ¬ rb.slot > S := fun h => hlt (UInt64.lt_trans h hrc)
      refine ⟨c, r, getCheckpointBlock_run_stop store c cb hc _ S hS hcle u,
        getCheckpointBlock_run_stop store r rb hrb _ S hS hrle u, ?_⟩
      rcases finalized_epoch_le hinv hord hA hblocks with hF | hF
      · -- The anchor checkpoint: its root is neither block.
        rw [hF]
        have h1 : (htr a == c) = false := beq_false_of_ne (Ne.symm hc0)
        have h2 : (htr a == r) = false := beq_false_of_ne (Ne.symm hr0)
        simp only [h1, h2]
      · -- Any other finalized epoch starts before the child: a contradiction.
        exfalso
        have hfit : store.finalizedCheckpoint.epoch.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch
            < 2 ^ 64 := Nat.lt_of_not_le fun hge => computeStartSlotAtEpoch_not_ok_of_ge hge hS
        have hSn : S.toNat = store.finalizedCheckpoint.epoch.toNat *
            EthCLSpecs.Heze.Const.slotsPerEpoch := by
          rw [computeStartSlotAtEpoch_ok_eq hS]
          exact epochStart_toNat _ hfit
        have hge : cb.slot.toNat ≤ S.toNat := Nat.le_of_not_lt fun h =>
          hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hspe := EthCLSpecs.Heze.Const.slotsPerEpochPos
        have h1 := Nat.div_mul_le_self cs.toNat EthCLSpecs.Heze.Const.slotsPerEpoch
        have h2 := Nat.mul_le_mul_right EthCLSpecs.Heze.Const.slotsPerEpoch hF
        rw [Nat.sub_one_mul] at h2
        by_cases h0 : cs.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch = 0
        · rw [h0] at h2
          simp at h2
          omega
        · have h3 : EthCLSpecs.Heze.Const.slotsPerEpoch ≤
              cs.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch * EthCLSpecs.Heze.Const.slotsPerEpoch :=
            Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
          omega

/-- **At the slot after `r`, no child block of `r` has a child block.** The store of a head run
holds no block later than the slot of the run (`HeadRun.Core.block_slot_le`). A child block of
`r` is later than `r`, and a child of it later still, so past the slot after `r`. -/
theorem HeadRun.Held.noGrandchild {n : NodeRun map} {q : HeadRun map} {r : EthCLSpecs.Heze.Root}
    {rb : EthCLSpecs.Heze.BeaconBlock} {t : Nat} (hn : n.Honest rb) (hq : q.Held n r rb t)
    (ht : t = rb.slot.toNat + 1) (hslots : SlotsIncrease q.store) :
    ∀ c cb, FcMap.lookup q.store.blocks c = some cb → cb.parentRoot = r →
      ∀ k b, FcMap.lookup q.store.blocks k = some b → b.parentRoot ≠ c := by
  intro c cb hc hp k b hk hpb
  have h1 := hslots c cb rb hc (hp ▸ hq.block)
  have h2 := hslots k b cb hk (hpb ▸ hc)
  have h3 := hq.block_slot_le hn (hn.anchor_le_of_lt (by omega)) hk
  have := UInt64.lt_iff_toNat_lt.mp h1
  have := UInt64.lt_iff_toNat_lt.mp h2
  omega

/-- **`EmptyViableWithFull` at the slot after `r`, with no premise on viability.** At the slot
after `r` the store holds no grandchild of `r` (`HeadRun.Held.noGrandchild`), and each child of
`r` passes the leaf check exactly when `r` does (`leafOk_child_eq`). So the FULL node of `r` is
in the viable node list only with its EMPTY node (`emptyViableWithFull_of_children`).

The premises are facts of the anchor and the preset: the anchor state is ordered
(`StateCkptOrd`), its epoch is at most the epoch of the run, two epochs fit in the block-root
ring, no block of the trace has a zero state root, and `r` is not the anchor. -/
theorem HeadRun.Held.emptyViable_raceLo
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Checkpoint]
    (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (hcol : ¬ RootCollision) {n : NodeRun map} {q : HeadRun map} {r : EthCLSpecs.Heze.Root}
    {rb : EthCLSpecs.Heze.BeaconBlock} (hn : n.Honest rb)
    (hq : q.Held n r rb (rb.slot.toNat + 1)) (hord : StateCkptOrd n.anchorState)
    (hsr : ∀ (sb : EthCLSpecs.Heze.SignedBeaconBlock) (w : Nat),
      (TraceEvent.handler (.block sb), w) ∈ n.events →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hA : n.anchorState.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤
      (rb.slot.toNat + 1) / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hr0 : r ≠ htr n.anchor) {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root = some jb) :
    EmptyViableWithFull q.store r := by
  have hslot := hq.slotInv hw hn hcol
  have hcb : ¬ HtrCollision EthCLSpecs.Heze.BeaconBlock := fun h => hcol (.inr h)
  have hev : ∀ e, TraceEvent.handler e ∈ q.events.map Prod.fst → e.NotAtAnchorParent n.anchor :=
    fun e he => by
      obtain ⟨w, hw'⟩ := hq.mem_events e he
      exact hn.noAnchorParent e w hw'
  -- The invariants of the store of the run.
  have hinv : CkptInv n.anchorState n.anchor q.store := by
    rcases NodeTrace.ckptInv hw hq.trace
        (CkptInv.anchor _ _ _ hn.anchorStore hn.anchorSelf) hord hev
        (fun sb he => by
          obtain ⟨w, hw'⟩ := hq.mem_events _ he
          exact hsr sb w hw') with hi | hc
    · exact hi
    · exact absurd hc hcol
  have hunr : UnrealInv (htr n.anchor) q.store :=
    hq.trace.unrealInv (UnrealInv.anchor _ _ _ hn.anchorStore)
  have hkeys : UnrealKeys q.store :=
    hq.trace.unrealKeys (BlockStatesPure.anchor _ _ _ hn.anchorStore)
      (UnrealKeys.anchor _ _ _ hn.anchorStore)
  have hlink : StateLink (htr n.anchor) q.store := by
    rcases NodeTrace.stateLink hw hq.trace
        (SlotInv.anchor _ _ _ hn.anchorStore hn.anchorSelf)
        (StateLink.anchor _ _ _ hn.anchorStore) hev with ⟨-, hl⟩ | hc
    · exact hl
    · exact absurd hc hcol
  -- The clock of the run.
  obtain ⟨cs, hcsn, hcs0⟩ := hq.slot
  have hcs : ∀ u, (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      q.store).run u = .ok (cs, u) := ((getCurrentSlot_stateFree q.store).run_eq hcs0).2
  have hblocks : ∀ k b, FcMap.lookup q.store.blocks k = some b → b.slot.toNat ≤ cs.toNat :=
    fun k b hk => hcsn ▸ hq.block_slot_le hn (hn.anchor_le_of_lt (by omega)) hk
  -- A child of `r` is not the anchor: the anchor's parent is not stored.
  have hchild0 : ∀ c cb, FcMap.lookup q.store.blocks c = some cb → cb.parentRoot = r →
      c ≠ htr n.anchor := by
    intro c cb hc hp hca
    have hat := hslot.atRoot c cb hc
    rw [hca] at hat
    have hcba : cb = n.anchor := Classical.byContradiction fun hne => hcb ⟨cb, n.anchor, hne, hat⟩
    subst hcba
    have := hslot.anchorParent
    rw [hp, hq.block] at this
    cases this
  refine emptyViableWithFull_of_children q.store r hslot.slots hj
    (hq.noGrandchild hn rfl hslot.slots) ?_
  intro c cb hc hp
  exact leafOk_child_eq hsph q.store hinv hord hlink hunr hkeys hcs (by omega) (by rw [hcsn]; exact hA)
    hblocks hq.block hr0 hc hp (hchild0 c cb hc hp)

/-- **Tier T2 with viability at the slot after `r` proved.** `race_empty_persists_composed`
takes `empty r` viable beside `full r` at the slot after `r` as a premise.
`HeadRun.Held.emptyViable_raceLo` proves it from facts of the anchor: an ordered anchor
state, no zero state root among the received blocks, an anchor epoch no later than the slot
after `r`, and `r` not the anchor root. The premise `hviable` for the later slots of the window
stays. `viableStep_of_carrier` (`ViableHonest.lean`) proves it under the vote carrier chain of
the finalization window. -/
theorem race_empty_persists_spec
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.ValidatorIndex]
    [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Checkpoint]
    [EthCLLib.Proofs.LawfulFcMap map (EthCLSpecs.Heze.Slot × EthCLSpecs.Heze.Root)]
    {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : EthCLSpecs.Heze.Root}
    {rb : EthCLSpecs.Heze.BeaconBlock} {hi : Nat} {jst : EthCLSpecs.Heze.BeaconState}
    {nodeOf : EthCLSpecs.Heze.ValidatorIndex → Node}
    {honestOf : EthCLSpecs.Heze.ValidatorIndex → Bool}
    {committees : Nat → Nat → Array EthCLSpecs.Heze.ValidatorIndex}
    {g : UInt64} {dr : EthCLSpecs.Heze.Root} {il : EthCLSpecs.Heze.InclusionList}
    {tSend Δ : Nat} {due : UInt64}
    {txs : EthCLSpecs.Heze.ExecutionPayload → Array EthCLSpecs.Heze.Transaction}
    {isValidOmission : EthCLSpecs.Heze.ExecutionPayload → EthCLSpecs.Heze.Transaction → Prop}
    {tx : EthCLSpecs.Heze.Transaction}
    (hset : RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    (hcomm : RaceCommittees jst honestOf committees (raceLo rb) hi)
    (hsph : 2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (hord : ∀ v, honest v → StateCkptOrd (node v).anchorState)
    (hsr : ∀ v, honest v → ∀ (sb : EthCLSpecs.Heze.SignedBeaconBlock) (w : Nat),
      (TraceEvent.handler (.block sb), w) ∈ (node v).events →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hA : ∀ v, honest v → (node v).anchorState.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch ≤
      (rb.slot.toNat + 1) / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hr0 : ∀ v, honest v → r ≠ htr (node v).anchor)
    (hviable : ∀ s, raceLo rb < s → s ≤ hi →
      (∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
        NodeBelow (run u t).store (.empty r) (run u t).head) →
      ∀ v, honest v → EmptyViableWithFull (run v s).store r) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hcol : RootCollision
  · exact .inl hcol
  by_cases hlohi : raceLo rb ≤ hi
  · refine race_empty_persists_composed hw hset hdec hcomm (fun v hv => ?_) hviable
    have hQ := hset.runOk v hv (raceLo rb) (Nat.le_refl _) hlohi
    obtain ⟨jb, hj, -⟩ := hQ.justified
    exact hQ.toHeld.emptyViable_raceLo hw hsph hcol (hset.nodeOk v hv) (hord v hv) (hsr v hv)
      (hA v hv) (hr0 v hv) hj
  · exact .inr fun _ _ t hlo hhi => absurd (Nat.le_trans hlo hhi) hlohi

end Race

end EthCLSpecs.Proofs.Heze
