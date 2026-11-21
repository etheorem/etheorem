import EthCLSpecs.Proofs.Heze.ForkSides

/-!
# `EthCLSpecs.Proofs.Heze.SettingWalk`: the honest head lies strictly below `pending r`

`get_head` (`gloas/fork-choice.md`) walks from the pending node of the justified root. Take an
honest head run of the window whose justified node lies above `pending r`. The walk of the
viable node tree keeps a node strictly below `pending r` (`KeptAt`). Then every node of the path
from the justified node is viable (`mem_nodes_of_kept`). At each fork of the path, the
path child is ahead of every other child on weight (`FinalitySetting.forkAhead`), so the loop
steps to it (`headLoopBody_run_of_winner`). At `pending r` the loop steps to a child. So the
head lies strictly below `pending r` (`getHead_run_strictly_below`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState LawfulFcMap run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex ExecutionPayload Transaction ExecutionRequests getNodeChildren getHead)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- A path that does not end at its top starts with an edge from the top. -/
theorem NodeBelow.first_edge (store : Store map) {n m : ForkChoiceNode}
    (h : NodeBelow store n m) (hne : n ≠ m) :
    ∃ c, NodeEdge store n c ∧ NodeBelow store c m := by
  induction h with
  | refl => exact absurd rfl hne
  | step p q hnp hpq ih =>
    by_cases hnp' : n = p
    · subst hnp'
      exact ⟨q, hpq, .refl⟩
    · obtain ⟨c, hnc, hcp⟩ := ih hnp'
      exact ⟨c, hnc, .step p q hcp hpq⟩

/-- The pending node of the root of a node with a valid status lies above it. -/
theorem ValidStatus.pending_above (store : Store map) {n : ForkChoiceNode} (hv : ValidStatus n) :
    NodeBelow store (.pending n.root) n := by
  rcases hv with hs | hs | hs
  · rw [show (ForkChoiceNode.pending n.root) = n from node_eq_of_root_status _ _ rfl hs.symm]
    exact .refl
  · rw [show n = .empty n.root from node_eq_of_root_status _ _ rfl hs]
    exact .step _ _ .refl (NodeEdge.empty _)
  · rw [show n = .full n.root from node_eq_of_root_status _ _ rfl hs]
    exact .step _ _ .refl (NodeEdge.full _)

/-- A node strictly above `pending r` other than one of root `r` has a block before the block of
`r`. -/
theorem NodeBelow.above_slot_lt (store : Store map) (hslots : SlotsIncrease store)
    {n : ForkChoiceNode} (hv : ValidStatus n) {r : Root} {rb nb : BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) (hnb : FcMap.lookup store.blocks n.root = some nb)
    (h : NodeBelow store n (.pending r)) (hne : n.root ≠ r) : nb.slot < rb.slot := by
  obtain ⟨yb, hyb, hlt⟩ := below_slot_gt store hslots hnb
    (NodeBelow.trans store _ _ _ (hv.pending_above store) h)
    (fun he => hne he.symm)
  rw [show (ForkChoiceNode.pending r).root = r from rfl, hrb] at hyb
  cases hyb
  exact hlt

/-- A node below a node with a block has a block. -/
theorem NodeBelow.block_of (store : Store map) [LawfulFcMap map Root]
    (hslots : SlotsIncrease store) {p q : ForkChoiceNode} {pb : BeaconBlock}
    (hpb : FcMap.lookup store.blocks p.root = some pb) (h : NodeBelow store p q) :
    ∃ qb, FcMap.lookup store.blocks q.root = some qb :=
  Option.isSome_iff_exists.mp (NodeBelow.walkPot_le store hslots h (by rw [hpb]; rfl)).1

/-- A node below the pending node of a root has a valid status. -/
theorem NodeBelow.validStatus_of_pending (store : Store map) {k : Root} {n : ForkChoiceNode}
    (h : NodeBelow store (.pending k) n) : ValidStatus n := by
  cases h with
  | refl => exact .inl rfl
  | step p _ _ hpn => exact NodeEdge.validStatus store p n hpn

variable [Config]

/-- A node strictly below `pending r` that the walk of the viable node tree keeps. The FULL nodes
of the path from the justified node have verified payloads. -/
def KeptBelow (store : Store map) (r : Root) (x : ForkChoiceNode) : Prop :=
  KeptAt store x ∧ NodeBelow store (.pending r) x ∧ x ≠ .pending r ∧
    ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) x → EthCLSpecs.Heze.isPayloadVerified store z = true

end

section Step
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

include hw in
/-- **The head of an honest run lies strictly below `pending r`.** Take a head run of slot `s`
of the window, after the honest votes before `s` are on the EMPTY side. Its justified node lies
above `pending r`, with the counts `ForkCount` at the forks of the path. The walk of the viable
node tree keeps a node strictly below `pending r` (`KeptBelow`). Then the head lies strictly
below `pending r`. -/
theorem FinalitySetting.settingAt
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    {jst : BeaconState}
    (hjst : FcMap.lookup (run v s).store.checkpointStates (run v s).store.justifiedCheckpoint
      = some (pureState jst))
    (hforks : ∀ x y xb,
      NodeBelow (run v s).store (.pending (run v s).store.justifiedCheckpoint.root) x →
      NodeEdge (run v s).store x y → NodeBelow (run v s).store y (.pending r) →
      FcMap.lookup (run v s).store.blocks x.root = some xb →
      ForkCount jst honestOf committees (supSlot (run v s).store y) (xb.slot.toNat + 1) s)
    (hJr : NodeBelow (run v s).store (.pending (run v s).store.justifiedCheckpoint.root)
      (.pending r))
    {jb : BeaconBlock}
    (hjb : FcMap.lookup (run v s).store.blocks (run v s).store.justifiedCheckpoint.root = some jb)
    {x : ForkChoiceNode} (hx : KeptBelow (run v s).store r x) :
    NodeBelow (run v s).store (.pending r) (run v s).head ∧ (run v s).head ≠ .pending r := by
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  have hinvB := hQ.slotInv hw hN hcol
  have hslots := hinvB.slots
  obtain ⟨hkx, hrx, hxne, hver⟩ := hx
  obtain ⟨s', hrun⟩ := hQ.headRun
  have hJx := NodeBelow.trans _ _ _ _ hJr hrx
  -- Every node of the path from the justified node to `x` is viable.
  have hmem : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        (run v s).store).run t = .ok (nodes, t') →
      ∀ y, NodeBelow (run v s).store (.pending (run v s).store.justifiedCheckpoint.root) y →
        NodeBelow (run v s).store y x → nodes.contains y = true :=
    fun nodes t t' hr y hJy hyx => mem_nodes_of_kept _ hslots hjb x hkx hver y hJy hyx nodes t t' hr
  -- A child on the path is listed: a FULL child on the path has its payload verified.
  have hlisted : ∀ n c, NodeEdge (run v s).store n c →
      NodeBelow (run v s).store (.pending (run v s).store.justifiedCheckpoint.root) c →
      NodeBelow (run v s).store c x → ∀ (u u' : Store map) (cs : Array ForkChoiceNode),
      (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
        (run v s).store n).run u = .ok (cs, u') → c ∈ cs :=
    fun n c hnc hJc hcx u u' cs hcs => getNodeChildren_run_mem _ n c hnc
      (fun y _ hcy => hver y (hcy ▸ hJc) (hcy ▸ hcx)) u u' cs hcs
  refine getHead_run_strictly_below _ hslots (.pending r) hJr (by rw [hjb]; rfl) ?_ ?_ ?_ _ s' _
    hrun
  · -- The viable node list holds `x`, so it is not empty.
    intro nodes t t' hr
    have hc := hmem nodes t t' hr x hJx .refl
    cases he : nodes.isEmpty
    · rfl
    · rw [Array.isEmpty_iff.mp he] at hc
      simp at hc
  · -- At a fork of the path, the loop steps to the path child.
    intro nodes t t' hr n hJn hnr hne
    obtain ⟨c, hnc, hcr⟩ := NodeBelow.first_edge _ hnr hne
    refine ⟨c, hcr, ?_⟩
    have hcx : NodeBelow (run v s).store c x := NodeBelow.trans _ _ _ _ hcr hrx
    have hJc := NodeBelow.step _ _ hJn hnc
    obtain ⟨nb, hnb⟩ := NodeBelow.block_of _ hslots hjb hJn
    obtain ⟨cb, hcb⟩ := NodeBelow.block_of _ hslots hjb hJc
    have hvn := NodeBelow.validStatus_of_pending _ hJn
    -- The fork is not at the root `r`: its block is before `rb`.
    have hnr' : n.root ≠ r := by
      intro hroot
      have hrB : (FcMap.lookup (run v s).store.blocks (ForkChoiceNode.pending r).root).isSome := by
        rw [show (ForkChoiceNode.pending r).root = r from rfl, hQ.block]; rfl
      rcases hvn with hst | hst | hst
      · exact hne (node_eq_of_root_status _ _ hroot hst)
      · have he : n = .empty r := node_eq_of_root_status _ _ hroot hst
        rw [he] at hnr
        exact NodeEdge.not_below_parent _ hslots (NodeEdge.empty r) hrB hnr
      · have he : n = .full r := node_eq_of_root_status _ _ hroot hst
        rw [he] at hnr
        exact NodeEdge.not_below_parent _ hslots (NodeEdge.full r) hrB hnr
    have hns := NodeBelow.above_slot_lt _ hslots hvn hQ.block hnb hnr hnr'
    have hoff : nb.slot.toNat + 1 < s := by
      have := UInt64.lt_iff_toNat_lt.mp hns
      unfold raceLo at hlo
      omega
    have hcA : a.slot.toNat ≤ supSlot (run v s).store c := by
      have h1 := hinvB.anchor_le_slot _ _ hcb
      rw [hset.anchorBlock v hv] at h1
      have h2 := UInt64.le_iff_toNat_le.mp h1
      unfold supSlot
      rw [hcb]
      dsimp only
      omega
    have hcount := hforks n c nb hJn hnc hcr hnb
    refine headLoopBody_run_of_winner _ nodes n c fun u u' cs hcs => ⟨?_, fun z hz => ?_⟩
    · exact Array.mem_filter.mpr ⟨hlisted n c hnc hJc hcx u u' cs hcs,
        hmem nodes t t' hr c hJc hcx⟩
    · have hnz := getNodeChildren_run_edge _ u u' n cs hcs z (Array.mem_filter.mp hz).1
      by_cases hzc : z = c
      · subst hzc
        exact ⟨fun y s1 s1' h => by rcases betterOf_run_mem _ _ _ y s1 s1' h with h | h <;> exact h,
          fun y s1 s1' h => by rcases betterOf_run_mem _ _ _ y s1 s1' h with h | h <;> exact h⟩
      · have hahead := hset.forkAhead hw hcol hv hlo hs hV hjst hnc hnz (Ne.symm hzc) (.inl hcr)
          hcb hnb hoff hcA hcount
        exact ⟨fun y s1 s1' h => betterOf_run_of_ahead _ c z y s1 s1'
            (fun t1 t1' t2 t2' wA wB hA hB => hahead t1 t1' t2 t2' wA wB hA hB) h,
          fun y s1 s1' h => betterOf_run_of_behind _ z c y s1 s1'
            (fun t1 t1' t2 t2' wA wB hA hB => hahead t2 t2' t1 t1' wB wA hB hA) h⟩
  · -- At `pending r`, the loop steps to a child: the child toward `x` is viable.
    intro nodes t t' hr u u' st hst
    obtain ⟨c, hrc, hcx⟩ := NodeBelow.first_edge _ hrx (Ne.symm hxne)
    have hJc := NodeBelow.step _ _ hJr hrc
    unfold headLoopBody at hst
    obtain ⟨cs, u1, hcs, hst⟩ := run_bind_eq_ok _ _ _ _ hst
    have hcmem : c ∈ cs.filter nodes.contains :=
      Array.mem_filter.mpr ⟨hlisted _ c hrc hJc hcx u u1 cs hcs, hmem nodes t t' hr c hJc hcx⟩
    dsimp only at hst
    split at hst
    · rename_i hemp
      rw [Array.isEmpty_iff.mp hemp] at hcmem
      simp at hcmem
    · obtain ⟨best, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
      exact ⟨best, run_pure_eq_ok _ _ _ _ hst⟩

end Step

end EthCLSpecs.Proofs.Heze
