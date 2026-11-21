import EthCLSpecs.Proofs.Heze.PayloadRaceWalk
import EthCLSpecs.Proofs.Heze.ViableNext

/-!
# `EthCLSpecs.Proofs.Heze.HeadReach`: the `getHead` loop ends within its fuel

`getHead` walks the node tree with `fuelLoop (headFuel store)`, from the pending node of the
justified root. When no fuel is left, the loop returns that start node
(`getHead_eq_fuelLoop_headLoopBody`). A theorem that puts the head below a later block must
exclude that case.

A `.next` step goes from a pending node to a payload node of the same block, or from a payload
node to the pending node of a child block. Under `SlotsIncrease` the child has a greater slot.
So the potential `walkPot` falls at each step. It is twice the count of the blocks after the
block of the node, plus one at a pending node. It starts below
`headFuel store = 2 * |blocks| + 2`, so the loop ends in a `.done` step
(`fuelLoop_run_inv_measure`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap Step fuelLoop)
open EthCLSpecs.Heze (Preset Config Store Root Slot ForkChoiceNode BeaconBlock)

/-- An invariant of `fuelLoop` with a measure. A `.next` step keeps `P` and lowers `μ`, and a
`.done` step from a value that satisfies `P` returns a result that satisfies `Q`. Then a run with
more fuel than the measure of the start returns a result that satisfies `Q`. The loop always
has fuel left, so the value for no fuel plays no part. -/
theorem fuelLoop_run_inv_measure {σ ε β α : Type} (P : β → Prop) (Q : α → Prop) (μ : β → Nat)
    (exhausted : α) (step : β → StateT σ (Except ε) (Step β α))
    (hnext : ∀ (b b' : β) (s s' : σ), P b → (step b).run s = .ok (.next b', s') →
      P b' ∧ μ b' < μ b)
    (hdone : ∀ (b : β) (a : α) (s s' : σ), P b → (step b).run s = .ok (.done a, s') → Q a) :
    ∀ (fuel : Nat) (init : β) (s s' : σ) (a : α), P init → μ init < fuel →
      (fuelLoop fuel init exhausted step).run s = .ok (a, s') → Q a := by
  intro fuel
  induction fuel with
  | zero => intro init s s' a _ h; omega
  | succ fuel ih =>
    intro init s s' a hinit hμ h
    simp only [fuelLoop] at h
    obtain ⟨st, s1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    cases st with
    | done d =>
      have ha := run_pure_eq_ok d a s1 s' hrest
      exact ha ▸ hdone init d s s1 hinit hstep
    | next b =>
      obtain ⟨hb, hlt⟩ := hnext init b s s1 hinit hstep
      exact ih b s1 s' a hb (by omega) hrest

/-- A weaker filter counts strictly more when one member passes it and fails the stronger
one. -/
theorem countP_lt_of_imp {γ : Type} (p q : γ → Bool) :
    ∀ (l : List γ) (x : γ), (∀ y ∈ l, p y = true → q y = true) → x ∈ l → q x = true →
      p x = false → l.countP p < l.countP q
  | [], _, _, hx, _, _ => absurd hx (List.not_mem_nil)
  | y :: l, x, himp, hx, hq, hp => by
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun z hz h => himp z (List.mem_cons_of_mem _ hz) h
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [hp, hq, Bool.false_eq_true, ↓reduceIte]
      omega
    · have := countP_lt_of_imp p q l x (fun z hz h => himp z (List.mem_cons_of_mem _ hz) h)
        hx' hq hp
      cases hpy : p y
      · cases q y <;> simp <;> omega
      · have := himp y (List.mem_cons_self ..) hpy
        simp [this]
        omega

/-- **The winner of a fold.** `c` wins every comparison with a member of `xs`, in either
argument order. A fold over a sublist of `xs`, from an accumulator in `xs`, returns `c` when `c`
is the accumulator or a member of the list. -/
theorem foldlM_run_winner {σ ε α : Type} (f : α → α → StateT σ (Except ε) α) (xs : List α)
    (c : α)
    (hl : ∀ z ∈ xs, ∀ (x : α) (s s' : σ), (f c z).run s = .ok (x, s') → x = c)
    (hr : ∀ z ∈ xs, ∀ (x : α) (s s' : σ), (f z c).run s = .ok (x, s') → x = c)
    (hmem : ∀ (a b x : α) (s s' : σ), (f a b).run s = .ok (x, s') → x = a ∨ x = b) :
    ∀ (l : List α) (init x : α) (s s' : σ), init ∈ xs → (∀ y ∈ l, y ∈ xs) →
      (init = c ∨ c ∈ l) → (l.foldlM f init).run s = .ok (x, s') → x = c := by
  intro l
  induction l with
  | nil =>
    intro init x s s' _ _ hc h
    rcases hc with hc | hc
    · exact (run_pure_eq_ok init x s s' h).trans hc
    · cases hc
  | cons a rest ih =>
    intro init x s s' hinit hl' hc h
    rw [List.foldlM_cons] at h
    obtain ⟨y, s1, hy, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    have hya : y ∈ xs := by
      rcases hmem init a y s s1 hy with rfl | rfl
      · exact hinit
      · exact hl' _ List.mem_cons_self
    have hrest' : ∀ z ∈ rest, z ∈ xs := fun z hz => hl' z (List.mem_cons_of_mem _ hz)
    rcases hc with rfl | hc
    · exact ih y x s1 s' hya hrest' (Or.inl (hl a (hl' a List.mem_cons_self) y s s1 hy))
        hrest
    · rcases List.mem_cons.mp hc with rfl | hc'
      · exact ih y x s1 s' hya hrest' (Or.inl (hr init hinit y s s1 hy)) hrest
      · exact ih y x s1 s' hya hrest' (Or.inr hc') hrest

section Pot
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The number of blocks of `store` with a slot after `slot`. -/
def blocksAfter (store : Store map) (slot : Slot) : Nat :=
  (FcMap.keys store.blocks).countP fun k =>
    match FcMap.lookup store.blocks k with
    | some b => decide (slot < b.slot)
    | none => false

/-- The potential of a node of the walk: twice the blocks after its block, plus one at a
pending node. A node whose root has no block has potential `0`. -/
def walkPot (store : Store map) (n : ForkChoiceNode) : Nat :=
  match FcMap.lookup store.blocks n.root with
  | some b => 2 * blocksAfter store b.slot +
      (if n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending then 1 else 0)
  | none => 0

/-- The potential of a node with a block is below `headFuel`. -/
theorem walkPot_lt_headFuel (store : Store map) (n : ForkChoiceNode) :
    walkPot store n < headFuel store := by
  unfold walkPot headFuel
  split
  · rename_i nb _
    have : blocksAfter store nb.slot ≤ (FcMap.keys store.blocks).length := by
      unfold blocksAfter
      exact List.countP_le_length
    split <;> omega
  · omega

/-- A child block lowers the count of later blocks. The child is itself a later block of the
parent, and every block after the child is after the parent. -/
theorem blocksAfter_lt [LawfulFcMap map Root] (store : Store map) (c : Root) (pb cb : BeaconBlock)
    (hc : FcMap.lookup store.blocks c = some cb) (hlt : pb.slot < cb.slot) :
    blocksAfter store cb.slot < blocksAfter store pb.slot := by
  unfold blocksAfter
  refine countP_lt_of_imp _ _ _ c ?_ ((LawfulFcMap.mem_keys store.blocks c).mpr (by rw [hc]; rfl))
    (by simp [hc, hlt]) (by simp [hc])
  intro k _ h
  split at h
  · simp only [decide_eq_true_eq] at h ⊢
    exact UInt64.lt_trans hlt h
  · cases h

/-- An edge of the node tree lowers the potential and keeps a block at the root. A payload
node keeps the block of its pending node and drops the pending `1`. The pending node of a child
block has a greater slot than its parent (`SlotsIncrease`), so the count of later blocks
falls. -/
theorem NodeEdge.walkPot_lt [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {n c : ForkChoiceNode} (h : NodeEdge store n c)
    (hn : (FcMap.lookup store.blocks n.root).isSome) :
    (FcMap.lookup store.blocks c.root).isSome ∧ walkPot store c < walkPot store n := by
  obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.mp hn
  rcases NodeEdge.cases_on_child store n c h with
    ⟨hp, hc⟩ | ⟨root, cb, s, s', rfl, hcb, hparent, hstatus⟩
  · have hroot : n.root = c.root := by rw [hp]; rfl
    have hcs : c.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
      rcases hc with hc | hc <;> rw [hc]
      · exact payloadStatus_empty_ne_pending
      · exact payloadStatus_full_ne_pending
    have hnp : n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending := by rw [hp]; rfl
    refine ⟨by rw [← hroot, hnb]; rfl, ?_⟩
    unfold walkPot
    rw [← hroot, hnb]
    simp only [hcs, hnp, ite_false, ite_true]
    omega
  · have hns := getParentPayloadStatus_run_ne_pending store s s' cb _ hstatus
    have hlt := hslots root cb nb hcb (hparent ▸ hnb)
    have hafter := blocksAfter_lt store root nb cb hcb hlt
    have hr : (ForkChoiceNode.pending root).root = root := rfl
    have hps : (ForkChoiceNode.pending root).payloadStatus =
        EthCLSpecs.Heze.Const.payloadStatusPending := rfl
    refine ⟨by rw [hr, hcb]; rfl, ?_⟩
    unfold walkPot
    rw [hr, hcb, hnb, hps]
    simp only [hns, ite_false, ite_true]
    omega

variable [Config]

/-- **One step of the head loop to a winner.** Every run of `getNodeChildren` at `n` lists `c`
among the viable children, and `c` wins every `betterOf` comparison with a viable child, in
either order. Then every successful loop step at `n` moves to `c`. -/
theorem headLoopBody_run_of_winner (store : Store map) (nodes : Array ForkChoiceNode)
    (n c : ForkChoiceNode)
    (hc : ∀ (t t' : Store map) (cs : Array ForkChoiceNode),
      (EthCLSpecs.Heze.getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
        store n).run t = .ok (cs, t') →
      c ∈ cs.filter nodes.contains ∧
      ∀ z ∈ cs.filter nodes.contains,
        (∀ (x : ForkChoiceNode) (s s' : Store map),
          (EthCLSpecs.Heze.getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map))
            store c z).run s = .ok (x, s') → x = c) ∧
        ∀ (x : ForkChoiceNode) (s s' : Store map),
          (EthCLSpecs.Heze.getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map))
            store z c).run s = .ok (x, s') → x = c) :
    ∀ (t t' : Store map) (st : Step ForkChoiceNode ForkChoiceNode),
      (headLoopBody store nodes n).run t = .ok (st, t') → st = .next c := by
  intro t t' st h
  unfold headLoopBody headFold at h
  obtain ⟨cs, s1, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hmem, hwin⟩ := hc t s1 cs hcs
  dsimp only at h
  split at h
  · rename_i hemp
    exact absurd (Array.isEmpty_iff.mp hemp ▸ hmem) (by simp)
  · rename_i hne
    obtain ⟨best, s2, hfold, h⟩ := run_bind_eq_ok _ _ _ _ h
    have hst := run_pure_eq_ok _ _ _ _ h
    subst hst
    rw [← Array.foldlM_toList] at hfold
    have hpos : 0 < (cs.filter nodes.contains).size := by
      rcases Nat.eq_zero_or_pos (cs.filter nodes.contains).size with h0 | h0
      · exact absurd (Array.isEmpty_iff_size_eq_zero.mpr h0) (by simpa using hne)
      · exact h0
    have hinit : (cs.filter nodes.contains)[0]! ∈ (cs.filter nodes.contains).toList := by
      rw [getElem!_pos (cs.filter nodes.contains) 0 hpos]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hpos)
    have hb := foldlM_run_winner _ (cs.filter nodes.contains).toList c
      (fun z hz => (hwin z (Array.mem_toList_iff.mp hz)).1)
      (fun z hz => (hwin z (Array.mem_toList_iff.mp hz)).2)
      (betterOf_run_mem store) (cs.filter nodes.contains).toList _ best s1 s2 hinit
      (fun _ hy => hy) (Or.inr (Array.mem_toList_iff.mpr hmem)) hfold
    rw [hb]

/-- **The head loop ends within its fuel.** Take an invariant of the node that each `.next` step
keeps. The loop starts at a node with a block at its root. Then the head that the loop returns
satisfies the invariant. The potential falls at each step and starts below `headFuel`. So the
loop ends in a `.done` step, which returns the current node. -/
theorem headLoop_run_inv [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (nodes : Array ForkChoiceNode) (Inv : ForkChoiceNode → Prop)
    (hnext : ∀ (n c : ForkChoiceNode) (t t' : Store map), Inv n →
      (FcMap.lookup store.blocks n.root).isSome →
      (headLoopBody store nodes n).run t = .ok (.next c, t') → Inv c)
    (start exhausted head : ForkChoiceNode) (s s' : Store map) (hstart : Inv start)
    (hsb : (FcMap.lookup store.blocks start.root).isSome)
    (hrun : (fuelLoop (headFuel store) start exhausted (headLoopBody store nodes)).run s
      = .ok (head, s')) :
    Inv head := by
  refine fuelLoop_run_inv_measure
    (fun n => Inv n ∧ (FcMap.lookup store.blocks n.root).isSome) Inv (walkPot store) exhausted
    _ ?_ ?_ (headFuel store) start s s' head ⟨hstart, hsb⟩ (walkPot_lt_headFuel store start) hrun
  · intro n c t t' ⟨hn, hb⟩ hst
    have hedge := (headLoopBody_run_next_edge store t t' nodes n c hst).1
    obtain ⟨hcb, hlt⟩ := NodeEdge.walkPot_lt store hslots hedge hb
    exact ⟨⟨hnext n c t t' hn hb hst, hcb⟩, hlt⟩
  · intro n d t t' ⟨hn, _⟩ hst
    rw [headLoopBody_run_done store t t' nodes n d hst]
    exact hn

omit [Config] in
/-- The walk potential does not rise along a path, and the root keeps a block. -/
theorem NodeBelow.walkPot_le [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {p q : ForkChoiceNode} (h : NodeBelow store p q)
    (hp : (FcMap.lookup store.blocks p.root).isSome) :
    (FcMap.lookup store.blocks q.root).isSome ∧ walkPot store q ≤ walkPot store p := by
  induction h with
  | refl => exact ⟨hp, Nat.le_refl _⟩
  | step x y _ hxy ih =>
    obtain ⟨hx, hle⟩ := ih
    obtain ⟨hy, hlt⟩ := NodeEdge.walkPot_lt store hslots hxy hx
    exact ⟨hy, by omega⟩

/-- The loop result lies below the start: each `.next` step goes to a child. The fuel covers
the potential, so the loop ends in a `.done` step. -/
theorem headLoop_run_below_start [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (nodes : Array ForkChoiceNode) (exhausted : ForkChoiceNode) :
    ∀ (fuel : Nat) (start head : ForkChoiceNode) (s s' : Store map),
      (FcMap.lookup store.blocks start.root).isSome → walkPot store start < fuel →
      (fuelLoop fuel start exhausted (headLoopBody store nodes)).run s = .ok (head, s') →
      NodeBelow store start head := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro start head s s' hb hμ h
    simp only [fuelLoop] at h
    obtain ⟨st, s1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    cases st with
    | done d =>
      have ha := run_pure_eq_ok d head s1 s' hrest
      have hd := headLoopBody_run_done store s s1 nodes start d hstep
      rw [ha, hd]
      exact .refl
    | next c =>
      have hedge := (headLoopBody_run_next_edge store s s1 nodes start c hstep).1
      obtain ⟨hcb, hlt⟩ := NodeEdge.walkPot_lt store hslots hedge hb
      exact NodeBelow.of_edge hedge (ih c head s1 s' hcb (by omega) hrest)

/-- **The walk passes a node above its result.** The loop from `start` returns a node below
`T`, and `start` lies above `T`. Then the loop reaches `T` with fuel above its potential, and
the rest of the loop from `T` returns the same node. Each step goes to a child `c` above the
result. `c` and `T` both lie above the result, so they are on one chain
(`NodeBelow.comparable`). `T` strictly below `c` would put `T` below the parent of `c`, a
cycle. -/
theorem headLoop_run_through [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (nodes : Array ForkChoiceNode) (exhausted T : ForkChoiceNode) :
    ∀ (fuel : Nat) (start head : ForkChoiceNode) (s s' : Store map),
      (FcMap.lookup store.blocks start.root).isSome → walkPot store start < fuel →
      NodeBelow store start T → NodeBelow store T head →
      (fuelLoop fuel start exhausted (headLoopBody store nodes)).run s = .ok (head, s') →
      ∃ (f : Nat) (s1 : Store map), walkPot store T < f ∧
        (fuelLoop f T exhausted (headLoopBody store nodes)).run s1 = .ok (head, s') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro start head s s' hb hμ hST hTh h
    by_cases hst : start = T
    · subst hst
      exact ⟨fuel + 1, s, hμ, h⟩
    · have h' := h
      simp only [fuelLoop] at h
      obtain ⟨st, s1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
      cases st with
      | done d =>
        -- A `.done` step returns `start`, which then lies below `T`: a cycle with `T` below
        -- `start`.
        have ha := run_pure_eq_ok d head s1 s' hrest
        rw [headLoopBody_run_done store s s1 nodes start d hstep] at ha
        subst ha
        exfalso
        cases hST with
        | refl => exact hst rfl
        | step p _ hsp hpT =>
          obtain ⟨hpb, hle⟩ := NodeBelow.walkPot_le store hslots hsp hb
          obtain ⟨hTb, hlt⟩ := NodeEdge.walkPot_lt store hslots hpT hpb
          have hle' := (NodeBelow.walkPot_le store hslots hTh hTb).2
          omega
      | next c =>
        have hedge := (headLoopBody_run_next_edge store s s1 nodes start c hstep).1
        obtain ⟨hcb, hlt⟩ := NodeEdge.walkPot_lt store hslots hedge hb
        have hch := headLoop_run_below_start store hslots nodes exhausted fuel c head s1 s' hcb
          (by omega) hrest
        -- `c` lies above `T`: the two are on one chain, and `T` strictly below `c` closes a
        -- cycle through `start`.
        have hcT : NodeBelow store c T := by
          rcases NodeBelow.comparable store c T head hch hTh with h1 | h1
          · exact h1
          · cases h1 with
            | refl => exact .refl
            | step p _ hTp hpc =>
              -- `p` is the one parent `start` of `c`, so `start` lies below `T` and above it.
              have hp : p = start := NodeEdge.parent_unique store p start c hpc hedge
              rw [hp] at hTp
              exfalso
              cases hST with
              | refl => exact hst rfl
              | step q _ hsq hqT =>
                obtain ⟨hqb, hle3⟩ := NodeBelow.walkPot_le store hslots hsq hb
                obtain ⟨hTb, hlt3⟩ := NodeEdge.walkPot_lt store hslots hqT hqb
                have hle2 := (NodeBelow.walkPot_le store hslots hTp hTb).2
                omega
        exact ih c head s1 s' hcb (by omega) hcT hTh hrest

/-- **The path to a kept node is viable.** Take a node `x` that its own walk keeps
(`KeptAt`), below the justified pending node, with verified payloads at the FULL nodes of the
path. Every node `y` on the path from the justified pending node to `x` is in the viable node
list. The walk keeps `x` itself, and a strict ancestor keeps itself (`go_keeps_anc`). The walk
from the justified pending node keeps what `y` keeps (`go_keeps_desc`). -/
theorem mem_nodes_of_kept [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {jb : BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (x : ForkChoiceNode) (hx : KeptAt store x)
    (hver : ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) x → EthCLSpecs.Heze.isPayloadVerified store z = true)
    (y : ForkChoiceNode) (hJy : NodeBelow store (.pending store.justifiedCheckpoint.root) y)
    (hyx : NodeBelow store y x)
    (nodes : Array ForkChoiceNode) (t t' : Store map)
    (hrun : (EthCLSpecs.Heze.getFilteredNodeTree
      (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t = .ok (nodes, t')) :
    nodes.contains y = true := by
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go
      (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  have hbud : Budget store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root) [store.justifiedCheckpoint.root] := by
    simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_singleton]
    omega
  have hky : KeptAt store y := by
    by_cases hyx' : y = x
    · exact hyx' ▸ hx
    · intro K P xb u ys hxb hP hPs hxP hbud' hys
      exact go_keeps_anc store hslots x hx K y P xb u ys hxb hP hPs hxP hbud' hys hyx hyx'
        (fun z hz hzx => hver z (NodeBelow.trans store _ _ _ hJy hz) hzx)
  rw [Array.contains_iff_mem]
  exact go_keeps_desc store hslots y hky _ _ [store.justifiedCheckpoint.root] jb t nodes hj
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun z hz => by rw [List.mem_singleton.mp hz]; exact ⟨jb, hj, UInt64.le_refl _⟩)
    (List.mem_singleton_self _) hbud hrun' hJy
    (fun z hz hzy => hver z hz (NodeBelow.trans store _ _ _ hzy hyx))

/-- **The head reaches a target.** The viable node list is never empty, and the justified
pending node is above the node `T`. At each node below the justified pending node and strictly
above `T`, every successful loop step moves to a node above `T` or to `T` itself. Then the head
is below `T`. In the proof, every step from a node below `T` stays below `T`. -/
theorem getHead_run_below_of_path [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (T : ForkChoiceNode)
    (hJT : NodeBelow store (.pending store.justifiedCheckpoint.root) T)
    (hJ : (FcMap.lookup store.blocks store.justifiedCheckpoint.root).isSome)
    (hnonempty : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run t = .ok (nodes, t') → nodes.isEmpty = false)
    (hstep : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run t = .ok (nodes, t') →
      ∀ n, NodeBelow store (.pending store.justifiedCheckpoint.root) n → NodeBelow store n T →
      n ≠ T → ∃ c, NodeBelow store c T ∧ ∀ (u u' : Store map)
        (st : Step ForkChoiceNode ForkChoiceNode),
        (headLoopBody store nodes n).run u = .ok (st, u') → st = .next c)
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (EthCLSpecs.Heze.getHead (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run runnerStore = .ok (head, s')) :
    NodeBelow store T head := by
  rw [getHead_eq_fuelLoop_headLoopBody] at hrun
  obtain ⟨nodes, s1, hnodes, hloop⟩ := run_bind_eq_ok _ _ _ _ hrun
  dsimp only at hloop
  rw [hnonempty nodes runnerStore s1 hnodes] at hloop
  simp only [Bool.false_eq_true, ite_false] at hloop
  have hpath := hstep nodes runnerStore s1 hnodes
  -- `P`: the node is below `T`, or strictly above `T` and below the justified pending node.
  -- Its root has a block.
  let P : ForkChoiceNode → Prop := fun n =>
    (NodeBelow store T n ∨ (NodeBelow store (.pending store.justifiedCheckpoint.root) n ∧
      NodeBelow store n T ∧ n ≠ T)) ∧ (FcMap.lookup store.blocks n.root).isSome
  have hP0 : P (.pending store.justifiedCheckpoint.root) := by
    refine ⟨?_, hJ⟩
    by_cases he : ForkChoiceNode.pending store.justifiedCheckpoint.root = T
    · exact Or.inl (he ▸ NodeBelow.refl)
    · exact Or.inr ⟨NodeBelow.refl, hJT, he⟩
  refine fuelLoop_run_inv_measure P (NodeBelow store T) (walkPot store) _ _ ?_ ?_
    (headFuel store) _ s1 s' head hP0 (walkPot_lt_headFuel store _) hloop
  · intro n c t t' ⟨hn, hb⟩ hst
    have hedge := (headLoopBody_run_next_edge store t t' nodes n c hst).1
    obtain ⟨hcb, hlt⟩ := NodeEdge.walkPot_lt store hslots hedge hb
    refine ⟨⟨?_, hcb⟩, hlt⟩
    rcases hn with hn | ⟨hJn, hn, hne⟩
    · exact Or.inl (NodeBelow.step n c hn hedge)
    · obtain ⟨c', hc', hall⟩ := hpath n hJn hn hne
      have hcc : c = c' := by
        have := hall t t' _ hst
        injection this
      subst hcc
      by_cases he : c = T
      · exact Or.inl (he ▸ NodeBelow.refl)
      · exact Or.inr ⟨NodeBelow.step n c hJn hedge, hc', he⟩
  · intro n d t t' ⟨hn, _⟩ hst
    rcases hn with hn | ⟨hJn, hn, hne⟩
    · rw [headLoopBody_run_done store t t' nodes n d hst]
      exact hn
    · obtain ⟨c', -, hall⟩ := hpath n hJn hn hne
      cases hall t t' _ hst

/-- **The head is strictly below the target.** Under the premises of
`getHead_run_below_of_path`, every successful loop step at `T` moves to a child. Then the head is
strictly below `T`. The walk passes `T` (`headLoop_run_through`), steps to a child `c` of `T`,
and ends below `c` (`headLoop_run_below_start`). `T` below `c` would close a cycle. -/
theorem getHead_run_strictly_below [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (T : ForkChoiceNode)
    (hJT : NodeBelow store (.pending store.justifiedCheckpoint.root) T)
    (hJ : (FcMap.lookup store.blocks store.justifiedCheckpoint.root).isSome)
    (hnonempty : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run t = .ok (nodes, t') → nodes.isEmpty = false)
    (hstep : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run t = .ok (nodes, t') →
      ∀ n, NodeBelow store (.pending store.justifiedCheckpoint.root) n → NodeBelow store n T →
      n ≠ T → ∃ c, NodeBelow store c T ∧ ∀ (u u' : Store map)
        (st : Step ForkChoiceNode ForkChoiceNode),
        (headLoopBody store nodes n).run u = .ok (st, u') → st = .next c)
    (hT : ∀ (nodes : Array ForkChoiceNode) (t t' : Store map),
      (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run t = .ok (nodes, t') →
      ∀ (u u' : Store map) (st : Step ForkChoiceNode ForkChoiceNode),
        (headLoopBody store nodes T).run u = .ok (st, u') → ∃ c, st = .next c)
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (EthCLSpecs.Heze.getHead (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run runnerStore = .ok (head, s')) :
    NodeBelow store T head ∧ head ≠ T := by
  have hbelow := getHead_run_below_of_path store hslots T hJT hJ hnonempty hstep runnerStore s'
    head hrun
  refine ⟨hbelow, fun he => ?_⟩
  rw [getHead_eq_fuelLoop_headLoopBody] at hrun
  obtain ⟨nodes, s1, hnodes, hloop⟩ := run_bind_eq_ok _ _ _ _ hrun
  dsimp only at hloop
  rw [hnonempty nodes runnerStore s1 hnodes] at hloop
  simp only [Bool.false_eq_true, ite_false] at hloop
  obtain ⟨f, s2, hf, hloopT⟩ := headLoop_run_through store hslots nodes _ T (headFuel store) _
    head s1 s' hJ (walkPot_lt_headFuel store _) hJT hbelow hloop
  have hTb := (NodeBelow.walkPot_le store hslots hJT hJ).1
  cases f with
  | zero => omega
  | succ f =>
    simp only [fuelLoop] at hloopT
    obtain ⟨st, s3, hst, hrest⟩ := run_bind_eq_ok _ _ _ _ hloopT
    obtain ⟨c, rfl⟩ := hT nodes runnerStore s1 hnodes s2 s3 st hst
    have hedge := (headLoopBody_run_next_edge store s2 s3 nodes T c hst).1
    obtain ⟨hcb, hlt⟩ := NodeEdge.walkPot_lt store hslots hedge hTb
    have hch := headLoop_run_below_start store hslots nodes _ f c head s3 s' hcb (by omega) hrest
    rw [he] at hch
    obtain ⟨-, hlt'⟩ := NodeEdge.walkPot_lt store hslots hedge hTb
    have hle := (NodeBelow.walkPot_le store hslots hch hcb).2
    omega

end Pot

end EthCLSpecs.Proofs.Heze
