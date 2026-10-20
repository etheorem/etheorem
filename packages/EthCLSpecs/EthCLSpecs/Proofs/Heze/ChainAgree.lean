import EthCLSpecs.Proofs.Heze.ForkPoint
import EthCLSpecs.Proofs.Heze.BlockChain
import EthCLSpecs.Proofs.Heze.FinalityLock

/-!
# `EthCLSpecs.Proofs.Heze.ChainAgree`: two chains of one block tree agree below a shared root

`Agree` (`EthCLLib.Proofs.FFG.Model`) asks that two chains with one checkpoint in common hold
the same checkpoints at every earlier epoch. The chains here are the chains of two runs from
one anchor state, whose blocks lie on ancestor paths of honest stores. A block fixes its
parent root. The roots of two distinct blocks differ, unless the hash collides. So one root at
an epoch fixes the blocks up to it. Then the two runs have one root at every earlier slot.

## Linked blocks

`Linked a bs` states three facts. The parent root of each block of `bs` is the root of the
block before it. The parent root of the first block is the root of the anchor block `a`. No
block is `a`. An ancestor path of a store with the slot invariant meets `Linked`
(`AncestorPath.linked`). Without a block collision, two lists that meet `Linked` and have one
last root are one list (`Linked.eq_of_last`).

## Slots along a run

The blocks of a run come in slot order (`ChainRun.blocks_sorted`). Each block has a slot
greater than the header slot of the start state (`ChainRun.blocks_gt_header`). So the blocks
at or before a slot are a prefix of the blocks of the run.

## The anchor root

At a slot before every block of a run, `rootAtSlot` reads the anchor state. From the header
slot of the anchor state on, that is the root of its filled header. Suppose that the other run
has a block with that root there. Then the filled header is the header of that block
(`htr_eq_htr_headerOf`), or two headers collide. In the first case the header slot equals a
block slot, and `ChainRun.blocks_gt_header` excludes that.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState BeaconBlock BeaconBlockHeader)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## Linked blocks -/

section Linked
variable [Preset] [HasherTag]

/-- The root after a list of blocks: the root of its last block, or the root of `a`. -/
def lastRootOf (a : BeaconBlock) (bs : List BeaconBlock) : EthCLSpecs.Heze.Root :=
  bs.getLast?.elim (htr a) htr

/-- `Linked a bs`: the parent root of each block is the root after the blocks before it, and no
block is `a`. -/
inductive Linked (a : BeaconBlock) : List BeaconBlock → Prop
  | nil : Linked a []
  | snoc {bs : List BeaconBlock} {b : BeaconBlock} : Linked a bs →
      b.parentRoot = lastRootOf a bs → b ≠ a → Linked a (bs ++ [b])

/-- The root after a list with one more block is the root of that block. -/
theorem lastRootOf_snoc (a : BeaconBlock) (bs : List BeaconBlock) (b : BeaconBlock) :
    lastRootOf a (bs ++ [b]) = htr b := by
  unfold lastRootOf
  rw [List.getLast?_concat]
  rfl

/-- Each prefix of a list that meets `Linked` meets `Linked`. -/
theorem Linked.prefix {a : BeaconBlock} {L : List BeaconBlock} (h : Linked a L) :
    ∀ l m : List BeaconBlock, L = l ++ m → Linked a l := by
  induction h with
  | nil =>
    intro l m he
    rw [(List.nil_eq_append_iff.mp he).1]
    exact .nil
  | @snoc bs b hbs hp hne ih =>
    intro l m he
    rcases List.eq_nil_or_concat m with rfl | ⟨m', x, rfl⟩
    · rw [List.append_nil] at he
      rw [← he]
      exact .snoc hbs hp hne
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      obtain ⟨h1, -⟩ := List.append_inj' he rfl
      exact ih l m' h1

/-- Without a block collision, two linked lists with one last root are one list. -/
theorem Linked.eq_of_last (hc : ¬ HtrCollision BeaconBlock) {a : BeaconBlock}
    {l₁ : List BeaconBlock} (h₁ : Linked a l₁) :
    ∀ {l₂ : List BeaconBlock}, Linked a l₂ → lastRootOf a l₁ = lastRootOf a l₂ → l₁ = l₂ := by
  -- Two blocks with one root are one block.
  have inj : ∀ x y : BeaconBlock, htr x = htr y → x = y := fun x y hxy =>
    Classical.byContradiction fun hne => hc ⟨x, y, hne, hxy⟩
  induction h₁ with
  | nil =>
    intro l₂ h₂ he
    cases h₂ with
    | nil => rfl
    | snoc _ _ hne =>
      rw [lastRootOf_snoc] at he
      exact absurd (inj _ _ he).symm hne
  | @snoc bs₁ b₁ hbs₁ hp₁ hne₁ ih =>
    intro l₂ h₂ he
    cases h₂ with
    | nil =>
      rw [lastRootOf_snoc] at he
      exact absurd (inj _ _ he) hne₁
    | @snoc bs₂ b₂ hbs₂ hp₂ _ =>
      rw [lastRootOf_snoc, lastRootOf_snoc] at he
      have hb := inj _ _ he
      subst hb
      rw [ih hbs₂ (hp₁.symm.trans hp₂)]

variable {map : MapKind} [FcMap map]

/-- An ancestor path of a store with the slot invariant meets `Linked`. Its root is the root
after its blocks. -/
theorem AncestorPath.linked {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) {k : EthCLSpecs.Heze.Root} {bs : List BeaconBlock}
    (h : AncestorPath a s k bs) : Linked a bs ∧ k = lastRootOf a bs := by
  induction h with
  | anchor => exact ⟨.nil, rfl⟩
  | cons hk hne _ ih =>
    refine ⟨.snoc ih.1 ih.2 hne, ?_⟩
    rw [lastRootOf_snoc]
    exact (hinv.atRoot _ _ hk).symm

end Linked

/-! ## Slots along a run -/

section Slots
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The blocks of a run below the bound come in slot order. -/
theorem ChainRun.blocks_sorted {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    (blocksOf q).Pairwise (fun x y => x.slot.toNat ≤ y.slot.toNat) := by
  induction h with
  | nil => exact .nil
  | slot _ _ _ ih => exact ih
  | block sb v hstep hrest ih =>
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih⟩
    obtain ⟨hs, hbs⟩ := hstep.slot
    have := hrest.blocks_slot_ge hhi b hb
    omega

/-- The header slot does not decrease along a run. Each block of the run has a slot greater
than the header slot of the start state. -/
theorem ChainRun.blocks_gt_header {hi : Nat} {q : List ChainStep} {u w : BeaconState}
    (h : ChainRun hi q u w) :
    u.latestBlockHeader.slot.toNat ≤ w.latestBlockHeader.slot.toNat ∧
      ∀ b ∈ blocksOf q, u.latestBlockHeader.slot.toNat < b.slot.toNat := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, fun b hb => absurd hb List.not_mem_nil⟩
  | @slot _ st st1 _ _ hstep _ ih =>
    have hh : st1.latestBlockHeader.slot = st.latestBlockHeader.slot := by
      rw [hstep.hdr.1]
      unfold filledHeader
      split <;> rfl
    rw [hh] at ih
    exact ih
  | @block _ st st1 _ sb v hstep _ ih =>
    obtain ⟨-, hlt, hhd, -, -⟩ := hstep.hdr
    have hh : st1.latestBlockHeader.slot = sb.message.slot := by rw [hhd]; rfl
    rw [hh] at ih
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    refine ⟨by omega, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hlt'
    · have := ih.2 b hb
      omega

omit [HasherTag] [Config] [CryptoBackend] in
/-- In a list in slot order, the blocks at or before slot `S` come first. -/
theorem filter_prefix_of_sorted (S : Nat) :
    ∀ l : List BeaconBlock, l.Pairwise (fun x y => x.slot.toNat ≤ y.slot.toNat) →
      ∃ G, l = l.filter (fun b => b.slot.toNat ≤ S) ++ G
  | [], _ => ⟨[], rfl⟩
  | x :: t, h => by
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    by_cases hxS : x.slot.toNat ≤ S
    · obtain ⟨G, hG⟩ := filter_prefix_of_sorted S t ht
      refine ⟨G, ?_⟩
      rw [List.filter_cons_of_pos (by simpa using hxS), List.cons_append, ← hG]
    · -- Every later block has a slot past `S`, so the filter is empty.
      have hnil : (x :: t).filter (fun b => b.slot.toNat ≤ S) = [] := by
        refine List.filter_eq_nil_iff.mpr fun b hb => ?_
        rcases List.mem_cons.mp hb with rfl | hb
        · simpa using hxS
        · have := hx b hb
          simp only [decide_eq_true_eq]
          omega
      exact ⟨x :: t, by rw [hnil]; rfl⟩

omit [HasherTag] [Config] [CryptoBackend] in
/-- For `s ≤ S`, the blocks at or before `s` are the blocks at or before `s` among the blocks
at or before `S`. -/
theorem filter_le_filter (l : List BeaconBlock) {s S : Nat} (hs : s ≤ S) :
    l.filter (fun b => b.slot.toNat ≤ s) =
      (l.filter (fun b => b.slot.toNat ≤ S)).filter (fun b => b.slot.toNat ≤ s) := by
  rw [List.filter_filter]
  congr 1
  funext b
  by_cases h : b.slot.toNat ≤ s
  · simp [h, Nat.le_trans h hs]
  · simp [h]

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **One root fixes the earlier roots.** Two runs start at the anchor state `A`, and the blocks
of each run meet `Linked a`. The two runs have one root at slot `S`. Then they have one root at
every slot up to `S`, or two blocks or two headers share a root. -/
theorem rootAtSlot_agree (hc : ¬ RootCollision) {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {a : BeaconBlock} {A X Y : BeaconState} {steps₁ steps₂ : List ChainStep}
    (h₁ : ChainRun hi steps₁ A X) (h₂ : ChainRun hi steps₂ A Y)
    (hl₁ : Linked a (blocksOf steps₁)) (hl₂ : Linked a (blocksOf steps₂)) {S : Nat}
    (hS : rootAtSlot A steps₁ S = rootAtSlot A steps₂ S) :
    ∀ s ≤ S, rootAtSlot A steps₁ s = rootAtSlot A steps₂ s := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hc (.inr h)
  have hch : ¬ HtrCollision BeaconBlockHeader := fun h => hc (.inl h)
  -- The blocks at or before `S` are a prefix of the blocks of each run, and meet `Linked`.
  obtain ⟨G₁, hG₁⟩ := filter_prefix_of_sorted S _ (h₁.blocks_sorted hhi)
  obtain ⟨G₂, hG₂⟩ := filter_prefix_of_sorted S _ (h₂.blocks_sorted hhi)
  have hF₁ := hl₁.prefix _ _ hG₁
  have hF₂ := hl₂.prefix _ _ hG₂
  -- A block of a run at or before `S` puts the anchor header slot below `S`. Its root is not
  -- the root of the filled anchor header.
  have hanchor : ∀ {steps : List ChainStep} {Z : BeaconState}, ChainRun hi steps A Z →
      ∀ b ∈ (blocksOf steps).filter (fun b => b.slot.toNat ≤ S), anchorRoot A S ≠ htr b := by
    intro steps Z hz b hb he
    obtain ⟨hbm, hbS⟩ := List.mem_filter.mp hb
    simp only [decide_eq_true_eq] at hbS
    have hgt := (hz.blocks_gt_header).2 b hbm
    unfold anchorRoot at he
    rw [if_pos (by omega), htr_eq_htr_headerOf hw b] at he
    have hhd : filledHeader A = headerOf b :=
      Classical.byContradiction fun hne => hch ⟨_, _, hne, he⟩
    have hsl : (filledHeader A).slot = A.latestBlockHeader.slot := by
      unfold filledHeader
      split <;> rfl
    rw [hhd] at hsl
    change b.slot = _ at hsl
    rw [hsl] at hgt
    exact Nat.lt_irrefl _ hgt
  intro s hs
  unfold rootAtSlot at hS ⊢
  rw [filter_le_filter _ hs, filter_le_filter (blocksOf steps₂) hs]
  cases e₁ : ((blocksOf steps₁).filter (fun b => b.slot.toNat ≤ S)).getLast? with
  | none =>
    have hn₁ := List.getLast?_eq_none_iff.mp e₁
    cases e₂ : ((blocksOf steps₂).filter (fun b => b.slot.toNat ≤ S)).getLast? with
    | none =>
      rw [hn₁, List.getLast?_eq_none_iff.mp e₂]
    | some b₂ =>
      rw [e₁, e₂] at hS
      simp only [Option.elim] at hS
      exact absurd hS (hanchor h₂ b₂ (List.mem_of_getLast? e₂))
  | some b₁ =>
    cases e₂ : ((blocksOf steps₂).filter (fun b => b.slot.toNat ≤ S)).getLast? with
    | none =>
      rw [e₁, e₂] at hS
      simp only [Option.elim] at hS
      exact absurd hS.symm (hanchor h₁ b₁ (List.mem_of_getLast? e₁))
    | some b₂ =>
      rw [e₁, e₂] at hS
      simp only [Option.elim] at hS
      have hlast : lastRootOf a ((blocksOf steps₁).filter (fun b => b.slot.toNat ≤ S)) =
          lastRootOf a ((blocksOf steps₂).filter (fun b => b.slot.toNat ≤ S)) := by
        unfold lastRootOf
        rw [e₁, e₂]
        simp only [Option.elim]
        exact hS
      rw [hF₁.eq_of_last hcb hF₂ hlast]

include hw in
/-- **The two chains agree.** Two runs start at the anchor state, and the blocks of each run
meet `Linked a`. Then their chains meet `Agree`, or two blocks or two headers share a root. -/
theorem ffgChain_agree (hc : ¬ RootCollision) {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {a : BeaconBlock} {A X Y : BeaconState} {steps₁ steps₂ : List ChainStep}
    (h₁ : ChainRun hi steps₁ A X) (h₂ : ChainRun hi steps₂ A Y)
    (hl₁ : Linked a (blocksOf steps₁)) (hl₂ : Linked a (blocksOf steps₂))
    (vals₁ vals₂ : List EthCLSpecs.Heze.ValidatorIndex) :
    EthCLLib.Proofs.FFG.Agree (ffgChain hi steps₁ A vals₁) (ffgChain hi steps₂ A vals₂) := by
  intro e₁ r h₁r h₂r e he
  change some (chainRoot A steps₁ e₁) = some r at h₁r
  change some (chainRoot A steps₂ e₁) = some r at h₂r
  change some (chainRoot A steps₁ e) = some (chainRoot A steps₂ e)
  have heq : chainRoot A steps₁ e₁ = chainRoot A steps₂ e₁ :=
    Option.some.inj (h₁r.trans h₂r.symm)
  by_cases h0 : e₁ = 0
  · subst h0
    rw [Nat.le_zero.mp he, heq]
  -- The runs have one root at the first slot of `e₁`, so one root at every slot before it.
  have hS : rootAtSlot A steps₁ (e₁ * slotsPerEpoch) = rootAtSlot A steps₂ (e₁ * slotsPerEpoch) := by
    unfold chainRoot at heq
    rwa [if_neg h0, if_neg h0] at heq
  have hall := rootAtSlot_agree hw hc hhi h₁ h₂ hl₁ hl₂ hS
  congr 1
  unfold chainRoot
  by_cases he0 : e = 0
  · subst he0
    simp only [if_true]
    split
    · rfl
    · exact hall 0 (Nat.zero_le _)
  · rw [if_neg he0, if_neg he0]
    exact hall _ (Nat.mul_le_mul_right _ he)

end Slots

/-! ## The checkpoint walk along an ancestor path -/

section Walk
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap)

variable [Preset] [HasherTag] {map : MapKind} [FcMap map] [LawfulFcMap map EthCLSpecs.Heze.Root]

omit [Preset] [HasherTag] [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A `nodup` list inside another list is no longer. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (l m : List α), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | x :: t, m, hn, hs => by
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hn
    have hxm := hs x List.mem_cons_self
    have := nodup_length_le t (m.erase x) ht fun y hy =>
      (List.mem_erase_of_ne (fun h => hx (by rw [← h]; exact hy))).mpr
        (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem hxm] at this
    have hpos : 0 < m.length := List.length_pos_of_mem hxm
    simp only [List.length_cons]
    omega

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The store holds a block at the root of an ancestor path: the anchor block, or the last
block of the path. -/
theorem AncestorPath.lookup_root {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (ha : FcMap.lookup s.blocks (htr a) = some a) {k : EthCLSpecs.Heze.Root}
    {bs : List BeaconBlock} (h : AncestorPath a s k bs) : ∃ b, FcMap.lookup s.blocks k = some b := by
  cases h with
  | anchor => exact ⟨a, ha⟩
  | cons hk _ _ => exact ⟨_, hk⟩

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- When an ancestor path has a block, the store holds a block at the root of the path. -/
theorem AncestorPath.lookup_of_mem {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    {k : EthCLSpecs.Heze.Root} {bs : List BeaconBlock} (h : AncestorPath a s k bs)
    {x : BeaconBlock} (hx : x ∈ bs) : ∃ b, FcMap.lookup s.blocks k = some b := by
  induction h with
  | anchor => exact absurd hx List.not_mem_nil
  | cons hk _ _ _ => exact ⟨_, hk⟩

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The store holds each block of an ancestor path at its root. The blocks come in strict slot
order, and the block at the root of the path has the greatest slot. -/
theorem AncestorPath.sorted {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) {k : EthCLSpecs.Heze.Root} {bs : List BeaconBlock}
    (h : AncestorPath a s k bs) :
    (∀ x ∈ bs, FcMap.lookup s.blocks (htr x) = some x) ∧
      bs.Pairwise (fun x y => x.slot < y.slot) ∧
      ∀ x ∈ bs, ∀ y, FcMap.lookup s.blocks k = some y → x.slot ≤ y.slot := by
  induction h with
  | anchor => exact ⟨fun _ hx => absurd hx List.not_mem_nil, .nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | @cons k b bs hk _ hpath ih =>
    obtain ⟨hin, hpw, hmax⟩ := ih
    have hkb : htr b = k := hinv.atRoot _ _ hk
    -- Every block of the path below `b` has a smaller slot.
    have hlt : ∀ x ∈ bs, x.slot < b.slot := by
      intro x hx
      obtain ⟨pb, hp⟩ := hpath.lookup_of_mem hx
      exact UInt64.lt_of_le_of_lt (hmax x hx _ hp) (hinv.slots _ _ _ hk hp)
    refine ⟨fun x hx => ?_, List.pairwise_append.mpr ⟨hpw, .cons (fun _ h => absurd h
      List.not_mem_nil) .nil, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact hin x hx
      · rw [List.mem_singleton.mp hx, hkb]
        exact hk
    · rw [List.mem_singleton.mp hy]
      exact hlt x hx
    · rw [hk] at hy
      cases hy
      rcases List.mem_append.mp hx with hx | hx
      · exact UInt64.le_of_lt (hlt x hx)
      · rw [List.mem_singleton.mp hx]
        exact UInt64.le_refl _

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- An ancestor path is no longer than the key list of the store: its blocks are at distinct
keys. -/
theorem AncestorPath.length_le_keys {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    [LawfulFcMap map EthCLSpecs.Heze.Root] (hinv : SlotInv a s) {k : EthCLSpecs.Heze.Root}
    {bs : List BeaconBlock} (h : AncestorPath a s k bs) :
    bs.length ≤ (FcMap.keys s.blocks).length := by
  obtain ⟨hin, hpw, -⟩ := h.sorted hinv
  rw [← List.length_map (f := fun x => htr x)]
  refine nodup_length_le _ _ ?_ fun r hr => ?_
  · rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy he => ?_) hpw
    -- Two blocks at one key are one block.
    have h1 : FcMap.lookup s.blocks (htr y) = some x := he ▸ hin x hx
    have hxy' : x = y := Option.some.inj (h1.symm.trans (hin y hy))
    subst hxy'
    exact UInt64.lt_irrefl _ hxy
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact (LawfulFcMap.mem_keys _ _).mpr (by rw [hin x hx]; rfl)

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A walk step at a block at or before the target slot stops there. -/
theorem ancStep_run_le {store : EthCLSpecs.Heze.Store map} {T : EthCLSpecs.Heze.Slot}
    {n : EthCLSpecs.Heze.ForkChoiceNode} {b : BeaconBlock}
    (hb : FcMap.lookup store.blocks n.root = some b) (hle : ¬ T < b.slot)
    (t : EthCLSpecs.Heze.Store map) :
    (ancStep store T n).run t = .ok (.done n, t) := by
  simp only [ancStep, FcMap.getOrThrow, FcMap.getOrThrowKey, hb, gt_iff_lt, pure_bind]
  rw [if_neg hle]
  rfl

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A walk step at a block after the target slot moves to its parent, which the store holds. -/
theorem ancStep_run_gt {store : EthCLSpecs.Heze.Store map} {T : EthCLSpecs.Heze.Slot}
    {n : EthCLSpecs.Heze.ForkChoiceNode} {b pb : BeaconBlock}
    (hb : FcMap.lookup store.blocks n.root = some b)
    (hpb : FcMap.lookup store.blocks b.parentRoot = some pb) (hgt : T < b.slot)
    (t : EthCLSpecs.Heze.Store map) :
    ∃ ps, (ancStep store T n).run t =
      .ok (.next { root := b.parentRoot, payloadStatus := ps }, t) := by
  simp only [ancStep, FcMap.getOrThrow, FcMap.getOrThrowKey, hb, gt_iff_lt, pure_bind]
  rw [if_pos hgt]
  simp only [EthCLSpecs.Heze.getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey,
    hpb, pure_bind]
  exact ⟨_, rfl⟩

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **The walk along a path.** The walk of `get_ancestor` starts at a node at the root of an
ancestor path and moves toward slot `T`. It returns the root after the path blocks at or before
`T`. The store holds the anchor block, and the anchor block is at or before `T`. The fuel
exceeds the number of path blocks after `T`. -/
theorem AncestorPath.walk {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) (ha : FcMap.lookup s.blocks (htr a) = some a)
    {T : EthCLSpecs.Heze.Slot} (haT : a.slot ≤ T) {k : EthCLSpecs.Heze.Root}
    {bs : List BeaconBlock} (h : AncestorPath a s k bs) :
    ∀ (fuel : Nat) (n ex : EthCLSpecs.Heze.ForkChoiceNode) (t : EthCLSpecs.Heze.Store map),
      n.root = k → (bs.filter (fun b => T < b.slot)).length < fuel →
      ∃ m, (EthCLLib.Spec.fuelLoop fuel n ex (ancStep s T)).run t = .ok (m, t) ∧
        m.root = lastRootOf a (bs.filter (fun b => b.slot ≤ T)) := by
  induction h with
  | anchor =>
    intro fuel n ex t hn hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [EthCLLib.Spec.fuelLoop]
    have hs := ancStep_run_le (n := n) (by rw [hn]; exact ha) (UInt64.not_lt.mpr haT) t
    simp only [EthCLLib.Proofs.run_bind, hs, EthCLLib.Proofs.except_bind_ok]
    exact ⟨n, rfl, hn⟩
  | @cons k b bs hk hne hpath ih =>
    intro fuel n ex t hn hf
    have hkb : htr b = k := hinv.atRoot _ _ hk
    by_cases hgt : T < b.slot
    · -- `b` comes after `T`: step to its parent, with one unit of fuel less.
      obtain ⟨pb, hpb⟩ := hpath.lookup_root ha
      obtain ⟨ps, hs⟩ := ancStep_run_gt (n := n) (by rw [hn]; exact hk) hpb hgt t
      rw [List.filter_append, List.length_append] at hf
      simp only [List.filter_cons, hgt, decide_true, if_true, List.filter_nil,
        List.length_singleton] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [EthCLLib.Proofs.fuelLoop_run_of_next f n ex _ _ t t hs]
      obtain ⟨m, hm, hmr⟩ := ih f { root := b.parentRoot, payloadStatus := ps } ex t rfl
        (by omega)
      refine ⟨m, hm, ?_⟩
      rw [hmr, List.filter_append]
      simp only [List.filter_cons, UInt64.not_le.mpr hgt, decide_false, Bool.false_eq_true,
        if_false, List.filter_nil, List.append_nil]
    · -- `b` is at or before `T`: the walk stops at `b`.
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      rw [EthCLLib.Spec.fuelLoop]
      have hs := ancStep_run_le (n := n) (by rw [hn]; exact hk) hgt t
      simp only [EthCLLib.Proofs.run_bind, hs, EthCLLib.Proofs.except_bind_ok]
      refine ⟨n, rfl, ?_⟩
      rw [hn, List.filter_append]
      simp only [List.filter_cons, UInt64.not_lt.mp hgt, decide_true, if_true, List.filter_nil]
      rw [lastRootOf_snoc, hkb]

/-- **The checkpoint block on a path.** `getCheckpointBlock` starts at the root of an ancestor
path. Its start slot `E * SLOTS_PER_EPOCH` fits in `uint64`, so the checked
`compute_start_slot_at_epoch` succeeds. The walk returns the root after the path blocks at or
before that slot. The store holds the anchor block, and the anchor block is at or before that
slot. -/
theorem AncestorPath.checkpointBlock {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) (ha : FcMap.lookup s.blocks (htr a) = some a)
    {E : EthCLSpecs.Heze.Epoch} (hfit : E.toNat * slotsPerEpoch < 2 ^ 64)
    (haE : a.slot ≤ E * UInt64.ofNat slotsPerEpoch) {k : EthCLSpecs.Heze.Root}
    {bs : List BeaconBlock} (h : AncestorPath a s k bs) (t : EthCLSpecs.Heze.Store map) :
    (EthCLSpecs.Heze.getCheckpointBlock (StoreTransition := ForkChoiceStoreRun
      (EthCLSpecs.Heze.Store map)) s k E).run t =
      .ok (lastRootOf a (bs.filter (fun b => b.slot ≤ E * UInt64.ofNat slotsPerEpoch)), t) := by
  have hlen := h.length_le_keys hinv
  obtain ⟨m, hm, hmr⟩ := h.walk hinv ha haE _ (.pending k) (.pending k) t rfl
    (Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) hlen))
  have hl : (liftErr (m := ForkChoiceStoreRun (EthCLSpecs.Heze.Store map))
      (EthCLSpecs.Heze.computeStartSlotAtEpoch E : Except StateTransitionError EthCLSpecs.Heze.Slot)).run t
      = .ok (E * UInt64.ofNat slotsPerEpoch, t) :=
    EthCLLib.Proofs.run_liftErr_of_ok _ t (by rw [computeStartSlotAtEpoch_ok_of_lt hfit]; rfl)
  unfold EthCLSpecs.Heze.getCheckpointBlock
  simp only [EthCLLib.Proofs.run_bind, hl, getAncestor_eq_fuelLoop, hm,
    EthCLLib.Proofs.except_bind_ok, hmr]
  rfl

omit [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A prefix of an ancestor path is the ancestor path of its last root. -/
theorem AncestorPath.prefix {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) {k : EthCLSpecs.Heze.Root} {L : List BeaconBlock}
    (h : AncestorPath a s k L) :
    ∀ l m : List BeaconBlock, L = l ++ m → AncestorPath a s (lastRootOf a l) l := by
  induction h with
  | anchor =>
    intro l m he
    rw [(List.nil_eq_append_iff.mp he).1]
    exact .anchor
  | @cons k b bs hk hne hpath ih =>
    intro l m he
    rcases List.eq_nil_or_concat m with rfl | ⟨m', x, rfl⟩
    · rw [List.append_nil] at he
      rw [← he, lastRootOf_snoc, hinv.atRoot _ _ hk]
      exact .cons hk hne hpath
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      exact ih l m' (List.append_inj' he rfl).1

end Walk

/-! ## A conflicting justified checkpoint is off the chain -/

section Conflict
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap)

variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]
  [LawfulFcMap map EthCLSpecs.Heze.Root]

omit [Config] [CryptoBackend] in
/-- Take the anchor block as the block of the anchor state. From the header slot of the anchor
state on, a run has the root after its blocks at or before each slot. -/
theorem rootAtSlot_eq_lastRootOf {A : BeaconState} {a : BeaconBlock}
    (hanc : htr (filledHeader A) = htr a) (steps : List ChainStep) {T : Nat}
    (hT : A.latestBlockHeader.slot.toNat ≤ T) :
    rootAtSlot A steps T = lastRootOf a ((blocksOf steps).filter (fun b => b.slot.toNat ≤ T)) := by
  unfold rootAtSlot lastRootOf
  cases (List.filter (fun b => decide (b.slot.toNat ≤ T)) (blocksOf steps)).getLast? with
  | none =>
    simp only [Option.elim]
    unfold anchorRoot
    rw [if_pos hT, hanc]
  | some b => simp only [Option.elim]

omit [HasherTag] [Config] [CryptoBackend] [LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A filter by a `uint64` slot bound is the filter by its number. -/
theorem filter_slot_le_toNat (l : List BeaconBlock) (S : EthCLSpecs.Heze.Slot) :
    l.filter (fun b => b.slot ≤ S) = l.filter (fun b => b.slot.toNat ≤ S.toNat) := by
  simp only [UInt64.le_iff_toNat_le]

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **A conflicting checkpoint is off the chain.** The blocks of a run from the anchor state
`A` form the ancestor path of `k` in `s`. The justified checkpoint `j` is on the chain of the
run. The checkpoint `f` is at or before `j`, after epoch 0, and after the anchor slot. When `j`
and `f` conflict in `s`, `f` is not on the chain. Otherwise the walk of `getCheckpointBlock`
from `j.root` returns `f.root`. The store `s` holds the anchor block, and the anchor block is
the block of `A`. -/
theorem conflicting_not_onChain (hc : ¬ RootCollision) {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {a : BeaconBlock} {A Y : BeaconState} {s : EthCLSpecs.Heze.Store map}
    (hinv : SlotInv a s) (ha : FcMap.lookup s.blocks (htr a) = some a)
    (hanc : htr (filledHeader A) = htr a) (hroots : AnchorRoots A)
    {steps : List ChainStep} (hrun : ChainRun hi steps A Y) {k : EthCLSpecs.Heze.Root}
    (hp : AncestorPath a s k (blocksOf steps)) {j f : EthCLSpecs.Heze.Checkpoint}
    (hj : chainRoot A steps j.epoch.toNat = j.root) (hfj : f.epoch.toNat ≤ j.epoch.toNat)
    (hf1 : 1 ≤ f.epoch.toNat) (hjE : j.epoch.toNat * slotsPerEpoch < 2 ^ 64)
    (hAf : A.slot.toNat ≤ f.epoch.toNat * slotsPerEpoch)
    (hconf : Conflicting s j f) : chainRoot A steps f.epoch.toNat ≠ f.root := by
  intro hf
  -- The anchor block has the slot of the anchor header.
  have haslot : a.slot = A.latestBlockHeader.slot := by
    rw [htr_eq_htr_headerOf hw a] at hanc
    have hhd : filledHeader A = headerOf a :=
      Classical.byContradiction fun hne => hc (.inl ⟨_, _, hne, hanc⟩)
    have hsl : (filledHeader A).slot = A.latestBlockHeader.slot := by
      unfold filledHeader
      split <;> rfl
    rw [hhd] at hsl
    exact hsl
  have hhdr := hroots.hdrLe
  have hfE : f.epoch.toNat * slotsPerEpoch ≤ j.epoch.toNat * slotsPerEpoch :=
    Nat.mul_le_mul_right _ hfj
  have hstart := epochStart_toNat f.epoch (by omega)
  -- The blocks at or before the start of `j.epoch` are a prefix of the path, with root `j.root`.
  generalize hTj : j.epoch.toNat * slotsPerEpoch = Tj at hfE hjE
  generalize hTf : f.epoch.toNat * slotsPerEpoch = Tf at hfE hAf hstart
  obtain ⟨G, hG⟩ := filter_prefix_of_sorted Tj _ (hrun.blocks_sorted hhi)
  have hpre := hp.prefix hinv _ _ hG
  have hjroot : lastRootOf a ((blocksOf steps).filter (fun b => b.slot.toNat ≤ Tj)) = j.root := by
    rw [← rootAtSlot_eq_lastRootOf hanc steps (by omega), ← hTj, ← chainRoot_pos _ _ (by omega)]
    exact hj
  rw [hjroot] at hpre
  -- Walk from `j.root` to the start of `f.epoch`.
  have hwalk := hpre.checkpointBlock hinv ha (E := f.epoch) (by omega)
    (by
      rw [haslot, UInt64.le_iff_toNat_le, hstart]
      omega) s
  rw [filter_slot_le_toNat] at hwalk
  rw [hstart, ← filter_le_filter _ hfE, ← rootAtSlot_eq_lastRootOf hanc steps (by omega), ← hTf,
    ← chainRoot_pos _ _ hf1, hf] at hwalk
  exact hconf s s hwalk

end Conflict

end EthCLSpecs.Proofs.Heze
