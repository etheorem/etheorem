import EthCLSpecs.Proofs.Heze.PairScore
import EthCLSpecs.Proofs.Heze.ViableWindow

/-!
# `EthCLSpecs.Proofs.Heze.ForkSupport`: the support of a vote at any node of a path

`HonestVoteSide.lean` and `FullSupport.lean` prove three facts for the two children of
`pending r`:

- An honest vote on a head below `empty r` supports `empty r` (`honest_supported_below_empty`).
- A message that supports `full r` is from a slot after `r` (`fullSupport_slot_gt`).
- A chain below `empty r` in one store is a chain in another (`NodeBelow.transfer`).

The `getHead` walk compares the children of every node on its path. So this module proves the
three facts at any node:

- `honest_supported_below_any`: the supported node of an honest message lies below a node `y`
  above the head. If `y` is decided, its block must be from a slot before the message.
- `sibling_supporters_late`: a message that supports a child `z` of a node `x` is from a slot
  after the block of `x`. A vote for the block of `x` supports a payload node of `x` only from
  the next slot (`get_supported_node`, `gloas/fork-choice.md:436`). A child block of `x` is
  later than `x`.
- `NodeBelow.transfer_any`: a chain below `y` in store `A` is a chain in store `B`.

It also proves that `betterOf a b` returns `b` when `b` is strictly ahead on weight
(`betterOf_run_of_behind`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Config Store Root Slot ForkChoiceNode BeaconBlock Gwei
  LatestMessage getSupportedNode getWeight getHead)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- **The supported node of an honest message is `honestSupported`.** The message names the
head root, at a slot `t` no earlier than the head block `hb`, with the payload flag of
`honestAttestationIndex`. -/
theorem getSupportedNode_honest (store : Store map) (head : ForkChoiceNode) (hb : BeaconBlock)
    (hhb : FcMap.lookup store.blocks head.root = some hb) (t : Slot)
    {u u' : Store map} {n : ForkChoiceNode}
    (h : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
      store { slot := t, root := head.root,
              payloadPresent := honestAttestationIndex head hb.slot t == 1 }).run u
      = .ok (n, u')) :
    n = honestSupported head hb.slot.toNat t.toNat := by
  simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey, hhb, pure_bind] at h
  rw [run_pure_eq_ok _ _ _ _ h]
  unfold honestSupported
  by_cases hlt : hb.slot < t
  · have hlt' : hb.slot.toNat < t.toNat := UInt64.lt_iff_toNat_lt.mp hlt
    rw [ite_eq_left hlt, ite_eq_left hlt']
    have hne : (hb.slot == t) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      exact UInt64.lt_irrefl _ (he ▸ hlt)
    by_cases hf : head.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusFull
    · have hidx : (honestAttestationIndex head hb.slot t == 1) = true := by
        simp [honestAttestationIndex, hne, hf]
      rw [hidx, ite_eq_left hf]
      rfl
    · have hidx : (honestAttestationIndex head hb.slot t == 1) = false := by
        simp [honestAttestationIndex, hne, hf]
      rw [hidx, ite_eq_right hf]
      rfl
  · have hlt' : ¬ hb.slot.toNat < t.toNat := fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h')
    rw [ite_eq_right hlt, ite_eq_right hlt']
    rfl

/-- **Every stored block is no earlier than the anchor.** Under `SlotInv`, each stored block is
the anchor or has a stored parent with a smaller slot (`SlotsIncrease`). The induction runs on
the slot. -/
theorem SlotInv.anchor_le_slot {a : BeaconBlock} {s : Store map} (hinv : SlotInv a s) :
    ∀ k b, FcMap.lookup s.blocks k = some b → a.slot ≤ b.slot := by
  have key : ∀ n k b, FcMap.lookup s.blocks k = some b → b.slot.toNat ≤ n → a.slot ≤ b.slot := by
    intro n
    induction n with
    | zero =>
      intro k b hk hn
      rcases hinv.parentIn k b hk with rfl | ⟨pb, hpb⟩
      · exact UInt64.le_refl _
      · have := UInt64.lt_iff_toNat_lt.mp (hinv.slots k b pb hk hpb)
        exact absurd this (by omega)
    | succ n ih =>
      intro k b hk hn
      rcases hinv.parentIn k b hk with rfl | ⟨pb, hpb⟩
      · exact UInt64.le_refl _
      · have hlt := hinv.slots k b pb hk hpb
        have := UInt64.lt_iff_toNat_lt.mp hlt
        exact UInt64.le_of_lt (UInt64.lt_of_le_of_lt (ih _ pb hpb (by omega)) hlt)
  exact fun k b hk => key _ k b hk (Nat.le_refl _)

/-- A decided node below `y`, other than `y`, has its pending node below `y`. The only edge
into a decided node comes from the pending node of its root. -/
theorem NodeBelow.pending_of_decided_any (store : Store map) (y m : ForkChoiceNode)
    (h : NodeBelow store y m) (hne : m ≠ y)
    (hdec : m.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending) :
    NodeBelow store y (.pending m.root) := by
  cases h with
  | refl => exact absurd rfl hne
  | step p _ hp hpc =>
    rcases NodeEdge.cases_on_child store p m hpc with ⟨hp', -⟩ | ⟨_, _, _, _, hc, -⟩
    · exact hp' ▸ hp
    · exact absurd (congrArg ForkChoiceNode.payloadStatus hc) hdec

/-- **The supported node of an honest message lies below `y`.** The message names the head
root and carries the payload flag of `honestAttestationIndex`, at a slot `t` no earlier than
the head block. The head lies below `y`. A decided `y` has a block from a slot before `t`. The
supported node is the head, the pending node of the head root, or the EMPTY node of a pending
head (`honest_supported_below_empty`, at `y`). -/
theorem honest_supported_below_any (store : Store map) (y : ForkChoiceNode) (t : Slot)
    (hy : y.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending →
      ∀ yb, FcMap.lookup store.blocks y.root = some yb → yb.slot < t)
    (head : ForkChoiceNode) (hbelow : NodeBelow store y head) (hstatus : ValidStatus head)
    (hb : BeaconBlock) (hhb : FcMap.lookup store.blocks head.root = some hb) (hle : hb.slot ≤ t)
    {u u' : Store map} {n : ForkChoiceNode}
    (h : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
      store { slot := t, root := head.root,
              payloadPresent := honestAttestationIndex head hb.slot t == 1 }).run u
      = .ok (n, u')) :
    NodeBelow store y n := by
  simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey, hhb, pure_bind] at h
  rw [run_pure_eq_ok _ _ _ _ h]
  by_cases hlt : hb.slot < t
  · rw [ite_eq_left hlt]
    have hne : (hb.slot == t) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      exact UInt64.lt_irrefl _ (he ▸ hlt)
    rcases hstatus with hs | hs | hs
    · -- A pending head: the flag is `0`, so the supported node is the EMPTY child.
      have hidx : (honestAttestationIndex head hb.slot t == 1) = false := by
        simp [honestAttestationIndex, hne, hs, payloadStatus_full_ne_pending.symm]
      rw [hidx]
      have hp : head = .pending head.root := node_eq_of_root_status _ _ rfl hs
      exact NodeBelow.step _ _ hbelow (hp ▸ NodeEdge.empty head.root)
    · have hidx : (honestAttestationIndex head hb.slot t == 1) = false := by
        simp [honestAttestationIndex, hne, hs, payloadStatus_empty_ne_full]
      rw [hidx]
      have : ({ root := head.root, payloadStatus := EthCLSpecs.Heze.Const.payloadStatusEmpty }
          : ForkChoiceNode) = head := node_eq_of_root_status _ _ rfl hs.symm
      simp only [Bool.false_eq_true, ite_false]
      rw [this]
      exact hbelow
    · have hidx : (honestAttestationIndex head hb.slot t == 1) = true := by
        simp [honestAttestationIndex, hne, hs]
      rw [hidx]
      have : ({ root := head.root, payloadStatus := EthCLSpecs.Heze.Const.payloadStatusFull }
          : ForkChoiceNode) = head := node_eq_of_root_status _ _ rfl hs.symm
      simp only [ite_true]
      rw [this]
      exact hbelow
  · rw [ite_eq_right hlt]
    -- The head block is from slot `t`, so the supported node is the pending node of the head
    -- root. The block of `y` is older, so a decided head is not `y`. Then that pending node
    -- lies below `y`.
    have heq : hb.slot = t := by
      rcases UInt64.le_iff_lt_or_eq.mp hle with h' | h'
      · exact absurd h' hlt
      · exact h'
    have hne : ∀ hd : head.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending,
        head ≠ y := fun hd he => by
      subst he
      exact UInt64.lt_irrefl _ (heq ▸ hy hd hb hhb)
    rcases hstatus with hs | hs | hs
    · have hp : ({ root := head.root, payloadStatus := EthCLSpecs.Heze.Const.payloadStatusPending }
          : ForkChoiceNode) = head := node_eq_of_root_status _ _ rfl hs.symm
      rw [hp]
      exact hbelow
    · have hd : head.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending :=
        hs ▸ payloadStatus_empty_ne_pending
      exact NodeBelow.pending_of_decided_any store y head hbelow (hne hd) hd
    · have hd : head.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending :=
        hs ▸ payloadStatus_full_ne_pending
      exact NodeBelow.pending_of_decided_any store y head hbelow (hne hd) hd

/-- Below a node `y` with block `yb`, every node has the root of `y` or a block later than
`yb`. Below a decided `y`, a node with the root of `y` is `y` itself. -/
theorem NodeBelow.root_or_later (store : Store map) (hslots : SlotsIncrease store)
    {y n : ForkChoiceNode} {yb : BeaconBlock} (hyb : FcMap.lookup store.blocks y.root = some yb)
    (h : NodeBelow store y n) :
    (n.root = y.root ∧ (y.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending → n = y)) ∨
      ∃ nb, FcMap.lookup store.blocks n.root = some nb ∧ yb.slot < nb.slot := by
  by_cases hd : y.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
  · have hy : y = .pending y.root := node_eq_of_root_status _ _ rfl hd
    by_cases hr : n.root = y.root
    · exact .inl ⟨hr, fun h' => absurd hd h'⟩
    · rw [hy] at h
      exact .inr (below_slot_gt store hslots hyb h hr)
  · rcases NodeBelow.slot_gt_decided store hslots y hd yb hyb n h with he | h'
    · exact .inl ⟨by rw [he], fun _ => he⟩
    · exact .inr h'

/-- **A message that supports a child of `x` is from a slot after the block of `x`.** Take a
child `z` of `x` and a message whose supported node lies below `z`. The block at the message
root is no later than the message slot. A decided `z` has the root of `x`, and the message
supports it only from a slot after that block (`get_supported_node`). A pending `z` is a child
block of `x`, later than `x` under `SlotsIncrease`. -/
theorem sibling_supporters_late (store : Store map) (hslots : SlotsIncrease store)
    {x z : ForkChoiceNode} (hxz : NodeEdge store x z) {xb : BeaconBlock}
    (hxb : FcMap.lookup store.blocks x.root = some xb) (lm : LatestMessage)
    (hmsg : ∀ b, FcMap.lookup store.blocks lm.root = some b → b.slot ≤ lm.slot)
    {u u' : Store map} {m : ForkChoiceNode}
    (hsup : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u
      = .ok (m, u'))
    (hbelow : NodeBelow store z m) :
    xb.slot < lm.slot := by
  obtain ⟨-, hroot⟩ := getSupportedNode_run_valid store lm hsup
  rcases NodeEdge.cases_on_child store x z hxz with
    ⟨hp, hz⟩ | ⟨c, cb, s, s', hz, hcb, hpar, -⟩
  · -- `z` is a payload node of the block of `x`.
    have hxr : x.root = z.root := by rw [hp]; rfl
    have hzd : z.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
      rcases hz with hz | hz <;> rw [hz]
      · exact payloadStatus_empty_ne_pending
      · exact payloadStatus_full_ne_pending
    have hzb : FcMap.lookup store.blocks z.root = some xb := hxr ▸ hxb
    rcases NodeBelow.slot_gt_decided store hslots z hzd xb hzb m hbelow with hm | ⟨b, hb, hlt⟩
    · -- `m` is `z`: the decided branch of `get_supported_node` ran.
      subst hm
      have hr : lm.root = m.root := hroot.symm
      simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey, hr, hzb,
        pure_bind] at hsup
      have hn := run_pure_eq_ok _ _ _ _ hsup
      by_cases hs : xb.slot < lm.slot
      · exact hs
      · rw [ite_eq_right hs] at hn
        have hst := congrArg ForkChoiceNode.payloadStatus hn
        simp only at hst
        exact absurd hst hzd
    · rw [hroot] at hb
      exact UInt64.lt_of_lt_of_le hlt (hmsg b hb)
  · -- `z` is the pending node of a child block `c` of the block of `x`.
    subst hz
    have hxc : xb.slot < cb.slot := hslots c cb xb hcb (by rw [hpar]; exact hxb)
    by_cases hmc : m.root = c
    · rw [hroot] at hmc
      rw [hmc] at hmsg
      exact UInt64.lt_of_lt_of_le hxc (hmsg cb hcb)
    · obtain ⟨mb, hmb, hlt⟩ := below_slot_gt store hslots hcb hbelow hmc
      rw [hroot] at hmb
      exact UInt64.lt_trans hxc (UInt64.lt_of_lt_of_le hlt (hmsg mb hmb))

/-- **A chain below `y` in store `A` is a chain in store `B`.** This is `NodeBelow.transfer` at
any top node `y` with block `yb`, under four conditions:

- `B` holds the block of the bottom node.
- The two stores agree where both hold a block.
- `B` holds the parent of each stored block other than its anchor `a`.
- `a` is no later than `yb`.

A chain block other than the root of `y` is later than `yb` (`NodeBelow.root_or_later`), so it
is not `a`. -/
theorem NodeBelow.transfer_any (A B : Store map) (hslots : SlotsIncrease A)
    (y : ForkChoiceNode) (yb : BeaconBlock) (hyb : FcMap.lookup A.blocks y.root = some yb)
    (a : BeaconBlock)
    (hagree : ∀ k x z, FcMap.lookup A.blocks k = some x → FcMap.lookup B.blocks k = some z →
      x = z)
    (hpar : ∀ k x, FcMap.lookup B.blocks k = some x →
      x = a ∨ ∃ px, FcMap.lookup B.blocks x.parentRoot = some px)
    (ha : a.slot ≤ yb.slot) :
    ∀ n : ForkChoiceNode, NodeBelow A y n →
      (n = y ∨ ∃ x, FcMap.lookup B.blocks n.root = some x) →
      NodeBelow B y n := by
  intro n hn
  induction hn with
  | refl => intro _; exact NodeBelow.refl
  | step p c hp hpc ih =>
    intro hc
    by_cases hcy : c = y
    · rw [hcy]
      exact NodeBelow.refl
    have hcB : ∃ x, FcMap.lookup B.blocks c.root = some x := by
      rcases hc with hc | hc
      · exact absurd hc hcy
      · exact hc
    rcases NodeEdge.cases_on_child A p c hpc with
      ⟨hp', hcc | hcc⟩ | ⟨y', b, s, s', hcy', hb, hparent, hs⟩
    · -- `c` is EMPTY: the parent is the pending node of the same root.
      have hpB : p = y ∨ ∃ x, FcMap.lookup B.blocks p.root = some x :=
        .inr (by rw [hp']; exact hcB)
      refine NodeBelow.step p c (ih hpB) ?_
      rw [hp', hcc]
      exact NodeEdge.empty c.root
    · -- `c` is FULL: the parent is the pending node of the same root.
      have hpB : p = y ∨ ∃ x, FcMap.lookup B.blocks p.root = some x :=
        .inr (by rw [hp']; exact hcB)
      refine NodeBelow.step p c (ih hpB) ?_
      rw [hp', hcc]
      exact NodeEdge.full c.root
    · -- `c` is `pending y'`: `B` holds the same block at `y'`, and its parent.
      subst hcy'
      obtain ⟨x, hx⟩ := hcB
      have hxb : b = x := hagree y' b x hb hx
      subst hxb
      obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent A s s' b _ hs
      -- The block `b` is later than `yb`, so it is not the anchor.
      have hslot : yb.slot < b.slot := by
        rcases NodeBelow.root_or_later A hslots hyb (NodeBelow.step p _ hp hpc) with
          ⟨hr, hdy⟩ | ⟨x', hx', hlt⟩
        · -- `pending y'` has the root of `y`: `y` is pending, so the two are equal.
          exfalso
          by_cases hyd : y.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
          · exact hcy (node_eq_of_root_status _ _ hr (by rw [hyd]; rfl))
          · have := hdy hyd
            exact hcy this
        · rw [show (ForkChoiceNode.pending y').root = y' from rfl, hb] at hx'
          cases hx'
          exact hlt
      have hpbB : FcMap.lookup B.blocks b.parentRoot = some pb := by
        rcases hpar y' b hx with hba | ⟨px, hpx⟩
        · exfalso
          subst hba
          exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt ha hslot)
        · rw [hagree _ pb px hpb hpx]
          exact hpx
      have hpB : p = y ∨ ∃ x, FcMap.lookup B.blocks p.root = some x :=
        .inr ⟨pb, hparent ▸ hpbB⟩
      refine NodeBelow.step p _ (ih hpB) ?_
      exact NodeEdge.block p y' b B B hx hparent
        (getParentPayloadStatus_run_transfer A B b pb hpb hpbB hs B)

variable [Config]

/-- `betterOf a b` returns `b` when every pair of weight runs puts `b` strictly ahead. The
weight comparison comes first, so the root and the tiebreaker do not matter. -/
theorem betterOf_run_of_behind (store : Store map) (a b x : ForkChoiceNode) (s s' : Store map)
    (hbehind : ∀ (s₁ s₁' s₂ s₂' : Store map) (wA wB : Gwei),
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store a).run s₁
        = .ok (wA, s₁') →
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run s₂
        = .ok (wB, s₂') →
      wA < wB)
    (h : (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store a b).run s
      = .ok (x, s')) :
    x = b := by
  unfold getHead.betterOf at h
  obtain ⟨wA, s1, hwA, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨wB, s2, hwB, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hlt := hbehind _ _ _ _ _ _ hwA hwB
  have hng : ¬ (wA > wB) := fun hgt => UInt64.lt_irrefl _ (UInt64.lt_trans hlt hgt)
  simp only [hng, hlt, ↓reduceIte] at h
  exact run_pure_eq_ok _ _ _ _ h

end

end EthCLSpecs.Proofs.Heze
