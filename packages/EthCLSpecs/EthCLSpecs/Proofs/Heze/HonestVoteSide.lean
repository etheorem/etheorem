import EthCLSpecs.Proofs.Heze.HonestDuties
import EthCLSpecs.Proofs.Heze.PayloadRaceRefines

/-!
# `EthCLSpecs.Proofs.Heze.HonestVoteSide`: an honest vote below `empty r` counts for EMPTY

An honest attester votes for its head (phase0 `validator.md:638`). Its `data.index` signals
the payload status of the head (`gloas/validator.md:100-111`, `honestAttestationIndex`).
This module shows that such a vote, on a head below `empty r`, puts its validator on `empty`
in `storeSide`.

## The walk to `empty r`

`is_ancestor(store, node, empty r)` (`gloas/fork-choice.md:355`) walks `get_ancestor`
(`:337`) from `node` to the slot of `r`. A node below `empty r` has a unique parent chain to
`empty r` (`NodeEdge.parent_unique`). Each block on that chain has a slot above the slot of
`r` (`NodeBelow.slot_gt_empty`). Each step of the walk reads the block of the current node.
It moves to the parent that the block's parent root and parent payload status name. The
walk stops at the first node at or below the slot of `r`. That node is `empty r`.

The walk runs on fuel, `keys.length + 1` (`getAncestor_eq_fuelLoop`). It returns its start
node when it has no fuel left. So a run that succeeds could still return the wrong node.
`ancestor_chain` collects the roots of the chain in a list `L`. The roots are distinct,
because the slots strictly increase. They are keys of `blocks` (`LawfulFcMap`). So `L` is no
longer than the key list (`nodup_length_le_of_subset`). The fuel is enough
(`getAncestor_run_below_empty`).

## The supported node of an honest message

When the head block is older than the message, `get_supported_node` (`:385`) returns the
head root with the status of the payload flag. Otherwise it returns the pending node of the
head root. For an honest message, that node is the head, the pending node of the head root,
or the EMPTY node of a pending head. Each lies below `empty r` when the head does
(`honest_supported_below_empty`).

## The side in the store

`storeSide_empty_of_below` gives `storeSide store r i = .empty`. It needs the run of
`supports` at `empty r` to succeed. A successful score run of `empty r` runs `supports` at
every active unslashed index with a message. So the caller gets this from the score.

## A second store

The honest attester computes its head in its own store. The vote counts in the store of
another node. `NodeBelow.transfer` moves the chain to the second store. Where both stores
hold a block at one root, the two blocks must be equal. `SlotInv.atRoot` gives this unless
two blocks share a root. The second store holds the parent of each stored block other than
its anchor (`SlotInv.parentIn`). The anchor is no later than `r`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok run_bind_eq_ok
  run_pure_eq_ok)
open EthCLLib.Spec (HasherTag MapKind FcMap Step fuelLoop)
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Store Root Slot ForkChoiceNode BeaconBlock ValidatorIndex
  LatestMessage getAncestor isAncestor getParentPayloadStatus getSupportedNode)

/-- A list of distinct elements, each in `K`, is no longer than `K`. Core Lean has no
`List.Nodup.subperm`, so the proof erases one element of `K` per step. -/
theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (L K : List α), L.Nodup → (∀ x ∈ L, x ∈ K) → L.length ≤ K.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, K, hnd, hs => by
    have hx : x ∈ K := hs x List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    have ih := nodup_length_le_of_subset xs (K.erase x) hnd'.2 fun y hy =>
      (List.mem_erase_of_ne (fun (h : y = x) => hnd'.1 (h ▸ hy))).mpr
        (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem hx] at ih
    have : 0 < K.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The step of the `getAncestor` walk toward `slot`: the body of the `fuelLoop` in
`get_ancestor`. -/
def ancStep (store : Store map) (slot : Slot) (n : ForkChoiceNode) :
    ForkChoiceStoreRun (Store map) (Step ForkChoiceNode ForkChoiceNode) := do
  let block ← FcMap.getOrThrow store.blocks n.root
  if block.slot > slot then
    let status ← getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
      store block
    pure (.next { root := block.parentRoot, payloadStatus := status })
  else pure (.done n)

/-- `getAncestor` runs `fuelLoop` over `ancStep`, from the start node, with the start node
as the fuel-out value. The proof is `rfl`, so an edit to `getAncestor` breaks it. -/
theorem getAncestor_eq_fuelLoop (store : Store map) (node : ForkChoiceNode) (slot : Slot) :
    getAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store node slot =
      fuelLoop ((FcMap.keys store.blocks).length + 1) node node (ancStep store slot) :=
  rfl

/-- A `.next` step reads only the root of the node, so a node with the same root takes the
same step. -/
theorem ancStep_run_next_root (store : Store map) (slot : Slot) (m m' q : ForkChoiceNode)
    (hroot : m'.root = m.root) {t t' : Store map}
    (h : (ancStep store slot m).run t = .ok (.next q, t')) :
    (ancStep store slot m').run t = .ok (.next q, t') := by
  unfold ancStep at h ⊢
  rw [hroot]
  obtain ⟨b, t1, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [run_bind, hb, except_bind_ok]
  split at h
  · rename_i hgt
    rw [if_pos hgt]
    exact h
  · cases run_pure_eq_ok _ _ _ _ h

/-- A step at a node whose block is above `slot` goes to the node that the block's parent
root and parent payload status name. -/
theorem ancStep_run_above (store : Store map) (slot : Slot) (m : ForkChoiceNode)
    (b : BeaconBlock) (hb : FcMap.lookup store.blocks m.root = some b) (hgt : slot < b.slot)
    {t t' : Store map} {st : Step ForkChoiceNode ForkChoiceNode}
    (h : (ancStep store slot m).run t = .ok (st, t')) :
    ∃ ps : UInt8, st = .next { root := b.parentRoot, payloadStatus := ps } ∧
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run t
        = .ok (ps, t') := by
  unfold ancStep at h
  simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hb, pure_bind] at h
  rw [if_pos hgt] at h
  obtain ⟨ps, t1, hps, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [run_pure] at h
  injection h with h
  injection h with h1 h2
  subst h1 h2
  exact ⟨ps, rfl, hps⟩

/-- Slots grow below `empty r`, under `SlotsIncrease`. Every node below `empty r`, other
than `empty r` itself, has a block with a greater slot than the block at `r`. This is
`NodeBelow.slot_gt_decided` for the EMPTY node. -/
theorem NodeBelow.slot_gt_empty (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rootBlock : BeaconBlock) (hblock : FcMap.lookup store.blocks r = some rootBlock)
    (n : ForkChoiceNode) (h : NodeBelow store (.empty r) n) :
    n = .empty r ∨
      ∃ b : BeaconBlock, FcMap.lookup store.blocks n.root = some b ∧ rootBlock.slot < b.slot :=
  NodeBelow.slot_gt_decided store hslots _ payloadStatus_empty_ne_pending rootBlock hblock n h

/-- The walk from a node below `empty r` toward the slot of `r`. The chain roots `L` are
distinct, sit in `blocks` above the slot of `r`, and lie at or below the slot of the node's
own block. With more fuel than chain roots, a successful walk returns `empty r`.

The induction follows `NodeBelow` downward from `empty r`. At `empty r` the walk stops at
once. A decided child takes the same first step as the pending node of its root
(`ancStep_run_next_root`). So it keeps the list of that node. A pending child steps to its
parent, and its root joins the list. -/
theorem ancestor_chain (store : Store map) (hslots : SlotsIncrease store) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb) :
    ∀ m : ForkChoiceNode, NodeBelow store (.empty r) m →
      ∃ L : List Root, L.Nodup ∧
        (∀ x ∈ L, ∃ bx : BeaconBlock, FcMap.lookup store.blocks x = some bx ∧
          rb.slot < bx.slot ∧
          ∀ mb : BeaconBlock, FcMap.lookup store.blocks m.root = some mb → bx.slot ≤ mb.slot) ∧
        ∀ (fuel : Nat) (exh a : ForkChoiceNode) (t t' : Store map), L.length < fuel →
          (fuelLoop fuel m exh (ancStep store rb.slot)).run t = .ok (a, t') →
          a = .empty r := by
  intro m hm
  induction hm with
  | refl =>
    refine ⟨[], List.nodup_nil, by simp, ?_⟩
    intro fuel exh a t t' hf h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [fuelLoop] at h
    obtain ⟨st, t1, hst, h⟩ := run_bind_eq_ok _ _ _ _ h
    unfold ancStep at hst
    simp only [ForkChoiceNode.empty, FcMap.getOrThrow, FcMap.getOrThrowKey, hrb, pure_bind,
      gt_iff_lt, UInt64.lt_irrefl, if_false] at hst
    rw [run_pure_eq_ok _ _ _ _ hst] at h
    exact run_pure_eq_ok _ _ _ _ h
  | step p c hp hpc ih =>
    obtain ⟨L, hnd, hL, hwalk⟩ := ih
    -- `c` is not `empty r`, and its block sits above the slot of `r`.
    have hcne : c ≠ .empty r ∧ ∃ b, FcMap.lookup store.blocks c.root = some b ∧ rb.slot < b.slot := by
      rcases NodeBelow.slot_gt_empty store hslots r rb hrb c (NodeBelow.step p c hp hpc) with
        hc | hc
      · exfalso
        -- `c = empty r` needs the parent `pending r`, which is not below `empty r`.
        subst hc
        have hp' : p = .pending r :=
          NodeEdge.parent_unique store p _ _ hpc (NodeEdge.empty r)
        subst hp'
        rcases NodeBelow.slot_gt_empty store hslots r rb hrb _ hp with hpe | ⟨b, hb, hlt⟩
        · exact payloadStatus_empty_ne_pending (congrArg ForkChoiceNode.payloadStatus hpe).symm
        · rw [show (ForkChoiceNode.pending r).root = r from rfl, hrb] at hb
          cases hb
          exact UInt64.lt_irrefl _ hlt
      · obtain ⟨b, hb, hlt⟩ := hc
        refine ⟨fun he => ?_, b, hb, hlt⟩
        subst he
        rw [show (ForkChoiceNode.empty r).root = r from rfl, hrb] at hb
        cases hb
        exact UInt64.lt_irrefl _ hlt
    obtain ⟨-, bc, hbc, hlt⟩ := hcne
    rcases NodeEdge.cases_on_child store p c hpc with
      ⟨hp', -⟩ | ⟨y, b, s, s', hc, hb, hparent, hs⟩
    · -- `c` is decided: its walk takes the same first step as the walk from `pending c.root`.
      have hroot : p.root = c.root := by rw [hp']; rfl
      refine ⟨L, hnd, fun x hx => ?_, ?_⟩
      · obtain ⟨bx, hbx, h1, h2⟩ := hL x hx
        exact ⟨bx, hbx, h1, fun mb hmb => h2 mb (hroot ▸ hmb)⟩
      · intro fuel exh a t t' hf h
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        simp only [fuelLoop] at h
        obtain ⟨st, t1, hst, h⟩ := run_bind_eq_ok _ _ _ _ h
        obtain ⟨ps, rfl, hps⟩ := ancStep_run_above store rb.slot c bc hbc hlt hst
        have hstp := ancStep_run_next_root store rb.slot c p _ hroot hst
        apply hwalk (f + 1) exh a t t' hf
        simp only [fuelLoop, run_bind, hstp, except_bind_ok]
        exact h
    · -- `c` is `pending y`: its walk steps to `p`.
      subst hc
      have hb' : bc = b := Option.some.inj (hbc.symm.trans hb)
      subst hb'
      obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent store s s' bc _ hs
      have hpslot : pb.slot < bc.slot := hslots y bc pb hb hpb
      refine ⟨y :: L, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun hy => ?_, hnd⟩
        obtain ⟨bx, hbx, -, h2⟩ := hL y hy
        rw [hb] at hbx
        cases hbx
        have := h2 pb (hparent ▸ hpb)
        exact absurd (UInt64.lt_of_le_of_lt this hpslot) (UInt64.lt_irrefl _)
      · intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx
          exact ⟨bc, hb, hlt, fun mb hmb => by
            rw [show (ForkChoiceNode.pending x).root = x from rfl, hb] at hmb
            cases hmb
            exact UInt64.le_refl _⟩
        · obtain ⟨bx, hbx, h1, h2⟩ := hL x hx
          refine ⟨bx, hbx, h1, fun mb hmb => ?_⟩
          rw [show (ForkChoiceNode.pending y).root = y from rfl, hb] at hmb
          cases hmb
          exact UInt64.le_of_lt (UInt64.lt_of_le_of_lt (h2 pb (hparent ▸ hpb)) hpslot)
      · intro fuel exh a t t' hf h
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        simp only [fuelLoop] at h
        obtain ⟨st, t1, hst, h⟩ := run_bind_eq_ok _ _ _ _ h
        obtain ⟨ps, rfl, hps⟩ := ancStep_run_above store rb.slot _ bc hb hlt hst
        have hps' : ps = p.payloadStatus :=
          getParentPayloadStatus_run_val store _ _ _ _ bc _ _ hps hs
        have hq : ({ root := bc.parentRoot, payloadStatus := ps } : ForkChoiceNode) = p :=
          node_eq_of_root_status _ _ hparent hps'
        rw [hq] at h
        exact hwalk f exh a t1 t' (by simp at hf; omega) h

/-- A decided node below `empty r`, other than `empty r`, has its pending node below
`empty r` too. The only edge into a decided node comes from the pending node of its root. -/
theorem NodeBelow.pending_of_decided (store : Store map) (r : Root) (m : ForkChoiceNode)
    (h : NodeBelow store (.empty r) m) (hne : m ≠ .empty r)
    (hdec : m.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending) :
    NodeBelow store (.empty r) (.pending m.root) := by
  cases h with
  | refl => exact absurd rfl hne
  | step p _ hp hpc =>
    rcases NodeEdge.cases_on_child store p m hpc with ⟨hp', -⟩ | ⟨_, _, _, _, hc, -⟩
    · exact hp' ▸ hp
    · exact absurd (congrArg ForkChoiceNode.payloadStatus hc) hdec

/-- The supported node of an honest message lies below `empty r`. The message names the
head root and carries the payload flag of `honestAttestationIndex`. Its slot `t` is after the
slot of `r` and no earlier than the head block. The supported node is the head, the pending
node of the head root, or the EMPTY node of a pending head. -/
theorem honest_supported_below_empty (store : Store map) (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (head : ForkChoiceNode) (hbelow : NodeBelow store (.empty r) head)
    (hstatus : ValidStatus head) (hb : BeaconBlock)
    (hhb : FcMap.lookup store.blocks head.root = some hb) (t : Slot)
    (hle : hb.slot ≤ t) (hrt : rb.slot < t) {u u' : Store map} {n : ForkChoiceNode}
    (h : (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
      store { slot := t, root := head.root,
              payloadPresent := honestAttestationIndex head hb.slot t == 1 }).run u
      = .ok (n, u')) :
    NodeBelow store (.empty r) n := by
  simp only [getSupportedNode, FcMap.getOrThrow, FcMap.getOrThrowKey, hhb, pure_bind] at h
  rw [run_pure_eq_ok _ _ _ _ h]
  by_cases hlt : hb.slot < t
  · rw [if_pos hlt]
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
      simp only [Bool.false_eq_true, if_false]
      rw [this]
      exact hbelow
    · have hidx : (honestAttestationIndex head hb.slot t == 1) = true := by
        simp [honestAttestationIndex, hne, hs]
      rw [hidx]
      have : ({ root := head.root, payloadStatus := EthCLSpecs.Heze.Const.payloadStatusFull }
          : ForkChoiceNode) = head := node_eq_of_root_status _ _ rfl hs.symm
      simp only [if_true]
      rw [this]
      exact hbelow
  · rw [if_neg hlt]
    -- The head block is from slot `t`, so the head is not `empty r`, and the supported node
    -- is the pending node of the head root.
    have heq : hb.slot = t := by
      rcases UInt64.le_iff_lt_or_eq.mp hle with h' | h'
      · exact absurd h' hlt
      · exact h'
    have hne : head ≠ .empty r := by
      intro he
      subst he
      rw [show (ForkChoiceNode.empty r).root = r from rfl, hrb] at hhb
      cases hhb
      exact UInt64.lt_irrefl _ (heq ▸ hrt)
    rcases hstatus with hs | hs | hs
    · have hp : ({ root := head.root, payloadStatus := EthCLSpecs.Heze.Const.payloadStatusPending }
          : ForkChoiceNode) = head := node_eq_of_root_status _ _ rfl hs.symm
      rw [hp]
      exact hbelow
    · exact NodeBelow.pending_of_decided store r head hbelow hne
        (hs ▸ payloadStatus_empty_ne_pending)
    · exact NodeBelow.pending_of_decided store r head hbelow hne
        (hs ▸ payloadStatus_full_ne_pending)

/-- `getParentPayloadStatus` in a second store that holds the same parent block gives the
same status. -/
theorem getParentPayloadStatus_run_transfer (A B : Store map) (b pb : BeaconBlock)
    (hA : FcMap.lookup A.blocks b.parentRoot = some pb)
    (hB : FcMap.lookup B.blocks b.parentRoot = some pb) {s s' : Store map} {v : UInt8}
    (h : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) A b).run s
      = .ok (v, s')) (u : Store map) :
    (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map)) B b).run u
      = .ok (v, u) := by
  simp only [getParentPayloadStatus, FcMap.getOrThrow, FcMap.getOrThrowKey, hA, hB,
    pure_bind] at h ⊢
  rw [← run_pure_eq_ok _ _ _ _ h]
  rfl

/-- A chain below `empty r` in store `A` is a chain in store `B`. The theorem needs four
conditions:

- `B` holds the block of the bottom node.
- The two stores agree where both hold a block.
- `B` holds the parent of each stored block other than its anchor `a`.
- The anchor `a` is no later than `r`.

The induction follows the chain downward. It needs the block of each node in `B`. `hpar`
gives the parent of a chain block in `B`. A chain block has a slot above `r`, so it is not
`a`. -/
theorem NodeBelow.transfer (A B : Store map) (hslots : SlotsIncrease A) (r : Root)
    (rb : BeaconBlock) (hrb : FcMap.lookup A.blocks r = some rb) (a : BeaconBlock)
    (hagree : ∀ k x y, FcMap.lookup A.blocks k = some x → FcMap.lookup B.blocks k = some y →
      x = y)
    (hpar : ∀ k x, FcMap.lookup B.blocks k = some x →
      x = a ∨ ∃ px, FcMap.lookup B.blocks x.parentRoot = some px)
    (ha : a.slot ≤ rb.slot) :
    ∀ n : ForkChoiceNode, NodeBelow A (.empty r) n →
      (n = .empty r ∨ ∃ x, FcMap.lookup B.blocks n.root = some x) →
      NodeBelow B (.empty r) n := by
  intro n hn
  induction hn with
  | refl => intro _; exact NodeBelow.refl
  | step p c hp hpc ih =>
    intro hc
    rcases NodeEdge.cases_on_child A p c hpc with
      ⟨hp', hcc | hcc⟩ | ⟨y, b, s, s', hcy, hb, hparent, hs⟩
    · -- `c` is EMPTY: the parent is the pending node of the same root.
      have hpB : p = .empty r ∨ ∃ x, FcMap.lookup B.blocks p.root = some x := by
        rcases hc with hc | hc
        · exact Or.inr (by
            exfalso
            subst hc
            have hp'' : p = .pending r := hp'
            subst hp''
            rcases NodeBelow.slot_gt_empty A hslots r rb hrb _ hp with h | ⟨x, hx, hlt⟩
            · exact payloadStatus_empty_ne_pending (congrArg ForkChoiceNode.payloadStatus h).symm
            · rw [show (ForkChoiceNode.pending r).root = r from rfl, hrb] at hx
              cases hx
              exact UInt64.lt_irrefl _ hlt)
        · exact Or.inr (by rw [hp']; exact hc)
      refine NodeBelow.step p c (ih hpB) ?_
      rw [hp', hcc]
      exact NodeEdge.empty c.root
    · -- `c` is FULL: the parent is the pending node of the same root.
      have hpB : p = .empty r ∨ ∃ x, FcMap.lookup B.blocks p.root = some x := by
        rcases hc with hc | hc
        · exact absurd (congrArg ForkChoiceNode.payloadStatus (hcc.symm.trans hc))
            (payloadStatus_empty_ne_full.symm)
        · exact Or.inr (by rw [hp']; exact hc)
      refine NodeBelow.step p c (ih hpB) ?_
      rw [hp', hcc]
      exact NodeEdge.full c.root
    · -- `c` is `pending y`: `B` holds the same block at `y`, and its parent.
      subst hcy
      have hyB : ∃ x, FcMap.lookup B.blocks y = some x := by
        rcases hc with hc | hc
        · exact absurd (congrArg ForkChoiceNode.payloadStatus hc)
            payloadStatus_empty_ne_pending.symm
        · exact hc
      obtain ⟨x, hx⟩ := hyB
      have hxb : b = x := hagree y b x hb hx
      subst hxb
      obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent A s s' b _ hs
      have hslot : rb.slot < b.slot := by
        rcases NodeBelow.slot_gt_empty A hslots r rb hrb _ (NodeBelow.step p _ hp hpc) with
          h | ⟨x', hx', hlt⟩
        · exact absurd (congrArg ForkChoiceNode.payloadStatus h)
            payloadStatus_empty_ne_pending.symm
        · rw [show (ForkChoiceNode.pending y).root = y from rfl, hb] at hx'
          cases hx'
          exact hlt
      have hpbB : FcMap.lookup B.blocks b.parentRoot = some pb := by
        rcases hpar y b hx with hba | ⟨px, hpx⟩
        · exfalso
          subst hba
          exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt ha hslot)
        · rw [hagree _ pb px hpb hpx]
          exact hpx
      have hpB : p = .empty r ∨ ∃ x, FcMap.lookup B.blocks p.root = some x :=
        Or.inr ⟨pb, hparent ▸ hpbB⟩
      refine NodeBelow.step p _ (ih hpB) ?_
      exact NodeEdge.block p y b B B hx hparent
        (getParentPayloadStatus_run_transfer A B b pb hpb hpbB hs B)

variable [LawfulFcMap map Root]

/-- A list of distinct roots with entries in `blocks` is no longer than the key list. -/
theorem length_le_keys (store : Store map) (L : List Root) (hnd : L.Nodup)
    (hin : ∀ x ∈ L, ∃ b, FcMap.lookup store.blocks x = some b) :
    L.length ≤ (FcMap.keys store.blocks).length :=
  nodup_length_le_of_subset L _ hnd fun x hx => by
    obtain ⟨b, hb⟩ := hin x hx
    exact (LawfulFcMap.mem_keys _ x).mpr (by simp [hb])

/-- A successful `getAncestor` run from a node below `empty r` toward the slot of `r`
returns `empty r`. The chain roots are distinct keys of `blocks`, so the fuel
`keys.length + 1` is enough. -/
theorem getAncestor_run_below_empty (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (n : ForkChoiceNode) (hn : NodeBelow store (.empty r) n) {t t' : Store map}
    {a : ForkChoiceNode}
    (h : (getAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n rb.slot).run t
      = .ok (a, t')) :
    a = .empty r := by
  obtain ⟨L, hnd, hL, hwalk⟩ := ancestor_chain store hslots r rb hrb n hn
  have hlen := length_le_keys store L hnd fun x hx => by
    obtain ⟨bx, hbx, -⟩ := hL x hx
    exact ⟨bx, hbx⟩
  rw [getAncestor_eq_fuelLoop] at h
  exact hwalk _ n a t t' (by omega) h

/-- A successful `isAncestor` run from a node below `empty r` to a node `d` at the root `r`.
The walk lands on `empty r`, so the answer compares EMPTY with the status of `d`. -/
theorem isAncestor_run_below_empty_val (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (n : ForkChoiceNode) (hn : NodeBelow store (.empty r) n) (d : ForkChoiceNode)
    (hd : d.root = r) {t t' : Store map} {v : Bool}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n d).run t
      = .ok (v, t')) :
    v = (EthCLSpecs.Heze.Const.payloadStatusEmpty == d.payloadStatus ||
      d.payloadStatus == EthCLSpecs.Heze.Const.payloadStatusPending) := by
  unfold isAncestor at h
  simp only [hd, FcMap.getOrThrow, FcMap.getOrThrowKey, hrb, pure_bind] at h
  obtain ⟨a, t1, ha, h⟩ := run_bind_eq_ok _ _ _ _ h
  have ha' := getAncestor_run_below_empty store hslots r rb hrb n hn ha
  subst ha'
  simp [ForkChoiceNode.empty] at h
  exact run_pure_eq_ok _ _ _ _ h

/-- A successful `isAncestor` run from a node below `empty r` to `empty r` answers
`true`. -/
theorem isAncestor_run_below_empty (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (n : ForkChoiceNode) (hn : NodeBelow store (.empty r) n) {t t' : Store map} {v : Bool}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n
      (.empty r)).run t = .ok (v, t')) :
    v = true := by
  rw [isAncestor_run_below_empty_val store hslots r rb hrb n hn _ rfl h]
  rfl

/-- A successful `isAncestor` run from a node below `empty r` to `full r` answers `false`.
EMPTY is neither FULL nor PENDING. -/
theorem isAncestor_run_below_empty_full (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (n : ForkChoiceNode) (hn : NodeBelow store (.empty r) n) {t t' : Store map} {v : Bool}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n
      (.full r)).run t = .ok (v, t')) :
    v = false := by
  rw [isAncestor_run_below_empty_val store hslots r rb hrb n hn _ rfl h]
  rfl

/-- Take an index `i` that is not an equivocator, with a latest message that supports a node
below `empty r`. The `supports` run at `empty r` succeeds. Then the store puts `i` on
`empty`. The FULL test answers `false`, by a successful run or by a failed one. -/
theorem storeSide_empty_of_below (store : Store map) (hslots : SlotsIncrease store)
    (r : Root) (rb : BeaconBlock) (hrb : FcMap.lookup store.blocks r = some rb)
    (i : ValidatorIndex) (lm : LatestMessage)
    (hlm : FcMap.lookup store.latestMessages i = some lm)
    (heq : store.equivocatingIndices.contains i = false)
    (hsup : ∀ (u u' : Store map) (n : ForkChoiceNode),
      (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
        store lm).run u = .ok (n, u') → NodeBelow store (.empty r) n)
    (hok : ∃ (b : Bool) (u : Store map),
      (supports store (.empty r) i).run store = .ok (b, u)) :
    storeSide store r i.toNat = .empty := by
  have hval : ∀ (node : ForkChoiceNode) (b : Bool) (u u' : Store map),
      (supports store node i).run u = .ok (b, u') →
      ∃ n v w, (getSupportedNode
          (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u = .ok (n, v) ∧
        (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n node).run v
          = .ok (b, w) := by
    intro node b u u' h
    unfold supports at h
    rw [hlm] at h
    simp only [heq, Bool.false_eq_true, if_false] at h
    obtain ⟨n, v, hn, h⟩ := run_bind_eq_ok _ _ _ _ h
    exact ⟨n, v, u', hn, h⟩
  have hE : supportsVal store (.empty r) i = true := by
    obtain ⟨b, u, hb⟩ := hok
    obtain ⟨n, v, w, hn, ha⟩ := hval _ b _ _ hb
    have := isAncestor_run_below_empty store hslots r rb hrb n (hsup _ _ _ hn) ha
    subst this
    simp [supportsVal, hb]
  have hF : supportsVal store (.full r) i = false := by
    unfold supportsVal
    split
    · rename_i b u hb
      obtain ⟨n, v, w, hn, ha⟩ := hval _ b _ _ hb
      exact isAncestor_run_below_empty_full store hslots r rb hrb n (hsup _ _ _ hn) ha
    · rfl
  simp [storeSide, UInt64.ofNat_toNat, hE, hF]

end

end EthCLSpecs.Proofs.Heze
