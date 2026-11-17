import EthCLSpecs.Proofs.Heze.SiblingWeight

/-!
# `EthCLSpecs.Proofs.Heze.AncestorAny`: `is_ancestor` answers `true` below any node

`HonestVoteSide.lean` walks `get_ancestor` (`gloas/fork-choice.md:388`) from a node below
`empty r` to `empty r`. The `getHead` walk compares every pair of viable children, so the score
of any node needs the same fact. This module proves it for a target `d` of any status.

The walk from `m` toward the slot of `d`'s block stops at the first node of the chain whose
block is no later than that slot. Below a decided `d`, that node is `d`. Below a pending `d`, it
is `d`, or the EMPTY or the FULL node of the same root. Those two nodes have the block of `d`, so
the walk also stops at them. `is_ancestor` then compares the root. It compares the status only
for a decided target (`isAncestor_run_below_any`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok run_bind_eq_ok
  run_pure_eq_ok LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap Step fuelLoop)
open EthCLSpecs.Heze (Preset Store Root Slot ForkChoiceNode BeaconBlock ValidatorIndex
  getAncestor isAncestor getParentPayloadStatus)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- Below a node `d` with block `db`, under `SlotsIncrease`, every node has the root of `d` or a
block after `db`. Below a pending `d`, a node other than `d` is below one of its two decided
children (`NodeBelow.pending_split`). For a decided `d`, the fact is `NodeBelow.slot_gt_decided`.
-/
theorem NodeBelow.root_or_slot_gt (store : Store map) (hslots : SlotsIncrease store)
    (d : ForkChoiceNode) (db : BeaconBlock) (hdb : FcMap.lookup store.blocks d.root = some db)
    (n : ForkChoiceNode) (h : NodeBelow store d n) :
    n.root = d.root ∨ ∃ b, FcMap.lookup store.blocks n.root = some b ∧ db.slot < b.slot := by
  by_cases hd : d.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
  · have hdd : d = .pending d.root := node_eq_of_root_status _ _ rfl hd
    rw [hdd] at h
    by_cases hn : n = .pending d.root
    · exact .inl (by rw [hn]; rfl)
    · rcases NodeBelow.pending_split store d.root n h hn with h' | h'
      · rcases NodeBelow.slot_gt_decided store hslots (.empty d.root)
            payloadStatus_empty_ne_pending db hdb n h' with he | hb
        · exact .inl (by rw [he]; rfl)
        · exact .inr hb
      · rcases NodeBelow.slot_gt_decided store hslots (.full d.root)
            payloadStatus_full_ne_pending db hdb n h' with he | hb
        · exact .inl (by rw [he]; rfl)
        · exact .inr hb
  · rcases NodeBelow.slot_gt_decided store hslots d hd db hdb n h with he | hb
    · exact .inl (by rw [he])
    · exact .inr hb

/-- The node that the walk toward `d` returns: the root of `d`, and the status of `d` when
`d` is decided. -/
def AncHit (d a : ForkChoiceNode) : Prop :=
  a.root = d.root ∧ (d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending → a = d)

/-- **The walk toward `d`.** From a node `m` below `d`, the chain roots `L` above the slot of
`d`'s block are distinct blocks of the store, no later than `m`'s block. With more fuel than
roots, a successful walk returns a node at the root of `d`, equal to `d` when `d` is decided.
The induction follows `ancestor_chain` (`HonestVoteSide.lean`). A node at the root of `d` stops
the walk at once. -/
theorem ancestor_chain_any [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (d : ForkChoiceNode) (db : BeaconBlock)
    (hdb : FcMap.lookup store.blocks d.root = some db) :
    ∀ m : ForkChoiceNode, NodeBelow store d m →
      ∃ L : List Root, L.Nodup ∧
        (∀ x ∈ L, ∃ bx : BeaconBlock, FcMap.lookup store.blocks x = some bx ∧
          db.slot < bx.slot ∧
          ∀ mb : BeaconBlock, FcMap.lookup store.blocks m.root = some mb → bx.slot ≤ mb.slot) ∧
        ∀ (fuel : Nat) (exh a : ForkChoiceNode) (t t' : Store map), L.length < fuel →
          (fuelLoop fuel m exh (ancStep store db.slot)).run t = .ok (a, t') → AncHit d a := by
  -- A node at the root of `d` stops the walk at once. It is a hit when it is `d` for a decided
  -- `d`.
  have hstop : ∀ (m : ForkChoiceNode), m.root = d.root →
      (d.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending → m = d) →
      ∀ (fuel : Nat) (exh a : ForkChoiceNode) (t t' : Store map), 0 < fuel →
        (fuelLoop fuel m exh (ancStep store db.slot)).run t = .ok (a, t') → AncHit d a := by
    intro m hmr hmd fuel exh a t t' hf h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [fuelLoop] at h
    obtain ⟨st, t1, hst, h⟩ := run_bind_eq_ok _ _ _ _ h
    unfold ancStep at hst
    simp only [hmr, FcMap.getOrThrow, FcMap.getOrThrowKey, hdb, pure_bind, gt_iff_lt,
      UInt64.lt_irrefl, ite_false] at hst
    rw [run_pure_eq_ok _ _ _ _ hst] at h
    have ha := run_pure_eq_ok _ _ _ _ h
    subst ha
    exact ⟨hmr, hmd⟩
  intro m hm
  induction hm with
  | refl =>
    refine ⟨[], List.nodup_nil, by simp, ?_⟩
    intro fuel exh a t t' hf h
    exact hstop d rfl (fun _ => rfl) fuel exh a t t' hf h
  | step p c hp hpc ih =>
    obtain ⟨L, hnd, hL, hwalk⟩ := ih
    -- `c` is strictly below `d`, so it is not `d`.
    have hcd : c ≠ d := by
      intro hc
      subst hc
      have hpot := (NodeBelow.walkPot_le store hslots hp (by rw [hdb]; rfl))
      obtain ⟨-, hlt⟩ := NodeEdge.walkPot_lt store hslots hpc hpot.1
      omega
    rcases NodeBelow.root_or_slot_gt store hslots d db hdb c (NodeBelow.step p c hp hpc) with
      hcr | ⟨bc, hbc, hlt⟩
    · -- `c` has the root of `d`. Then `c` is a decided child of `pending d.root`, and `d` is
      -- that pending node. The walk stops at `c` at once.
      refine ⟨[], List.nodup_nil, by simp, ?_⟩
      intro fuel exh a t t' hf h
      refine hstop c hcr (fun hdec => ?_) fuel exh a t t' (by omega) h
      exfalso
      rcases NodeEdge.cases_on_child store p c hpc with
        ⟨hp', hcc⟩ | ⟨y, b, s, s', hcy, hb, hparent, hs⟩
      · -- `p` is `pending c.root = pending d.root`, and it lies below the decided `d`. But no
        -- node of the root of `d` other than `d` lies below a decided `d`.
        have hpd : p = .pending d.root := by rw [hp', hcr]
        subst hpd
        rcases NodeBelow.slot_gt_decided store hslots d hdec db hdb _ hp with he | ⟨x, hx, hxl⟩
        · exact hdec (congrArg ForkChoiceNode.payloadStatus he).symm
        · rw [show (ForkChoiceNode.pending d.root).root = d.root from rfl, hdb] at hx
          cases hx
          exact UInt64.lt_irrefl _ hxl
      · -- `c` is `pending y` with `y = d.root`, a pending node of the root of a decided `d`.
        subst hcy
        rcases NodeBelow.slot_gt_decided store hslots d hdec db hdb _
            (NodeBelow.step p _ hp hpc) with he | ⟨x, hx, hxl⟩
        · exact hdec (congrArg ForkChoiceNode.payloadStatus he).symm
        · rw [hcr, hdb] at hx
          cases hx
          exact UInt64.lt_irrefl _ hxl
    · rcases NodeEdge.cases_on_child store p c hpc with
        ⟨hp', -⟩ | ⟨y, b, s, s', hc, hb, hparent, hs⟩
      · -- `c` is decided: its walk takes the same first step as the walk from
        -- `pending c.root`.
        have hroot : p.root = c.root := by rw [hp']; rfl
        refine ⟨L, hnd, fun x hx => ?_, ?_⟩
        · obtain ⟨bx, hbx, h1, h2⟩ := hL x hx
          exact ⟨bx, hbx, h1, fun mb hmb => h2 mb (hroot ▸ hmb)⟩
        · intro fuel exh a t t' hf h
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          simp only [fuelLoop] at h
          obtain ⟨st, t1, hst, h⟩ := run_bind_eq_ok _ _ _ _ h
          obtain ⟨ps, rfl, hps⟩ := ancStep_run_above store db.slot c bc hbc hlt hst
          have hstp := ancStep_run_next_root store db.slot c p _ hroot hst
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
          obtain ⟨ps, rfl, hps⟩ := ancStep_run_above store db.slot _ bc hb hlt hst
          have hps' : ps = p.payloadStatus :=
            getParentPayloadStatus_run_val store _ _ _ _ bc _ _ hps hs
          have hq : ({ root := bc.parentRoot, payloadStatus := ps } : ForkChoiceNode) = p :=
            node_eq_of_root_status _ _ hparent hps'
          rw [hq] at h
          exact hwalk f exh a t1 t' (by simp at hf; omega) h

/-- **`is_ancestor` answers `true` below any node.** A successful run from a node below `d`
to `d` answers `true`: the walk lands at the root of `d` (`ancestor_chain_any`), and at the
status of `d` when `d` is decided. -/
theorem isAncestor_run_below_any [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) (d : ForkChoiceNode) (db : BeaconBlock)
    (hdb : FcMap.lookup store.blocks d.root = some db) (n : ForkChoiceNode)
    (hn : NodeBelow store d n) {t t' : Store map} {v : Bool}
    (h : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n d).run t
      = .ok (v, t')) :
    v = true := by
  obtain ⟨L, hnd, hL, hwalk⟩ := ancestor_chain_any store hslots d db hdb n hn
  have hlen := length_le_keys store L hnd fun x hx => by
    obtain ⟨bx, hbx, -⟩ := hL x hx
    exact ⟨bx, hbx⟩
  unfold isAncestor at h
  simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hdb, pure_bind] at h
  obtain ⟨a, t1, ha, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [getAncestor_eq_fuelLoop] at ha
  obtain ⟨hroot, hdec⟩ := hwalk _ n a t t1 (by omega) ha
  have hne : (a.root != d.root) = false := by simp [hroot]
  simp only [hne, Bool.false_eq_true, ite_false] at h
  have hv := run_pure_eq_ok _ _ _ _ h
  rw [hv]
  by_cases hd : d.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending
  · simp [hd]
  · rw [hdec hd]
    simp

end

end EthCLSpecs.Proofs.Heze
