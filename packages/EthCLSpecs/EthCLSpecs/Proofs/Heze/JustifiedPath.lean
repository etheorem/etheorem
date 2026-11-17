import EthCLSpecs.Proofs.Heze.SettingWalk
import EthCLSpecs.Proofs.Heze.ViableHonest

/-!
# `EthCLSpecs.Proofs.Heze.JustifiedPath`: a justified block no later than `rb` is above `r`

`get_head` walks from the pending node of the justified root, so the honest heads stay on the
path to `r` only when that node lies above `pending r`. This module proves it for an honest store
of the window whose justified block is no later than `rb`.

- The anchor checkpoint has the anchor root, and the anchor lies above every stored block
  (`SlotInv.anchor_above`).
- A later justified checkpoint is justified on a store run from the anchor (`justified_source`).
  An honest validator voted for it (`justified_honest_voter` past the base, `weigh_honest_voter`
  at a weigh step of the base). The target of an honest vote is the checkpoint block of the
  voter's head (`honestVotes`). In the window that head lies below `empty r` or at `pending r`
  (`VotesEmpty`), and before the window it lies on the path to `r` (`pathBefore`). Either way
  the checkpoint block, no later than `rb`, lies above `pending r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState LawfulFcMap run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec
open EthCLLib.Proofs.FFG (stakeSum)
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex ExecutionPayload Transaction ExecutionRequests Epoch Slot getCheckpointBlock
  getAncestor currentEpochOf previousEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section Store
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- **The anchor lies above every stored block.** Under `SlotInv`, a stored block is the anchor
or has a stored parent with a smaller slot. The read of the parent status succeeds, so a payload
node of the parent has an edge to the block. The induction runs on the slot. -/
theorem SlotInv.anchor_above {a : BeaconBlock} {s : Store map} (hinv : SlotInv a s) :
    ∀ k b, FcMap.lookup s.blocks k = some b → NodeBelow s (.pending (htr a)) (.pending k) := by
  have key : ∀ n k b, FcMap.lookup s.blocks k = some b → b.slot.toNat ≤ n →
      NodeBelow s (.pending (htr a)) (.pending k) := by
    intro n
    induction n with
    | zero =>
      intro k b hk hn
      rcases hinv.parentIn k b hk with rfl | ⟨pb, hpb⟩
      · rw [← hinv.atRoot k b hk]
        exact .refl
      · have := UInt64.lt_iff_toNat_lt.mp (hinv.slots k b pb hk hpb)
        exact absurd this (by omega)
    | succ n ih =>
      intro k b hk hn
      rcases hinv.parentIn k b hk with rfl | ⟨pb, hpb⟩
      · rw [← hinv.atRoot k b hk]
        exact .refl
      · have hlt := UInt64.lt_iff_toNat_lt.mp (hinv.slots k b pb hk hpb)
        have hpar := ih b.parentRoot pb hpb (by omega)
        obtain ⟨v, hv⟩ := getParentPayloadStatus_run_ok_of_parent s b pb hpb s
        have hedge : NodeEdge s { root := b.parentRoot, payloadStatus := v } (.pending k) :=
          NodeEdge.block _ k b s s hk rfl hv
        rcases getParentPayloadStatus_run_decided s s s b v hv with hs | hs
        · have he : ({ root := b.parentRoot, payloadStatus := v } : ForkChoiceNode) =
              .empty b.parentRoot := node_eq_of_root_status _ _ rfl hs
          rw [he] at hedge
          exact .step _ _ (.step _ _ hpar (NodeEdge.empty _)) hedge
        · have he : ({ root := b.parentRoot, payloadStatus := v } : ForkChoiceNode) =
              .full b.parentRoot := node_eq_of_root_status _ _ rfl hs
          rw [he] at hedge
          exact .step _ _ (.step _ _ hpar (NodeEdge.full _)) hedge
  exact fun k b hk => key _ k b hk (Nat.le_refl _)

/-- **The checkpoint block lies above its node.** `get_checkpoint_block` walks `get_ancestor`
from the pending node of the root, which returns an ancestor with a valid status
(`getAncestor_run_above`). The pending node of the result root lies above it. -/
theorem getCheckpointBlock_run_above (store : Store map) (k : Root) (e : Epoch)
    {u u' : Store map} {c : Root}
    (h : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store k e).run u
      = .ok (c, u')) :
    NodeBelow store (.pending c) (.pending k) := by
  unfold getCheckpointBlock at h
  obtain ⟨S, t1, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨m, t2, hm, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hc := run_pure_eq_ok _ _ _ _ h
  have hpk : ValidStatus (ForkChoiceNode.pending k) := .inl rfl
  have habove := getAncestor_run_above store (.pending k) S hpk hm
  have hvm : ValidStatus m := by
    rw [getAncestor_eq_fuelLoop] at hm
    exact EthCLLib.Proofs.fuelLoop_run_inv ValidStatus ValidStatus _ _
      (fun x q s s' hx hst => (ancStep_run_next_below store S x q hx hst).2)
      (fun x dd s s' hx hst => by
        unfold ancStep at hst
        obtain ⟨_, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
        split at hst
        · obtain ⟨_, _, -, hst⟩ := run_bind_eq_ok _ _ _ _ hst
          cases run_pure_eq_ok _ _ _ _ hst
        · have := run_pure_eq_ok _ _ _ _ hst
          injection this with this
          exact this ▸ hx) hpk _ _ t1 t2 m hpk hm
  rw [hc]
  exact NodeBelow.trans store _ _ _ (hvm.pending_above store) habove

/-- A successful checkpoint read has a stored block at its root: the first step of the walk of
`get_ancestor` reads it (`ancStep`). -/
theorem getCheckpointBlock_run_some (store : Store map) (k : Root) (e : Epoch) {u u' : Store map}
    {c : Root}
    (h : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store k e).run u
      = .ok (c, u')) :
    ∃ kb, FcMap.lookup store.blocks k = some kb := by
  unfold getCheckpointBlock at h
  obtain ⟨S, t1, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨m, t2, hm, -⟩ := run_bind_eq_ok _ _ _ _ h
  rw [getAncestor_eq_fuelLoop] at hm
  simp only [fuelLoop] at hm
  obtain ⟨st, t3, hst, -⟩ := run_bind_eq_ok _ _ _ _ hm
  unfold ancStep at hst
  obtain ⟨b, t4, hb, -⟩ := run_bind_eq_ok _ _ _ _ hst
  unfold FcMap.getOrThrow FcMap.getOrThrowKey at hb
  split at hb
  · rename_i v hv
    exact ⟨v, hv⟩
  · cases hb

/-- **The checkpoint block of `r` is `c`.** `c` is a stored block no later than the first slot `S`
of `e`, with `pending c` above `pending r`, and no block strictly between them on the path is
from `S` or before. Then the walk of `get_checkpoint_block` from `r` passes the blocks after `S`
(`cb_below_eq`) and stops at `c` (`getCheckpointBlock_run_stop`). -/
theorem cb_r_of_contra [LawfulFcMap map Root] (store : Store map) (hslots : SlotsIncrease store) {c r : Root}
    {cb : BeaconBlock} (hcb : FcMap.lookup store.blocks c = some cb) (e : Epoch) (S : Slot)
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok S)
    (hcS : ¬ cb.slot > S) (hcr : NodeBelow store (.pending c) (.pending r))
    (hno : ∀ y, NodeBelow store (.pending c) y → NodeBelow store y (.pending r) → y.root ≠ c →
      ∀ yb, FcMap.lookup store.blocks y.root = some yb → ¬ S < yb.slot → False)
    (u : Store map) :
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store r e).run u
      = .ok (c, u) := by
  have heq := cb_below_eq store hslots hcb e S hS hcr fun y hy hyr hne => by
    obtain ⟨yb, hyb⟩ := below_stored hy hcb
    exact ⟨yb, hyb, Classical.byContradiction fun h => hno y hy hyr hne yb hyb h⟩
  exact (heq u).trans (getCheckpointBlock_run_stop store c cb hcb e S hS hcS u)

/-- An honest supported node has the root of the head. -/
theorem honestSupported_root (h : ForkChoiceNode) (hs t : Nat) :
    (honestSupported h hs t).root = h.root := by
  unfold honestSupported
  split
  · split <;> rfl
  · rfl

/-- The pending node of the root of an honest supported node lies above it. -/
theorem honestSupported_pending_above (store : Store map) (h : ForkChoiceNode) (hs t : Nat) :
    NodeBelow store (.pending h.root) (honestSupported h hs t) := by
  unfold honestSupported
  split
  · split
    · exact .step _ _ .refl (NodeEdge.full _)
    · exact .step _ _ .refl (NodeEdge.empty _)
  · exact .refl

end Store

section Target
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

include hw in
/-- **An honest target no later than `rb` lies above `pending r`.** Take an honest placed vote of
a store run of an honest store of the window, with a target `c` after the anchor epoch, whose
block is no later than `rb`. The target is the checkpoint block of the voter's head
(`honestVotes`).

- In the window the head lies below `empty r`. If the target epoch starts before `rb`, the head
  reads the checkpoint block of `r` (`cb_below_eq`), an ancestor of `r`
  (`getCheckpointBlock_run_above`). Otherwise the walk stops at `r` or at a block after `rb`
  (`cb_on_path`). The target is no later than `rb`, so it is `r`.
- Before the window the head lies on the path to `r` (`pathBefore`), and the target is an
  ancestor of the head.

`NodeBelow.transfer_any` moves the chain to the store of the run.

When the target epoch starts before `rb`, the target is also the checkpoint block of `r` in the
store of the run (`cb_r_of_contra`). The target block is no later than the epoch start
(`chainRoot_block`). Suppose a block `y` lies strictly between the target and `r`, from the
epoch start or before. Let `X` be the node of the voter's store whose checkpoint block is the
target. In the window `X` is `pending r`. Before the window `X` is the supported node of the
head. In both cases `y` lies above `X` (`pathBefore`, as `y` is no later than the vote). The
walk from `X` then stops at `y` or below it (`cb_on_path`). So the target is at or below `y`,
which the slots exclude. -/
theorem FinalitySetting.target_above_r
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t)
    {steps : List ChainStep} {k : Root} {v' : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v')
    (hpath : AncestorPath a (run v t).store k (blocksOf steps))
    (hsr : StoreRun A a (run v t).store steps) {i : ValidatorIndex}
    {d : EthCLSpecs.Heze.AttestationData} (hhon : honestOf i = true)
    (hvote : RunVote (2 ^ 64 - 1) A steps i d) {cb : BeaconBlock}
    (hcb : FcMap.lookup (run v t).store.blocks d.target.root = some cb) (hcle : cb.slot ≤ rb.slot)
    (hdA : epochOf A < d.target.epoch.toNat) :
    NodeBelow (run v t).store (.pending d.target.root) (.pending r) ∧
      (rb.slot > d.target.epoch * UInt64.ofNat slotsPerEpoch → ∀ u,
        (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) (run v t).store r
          d.target.epoch).run u = .ok (d.target.root, u)) := by
  have hBlk : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hn := hset.fields.nodeOk v hv
  have hq := hset.held v hv t ht ht'
  have hinvB : SlotInv a (run v t).store := hset.anchorBlock v hv ▸ hq.slotInv hw hn hcol
  -- The vote is from a slot after the anchor block and before `t`.
  obtain ⟨hep, b, hbmem, hbs⟩ := RunVote.slot_lt_block hvote hrun
  obtain ⟨k', hk'⟩ := hpath.mem_lookup hbmem
  have hlt : rb.slot.toNat < t := by unfold raceLo at ht; omega
  have hbt := hq.block_slot_le hn (hn.anchor_le_of_lt hlt) hk'
  have hdel := hset.delay
  have hdt : d.slot.toNat < t := by omega
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hda : a.slot.toNat ≤ d.slot.toNat := by
    have h1 : (epochOf A + 1) * slotsPerEpoch ≤ d.target.epoch.toNat * slotsPerEpoch :=
      Nat.mul_le_mul_right _ hdA
    have h2 := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
    rw [← hep] at h2
    have := Nat.add_one_mul (epochOf A) slotsPerEpoch
    omega
  obtain ⟨uu, uu', hck⟩ := hset.honestVotes v hv t ht ht' steps i d hsr hhon hvote hda (by omega)
  have hu := hset.fields.honestNode i hhon
  have hNu := hset.fields.nodeOk (nodeOf i) hu
  have hQu := hset.core (nodeOf i) hu d.slot.toNat hda (by omega)
  have hinvW : SlotInv a (run (nodeOf i) d.slot.toNat).store :=
    hset.anchorBlock _ hu ▸ hQu.slotInv hw hNu hcol
  -- The block of the target in the voter's store, and a transfer to the store of the run.
  have hagree : ∀ k x y, FcMap.lookup (run (nodeOf i) d.slot.toNat).store.blocks k = some x →
      FcMap.lookup (run v t).store.blocks k = some y → x = y :=
    fun _ _ _ hx hy => SlotInv.block_eq hinvW hinvB hBlk hx hy
  have hmove : ∀ (y : ForkChoiceNode) (yb : BeaconBlock),
      FcMap.lookup (run (nodeOf i) d.slot.toNat).store.blocks y.root = some yb →
      ∀ n, NodeBelow (run (nodeOf i) d.slot.toNat).store y n →
      (∃ x, FcMap.lookup (run v t).store.blocks n.root = some x) →
      NodeBelow (run v t).store y n := fun y yb hyb n hn hnB =>
    NodeBelow.transfer_any _ _ hinvW.slots y yb hyb a hagree
      (fun k x hx => hinvB.parentIn k x hx) (hinvW.anchor_le_slot _ _ hyb) n hn (.inr hnB)
  have hfit : d.target.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
    have h2 := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
    rw [← hep] at h2
    have := d.slot.toNat_lt
    omega
  have hS := computeStartSlotAtEpoch_ok_of_lt hfit
  have hSv : (d.target.epoch * UInt64.ofNat slotsPerEpoch).toNat =
      d.target.epoch.toNat * slotsPerEpoch := by
    have hn' : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
      UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
    rw [UInt64.toNat_mul, hn', Nat.mod_eq_of_lt hfit]
  generalize hSdef : d.target.epoch * UInt64.ofNat slotsPerEpoch = S at hS hSv ⊢
  obtain ⟨-, -, -, -, hval, -⟩ := id hsr
  -- The target block is no later than the first slot of its epoch.
  have hcS : ¬ cb.slot > S := by
    have htg := hvote.target_eq hw (Nat.le_refl _) hval hset.roots hrun (by omega)
    have hroot : d.target.root = chainRoot A steps d.target.epoch.toNat :=
      congrArg (fun c => c.root) htg
    have ha := (hset.storeFacts hw hcol hv ht ht').2.2.1
    refine fun hgt => absurd (UInt64.lt_iff_toNat_lt.mp hgt) (Nat.not_lt.mpr ?_)
    rw [hSv]
    rcases chainRoot_block hpath hinvB hset.anchorRoot hset.aligned (e := d.target.epoch.toNat)
        (by omega) (by omega) with h | ⟨b', hb', hbs'⟩
    · rw [hroot, h, ha] at hcb
      cases hcb
      exact Nat.le_trans haS (Nat.mul_le_mul_right _ (by omega))
    · rw [← hroot, hcb] at hb'
      cases hb'
      exact hbs'
  -- A transfer from the store of the run to the voter's store.
  have hmoveW : ∀ (y : ForkChoiceNode) (yb : BeaconBlock),
      FcMap.lookup (run v t).store.blocks y.root = some yb →
      ∀ n, NodeBelow (run v t).store y n →
      (∃ x, FcMap.lookup (run (nodeOf i) d.slot.toNat).store.blocks n.root = some x) →
      NodeBelow (run (nodeOf i) d.slot.toNat).store y n := fun y yb hyb n hn hnW =>
    NodeBelow.transfer_any _ _ hinvB.slots y yb hyb a
      (fun _ _ _ hx hy => SlotInv.block_eq hinvB hinvW hBlk hx hy)
      (fun k x hx => hinvW.parentIn k x hx) (hinvB.anchor_le_slot _ _ hyb) n hn (.inr hnW)
  -- A block from the epoch start or before, strictly below the target in the store of the run,
  -- is not above the node of the voter's store whose checkpoint block is the target.
  have hno : ∀ X : ForkChoiceNode,
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        (run (nodeOf i) d.slot.toNat).store X.root d.target.epoch).run uu
        = .ok (d.target.root, uu') →
      ∀ (y : ForkChoiceNode) (yb : BeaconBlock),
      FcMap.lookup (run (nodeOf i) d.slot.toNat).store.blocks y.root = some yb →
      ¬ yb.slot > S → NodeBelow (run (nodeOf i) d.slot.toNat).store (.pending y.root) X →
      y.root ≠ d.target.root → NodeBelow (run v t).store (.pending d.target.root) y → False := by
    intro X hX y yb hyb hyS hyX hne hBy
    obtain ⟨y', hy', hcb'⟩ := cb_on_path _ hinvW.slots hyb d.target.epoch _ hS hyS hyX
    have h1 := hcb' uu
    rw [hX] at h1
    injection h1 with h1
    injection h1 with h1
    rcases hy' with hy0 | ⟨hne', hyy', -, -⟩
    · exact hne (h1.trans hy0).symm
    · obtain ⟨tw, htw, hlt1⟩ := below_slot_gt _ hinvW.slots hyb hyy' hne'
      obtain ⟨yb2, hyb2, hlt2⟩ := below_slot_gt _ hinvB.slots hcb hBy hne
      have e1 : yb = yb2 := SlotInv.block_eq hinvW hinvB hBlk hyb hyb2
      change FcMap.lookup _ y' = some tw at htw
      rw [← h1] at htw
      have e2 : tw = cb := SlotInv.block_eq hinvW hinvB hBlk htw hcb
      subst e1 e2
      exact absurd (UInt64.lt_trans hlt1 hlt2) (UInt64.lt_irrefl _)
  -- The checkpoint block of `r` from a node `X` above which the early blocks of `r`'s path lie.
  have hcbr : ∀ X : ForkChoiceNode,
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        (run (nodeOf i) d.slot.toNat).store X.root d.target.epoch).run uu
        = .ok (d.target.root, uu') →
      (∃ xb, FcMap.lookup (run (nodeOf i) d.slot.toNat).store.blocks X.root = some xb) →
      (∀ (y : ForkChoiceNode) (yb : BeaconBlock),
        NodeBelow (run v t).store (.pending y.root) (.pending r) →
        FcMap.lookup (run v t).store.blocks y.root = some yb → ¬ yb.slot > S →
        NodeBelow (run (nodeOf i) d.slot.toNat).store (.pending y.root) X) →
      NodeBelow (run v t).store (.pending d.target.root) (.pending r) → ∀ u,
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) (run v t).store r
        d.target.epoch).run u = .ok (d.target.root, u) :=
    fun X hX ⟨xb, hxb⟩ hlift hFr => cb_r_of_contra _ hinvB.slots hcb d.target.epoch S hS hcS hFr
      fun y hy hyr hne yb hyb hyS => by
        have hpr : NodeBelow (run v t).store (.pending y.root) (.pending r) :=
          NodeBelow.trans _ _ _ _ (hy.pending_root rfl) hyr
        have hyX := hlift y yb hpr hyb hyS
        obtain ⟨ybW, hybW, -⟩ := NodeBelow.slot_le _ hinvW.slots _ _ hyX xb hxb
        have e : ybW = yb := SlotInv.block_eq hinvW hinvB hBlk hybW hyb
        subst e
        exact hno X hX y ybW hybW hyS hyX hne hy
  by_cases hwin : raceLo rb ≤ d.slot.toNat
  · -- In the window: the head of the voter lies below `empty r` or is `pending r`.
    have hQw := hset.held (nodeOf i) hu d.slot.toNat hwin (by omega)
    have hslW := hinvW.slots
    have hhr : NodeBelow (run (nodeOf i) d.slot.toNat).store (.pending r)
        (run (nodeOf i) d.slot.toNat).head := by
      rcases hV i hhon d ⟨v, hv, t, ht, ht', .inr ⟨steps, hsr, hvote⟩⟩ hwin hdt with h | h
      · exact NodeBelow.trans _ _ _ _ (.step _ _ .refl (NodeEdge.empty r)) h
      · rw [h]
        exact .refl
    by_cases hrS : rb.slot > S
    · -- The target epoch starts before `rb`: the head reads the checkpoint block of `r`.
      have heq := cb_below_eq _ hslW hQw.block d.target.epoch _ hS hhr fun y hy _ hne => by
        obtain ⟨yb, hyb, hlt'⟩ := below_slot_gt _ hslW hQw.block hy hne
        exact ⟨yb, hyb, UInt64.lt_trans hrS hlt'⟩
      rw [heq uu] at hck
      have habove := getCheckpointBlock_run_above _ r d.target.epoch hck
      obtain ⟨cw, hcw, -⟩ := NodeBelow.slot_le _ hslW _ _ habove rb hQw.block
      have hFr := hmove _ cw hcw _ habove ⟨rb, hq.block⟩
      exact ⟨hFr, fun _ => hcbr (.pending r) hck ⟨rb, hQw.block⟩
        (fun y yb hpr hyb _ => hmoveW (.pending y.root) yb hyb _ hpr ⟨rb, hQw.block⟩) hFr⟩
    · -- The target epoch starts at or after `rb`: the walk stops at `r` or after `rb`.
      refine ⟨?_, fun h => absurd h hrS⟩
      obtain ⟨y, hy, hcby⟩ := cb_on_path _ hslW hQw.block d.target.epoch _ hS hrS hhr
      have hyc : y = d.target.root := by
        have h1 := hcby uu
        rw [hck] at h1
        injection h1 with h1
        injection h1 with h1
        exact h1.symm
      rcases hy with hyr | ⟨hne, hry, -, yb, hyb, -⟩
      · rw [← hyc, hyr]
        exact .refl
      · exfalso
        obtain ⟨yb', hyb', hgt⟩ := below_slot_gt _ hslW hQw.block hry (fun h => hne h)
        rw [show (ForkChoiceNode.pending y).root = y from rfl] at hyb'
        rw [hyc] at hyb'
        have := hagree _ _ _ hyb' hcb
        subst this
        exact absurd hcle (UInt64.not_le.mpr hgt)
  · -- Before the window: the head lies on the path to `r`.
    obtain ⟨hb, hhb⟩ := getCheckpointBlock_run_some _ _ _ hck
    obtain ⟨hbB, hon, -⟩ := hset.pathBefore (nodeOf i) hu d.slot.toNat hda (by omega) hb hhb v hv t
      ht ht'
    have habove := getCheckpointBlock_run_above _ _ d.target.epoch hck
    obtain ⟨cw, hcw, -⟩ := NodeBelow.slot_le _ hinvW.slots _ _ habove hb hhb
    have h1 := hmove _ cw hcw _ habove ⟨hb, hbB⟩
    have hFr := NodeBelow.trans _ _ _ _ (NodeBelow.trans _ _ _ _ h1
      (honestSupported_pending_above _ _ hb.slot.toNat d.slot.toNat)) hon
    refine ⟨hFr, fun _ => ?_⟩
    -- The supported node of the head has the root of the head.
    have hsr' := honestSupported_root (run (nodeOf i) d.slot.toNat).head hb.slot.toNat d.slot.toNat
    obtain ⟨-, -, hsub⟩ := hset.pathBefore (nodeOf i) hu d.slot.toNat hda (by omega) hb hhb v hv t
      ht ht'
    refine hcbr (honestSupported (run (nodeOf i) d.slot.toNat).head hb.slot.toNat d.slot.toNat)
      (by rw [hsr']; exact hck) ⟨hb, by rw [hsr']; exact hhb⟩ (fun y yb hpr hyb hyS => ?_) hFr
    -- A block of `r`'s path from the epoch start or before is no later than the vote.
    have hsup : supSlot (run v t).store (.pending y.root) ≤ d.slot.toNat := by
      unfold supSlot
      rw [show (ForkChoiceNode.pending y.root).root = y.root from rfl, hyb]
      dsimp only
      simp only [show (ForkChoiceNode.pending y.root).payloadStatus =
        EthCLSpecs.Heze.Const.payloadStatusPending from rfl, ite_true, Nat.add_zero]
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hyS)
      have h2 := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
      rw [← hep] at h2
      omega
    exact hmoveW (.pending y.root) yb hyb _ (hsub _ hpr hsup) ⟨hb, by rw [hsr']; exact hhb⟩

end Target

section Voter
variable [Preset] [HasherTag] [Config] [CryptoBackend]
  (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)

include hw in
/-- **A passed target test at a state of the run has an honest voter.** Take a state `u` on a
prefix of a run from `A`. Take an epoch `e` of `u`, current or previous, after the epoch of
`A`, and a passed target test at `u` for `e`. The adversary holds less than two thirds at `u`.

Each participating validator has a target flag for `e` (`targetFlag_of_participating`). The
current epoch of `A` is before `e`, so `A` holds no such flag. So a placed vote of the run set
the flag (`ChainRun.flag_located`). The target of that vote is the chain's checkpoint of `e`
(`RunVote.target_eq`). Suppose every participating validator were adversarial. Then the
adversarial stake would be above two thirds of the total (`link_weight`). -/
theorem weigh_honest_voter
    {steps : List ChainStep} {A v : BeaconState} (hrun : ChainRun (2 ^ 64 - 1) steps A v)
    (hval : ValidatedSteps steps) (hroots : AnchorRoots A)
    (honestOf : ValidatorIndex → Bool) {p q : List ChainStep} {u : BeaconState}
    (hpq : steps = p ++ q) (hu : ChainRun (2 ^ 64 - 1) p A u) (htot : RunTotals u)
    (hadv : 3 * advStake u honestOf < 2 * (totBal u).toNat) {e : Epoch}
    (he : e = currentEpochOf (pureState u) ∨ e = previousEpochOf (pureState u))
    (heA : (currentEpochOf (pureState A)).toNat < e.toNat)
    (htest : (tgtBal u e).toNat * 3 ≥ (totBal u).toNat * 2) :
    ∃ (i : ValidatorIndex) (d : EthCLSpecs.Heze.AttestationData), honestOf i = true ∧
      RunVote (2 ^ 64 - 1) A steps i d ∧ toCp d.target = cpOf A steps e.toNat := by
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ idx, EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx →
      ∀ x ∈ idx.toList, x ∈ regVals.filter fun i => !honestOf i := by
    intro idx hidx x hx
    refine List.mem_filter.mpr ⟨by simpa using mem_regVals x.toNat, ?_⟩
    have h64 := htot.2.2
    have hf := targetFlag_of_participating hidx h64 he hx
    rcases hu.flag_located (p := []) (.nil _) x.toNat e hf with h0 | ⟨d, hd, hv⟩
    · exact absurd h0.le_current (by omega)
    · rw [List.nil_append, UInt64.ofNat_toNat] at hv
      have hv' : RunVote (2 ^ 64 - 1) A steps x d := by
        rw [hpq]
        exact hv.append _
      have ht := hv'.target_eq hw (Nat.le_refl _) hval hroots hrun (by rw [hd]; omega)
      cases hh : honestOf x
      · rfl
      · exact absurd ⟨x, d, hh, hv', by rw [ht, hd]⟩ hno
  have hlw := link_weight htot he htest _ hall
  unfold advStake stakeSum at hadv
  omega

/-- A checkpoint of the weigh step of `e` is the chain's checkpoint of `e` under a passed
current test, or of `e - 1` under a passed previous test, at the state that weighs `e`. That
state is of epoch `e`. -/
theorem mem_weighCps {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState} {e : Nat} {x : Cp}
    (hx : x ∈ weighCps hi steps st₀ e) :
    ∃ u, stakeState hi steps st₀ e = some u ∧ epochOf u = e ∧
      ((jcOf u = true ∧ x = cpOf st₀ steps e) ∨ (jpOf u = true ∧ x = cpOf st₀ steps (e - 1))) := by
  unfold weighCps at hx
  split at hx
  · rename_i u hu
    split at hx
    · rename_i hc
      refine ⟨u, hu, hc.2, ?_⟩
      rcases List.mem_append.mp hx with h | h
      · split at h
        · exact .inl ⟨by assumption, List.mem_singleton.mp h⟩
        · exact absurd h List.not_mem_nil
      · split at h
        · exact .inr ⟨by assumption, List.mem_singleton.mp h⟩
        · exact absurd h List.not_mem_nil
    · exact absurd hx List.not_mem_nil
  · exact absurd hx List.not_mem_nil

include hw in
/-- **A passed test at the state that weighs `e` has an honest voter.** Take an epoch `e` after
the anchor epoch and no later than the epoch of the end state `v`. The state `u` that weighs `e`
is the weigh state of `e`, or the end state when the run has none (`stakeState`). In both cases
`u` is of epoch `e`. A passed current test names the chain's checkpoint of `e`. A passed previous
test names the chain's checkpoint of `e - 1`. Each has an honest voter (`weigh_honest_voter`). -/
theorem stake_honest_voter {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hval : ValidatedSteps steps)
    (hroots : AnchorRoots A) (honestOf : ValidatorIndex → Bool)
    (htot : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → RunTotals u) {B : Nat}
    (hall : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ B →
      3 * advStake u honestOf < 2 * (totBal u).toNat)
    {e : Nat} {u : BeaconState} (hs : stakeState (2 ^ 64 - 1) steps A e = some u)
    (heA : epochOf A < e) (hev : e ≤ epochOf v) (heB : e ≤ B) {x : Cp}
    (hx : (jcOf u = true ∧ x = cpOf A steps e) ∨
      (jpOf u = true ∧ x = cpOf A steps (e - 1) ∧ epochOf A < e - 1)) :
    ∃ (i : ValidatorIndex) (d : EthCLSpecs.Heze.AttestationData), honestOf i = true ∧
      RunVote (2 ^ 64 - 1) A steps i d ∧ toCp d.target = x := by
  obtain ⟨p, q, u', hpq, hs', hu, hle⟩ := stakeState_prefix hrun heA
  rw [hs] at hs'
  injection hs' with hs'
  subst hs'
  -- The state that weighs `e` is of epoch `e`.
  have heq : epochOf u = e := by
    refine Nat.le_antisymm hle ?_
    by_cases hwg : ∃ w, WeighAt (2 ^ 64 - 1) steps A e w
    · obtain ⟨w, hw'⟩ := hwg
      have h1 := stakeState_of_weigh (Nat.le_refl _) hw'
      rw [hs] at h1
      injection h1 with h1
      subst h1
      obtain ⟨-, -, -, -, -, he⟩ := hw'
      unfold epochOf
      omega
    · have h1 := stakeState_of_end hrun fun w hw' => hwg ⟨w, hw'⟩
      rw [hs] at h1
      injection h1 with h1
      subst h1
      exact hev
  have hadv := hall p q u hpq hu (heq ▸ heB)
  have ht := htot p q u hpq hu
  have hcA := currentEpochOf_epochOf A
  have hcu := currentEpochOf_epochOf u
  rcases hx with ⟨hjc, rfl⟩ | ⟨hjp, rfl, hlt⟩
  · obtain ⟨i, d, hh, hv, hd⟩ := weigh_honest_voter hw hrun hval hroots honestOf hpq hu ht hadv
      (e := currentEpochOf (pureState u)) (.inl rfl) (by omega) (of_decide_eq_true hjc)
    exact ⟨i, d, hh, hv, by rw [hd, hcu, heq]⟩
  · have hpu := previousEpochOf_toNat_sub u
    unfold epochOf at heq hcu hcA
    obtain ⟨i, d, hh, hv, hd⟩ := weigh_honest_voter hw hrun hval hroots honestOf hpq hu ht hadv
      (e := previousEpochOf (pureState u)) (.inr rfl) (by unfold epochOf at hlt; omega)
      (of_decide_eq_true hjp)
    exact ⟨i, d, hh, hv, by rw [hd, hpu, heq]⟩

include hw in
/-- **A base checkpoint after the anchor epoch has an honest voter.** Take a run from `A` that
reaches epoch 2, and a checkpoint `x` of the chain's base after the anchor epoch and no later
than the end of the run. The anchor checkpoints are no later than the anchor epoch
(`StateCkptOrd`), so `x` is a checkpoint of a weigh step (`chainBase`). The epoch of `x` is past
the anchor epoch. So only the current test of `e₀ + 1` and the two tests of epoch 2 can name
`x`. Each of those tests names the chain's checkpoint of the epoch it tests
(`stake_honest_voter`). -/
theorem base_honest_voter {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hval : ValidatedSteps steps)
    (hroots : AnchorRoots A) (hord : StateCkptOrd A) (honestOf : ValidatorIndex → Bool)
    (htot : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → RunTotals u) {B : Nat}
    (hall : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ B →
      3 * advStake u honestOf < 2 * (totBal u).toNat)
    {x : Cp} (hx : x ∈ chainBase (2 ^ 64 - 1) steps A) (hxA : epochOf A < x.epoch)
    (hxv : x.epoch ≤ epochOf v) (h2 : 2 ≤ epochOf v) (hxB : x.epoch + 1 ≤ B) :
    ∃ (i : ValidatorIndex) (d : EthCLSpecs.Heze.AttestationData), honestOf i = true ∧
      RunVote (2 ^ 64 - 1) A steps i d ∧ toCp d.target = x := by
  have hvote := @stake_honest_voter _ _ _ _ hw steps A v hrun hval hroots honestOf htot B hall
  unfold chainBase at hx
  simp only [List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · -- An anchor checkpoint is no later than the anchor epoch.
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2', h3⟩ := hord
    rw [UInt64.le_iff_toNat_le] at h1 h2' h3
    rw [previousEpochOf_toNat_sub] at h3
    simp only [anchorCps, List.mem_cons, List.not_mem_nil, or_false] at hc
    change epochOf A < c.epoch.toNat at hxA
    unfold epochOf at hxA
    generalize A.slot.toNat / slotsPerEpoch = E at h3 hxA
    rcases hc with rfl | rfl | rfl <;> omega
  · obtain ⟨u, -, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := mem_weighCps hx <;>
      simp only [cpOf] at hxA <;> omega
  · obtain ⟨u, hs, -, h | ⟨-, rfl⟩⟩ := mem_weighCps hx
    · obtain ⟨-, rfl⟩ := id h
      simp only [cpOf] at hxv hxB
      exact hvote hs (by omega) hxv (by omega) (.inl h)
    · simp only [cpOf] at hxA
      omega
  · split at hx
    · obtain ⟨u, hs, -, h | ⟨hp, rfl⟩⟩ := mem_weighCps hx
      · obtain ⟨-, rfl⟩ := id h
        simp only [cpOf] at hxA hxB
        exact hvote hs (by omega) h2 (by omega) (.inl h)
      · simp only [cpOf] at hxA hxB
        exact hvote hs (by omega) h2 (by omega) (.inr ⟨hp, rfl, by omega⟩)
    · exact absurd hx List.not_mem_nil

include hw in
/-- **A justified checkpoint after the anchor epoch has an honest voter.** Take a run from `A`
that reaches epoch 2, and a checkpoint `x` after the anchor epoch that its chain justifies, no
later than the end of the run. A link justifies it (`link_honest_voter`), or it is in the base
(`base_honest_voter`). -/
theorem justified_voter {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hval : ValidatedSteps steps)
    (hroots : AnchorRoots A) (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (honestOf : ValidatorIndex → Bool)
    (htot : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → RunTotals u) {B : Nat}
    (hall : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ B →
      3 * advStake u honestOf < 2 * (totBal u).toNat)
    {x : Cp} (hj : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) x)
    (hxA : epochOf A < x.epoch) (hxv : x.epoch ≤ epochOf v) (h2 : 2 ≤ epochOf v)
    (hxB : x.epoch + 1 ≤ B) :
    ∃ (i : ValidatorIndex) (d : EthCLSpecs.Heze.AttestationData), honestOf i = true ∧
      RunVote (2 ^ 64 - 1) A steps i d ∧ toCp d.target = x := by
  by_cases hb : x ∈ (ffgChain (2 ^ 64 - 1) steps A regVals).base
  · exact base_honest_voter hw hrun hval hroots hord honestOf htot hall hb hxA hxv h2 hxB
  · exact link_honest_voter hrun hcps hord honestOf hall hj hb hxA hxB

end Voter

section Justified
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

include hw in
/-- **A justified block no later than `rb` lies above `pending r`.** Take an honest store of the
window whose justified checkpoint `j` has a block no later than `rb`, after the honest votes
before the slot of the run are on the EMPTY side (`VotesEmpty`).

- The anchor checkpoint has the anchor root, which lies above every stored block
  (`SlotInv.anchor_above`).
- A later `j` is justified on the chain of a store run from `A` that reaches epoch 2
  (`justified_source`). An honest validator voted for it (`justified_voter`), and its target
  lies above `pending r` (`FinalitySetting.target_above_r`). -/
theorem FinalitySetting.justified_above_r
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {jb : BeaconBlock}
    (hjb : FcMap.lookup (run v t).store.blocks (run v t).store.justifiedCheckpoint.root = some jb)
    (hjle : jb.slot ≤ rb.slot)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t) :
    NodeBelow (run v t).store (.pending (run v t).store.justifiedCheckpoint.root) (.pending r) := by
  have hp := slotsPerEpochPos
  have hq := hset.held v hv t ht ht'
  obtain ⟨hI, hAbove, -, hjt, -⟩ := hset.storeFacts hw hcol hv ht ht'
  generalize hj : (run v t).store.justifiedCheckpoint = j at hjb hjt ⊢
  by_cases hja : j.root = htr a
  · rw [hja]
    exact hI.slot.anchor_above r rb hq.block
  have hjA : epochOf A < j.epoch.toNat := by
    rcases (hj ▸ hAbove.1 : Above A a j) with rfl | h
    · exact absurd rfl hja
    · exact h
  obtain ⟨k, steps, v', hrun, hpath, hjv, h2, hjus, hsr⟩ := justified_source hw (hj ▸ hI.jSource)
    (by rw [currentEpochOf_epochOf]; exact hjA) hset.roots hset.cps hset.ord hset.sphr
    (hset.totals v hv t ht ht')
  obtain ⟨-, -, -, -, hval, -⟩ := id hsr
  have hjE : j.epoch.toNat ≤ E₁ + 4 := by
    have : t / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right ht'
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    omega
  obtain ⟨i, d, hhon, hvote, hd⟩ := justified_voter hw hrun hval hset.roots hset.cps hset.ord
    honestOf (B := E₁ + 5)
    (fun p q u hpq hu => hset.totals v hv t ht ht' p q u (hpq ▸ hsr) hu)
    (fun p q u hpq hu hB => hset.allChains v hv t ht ht' p q u (hpq ▸ hsr) hu hB)
    hjus (by simp only [toCp]; exact hjA) (by simp only [toCp]; exact hjv) h2
    (by simp only [toCp]; omega)
  have hde : d.target.epoch.toNat = j.epoch.toNat := congrArg (·.epoch) hd
  have hdr : d.target.root = j.root := congrArg (·.root) hd
  rw [← hdr] at hjb ⊢
  exact (hset.target_above_r hw hcol hv ht ht' hV hrun hpath hsr hhon hvote hjb hjle
    (by omega)).1

include hw in
/-- **The finalized checkpoint is the checkpoint block of `r` when its epoch starts before
`rb`.** Take an honest store of the window, after the honest votes before the slot of the run
are on the EMPTY side. Its finalized checkpoint `F` is after the anchor epoch, and the epoch of
`F` starts before `rb`. The chain of a store run from `A` that reaches epoch 2 justifies `F`
(`finalized_source`), so an honest validator voted for `F` (`justified_voter`). The block of `F`
is the chain's block at the epoch start, no later than `rb` (`chainRoot_block`). Then the walk
of `get_checkpoint_block` from `r` stops at `F` (`FinalitySetting.target_above_r`). -/
theorem FinalitySetting.fin_cb_r
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t)
    (hFA : epochOf A < (run v t).store.finalizedCheckpoint.epoch.toNat) {S : Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch (run v t).store.finalizedCheckpoint.epoch :
      Except StateTransitionError Slot) = .ok S) (hSr : S < rb.slot) (u : Store map) :
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) (run v t).store r
      (run v t).store.finalizedCheckpoint.epoch).run u
      = .ok ((run v t).store.finalizedCheckpoint.root, u) := by
  have hp := slotsPerEpochPos
  obtain ⟨hI, -, ha, -, hft⟩ := hset.storeFacts hw hcol hv ht ht'
  generalize hF : (run v t).store.finalizedCheckpoint = F at hFA hS hft ⊢
  obtain ⟨k, steps, v', hrun, hpath, hfv, h2, hfin, hsr⟩ := finalized_source hw (hF ▸ hI.fSource)
    (by rw [currentEpochOf_epochOf]; exact hFA) hset.roots hset.cps hset.ord hset.sphr
    (hset.totals v hv t ht ht')
  obtain ⟨-, -, -, -, hval, -⟩ := id hsr
  have hjus : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) (toCp F) := by
    rcases hfin with hf | hb
    · cases hf with
      | one hb _ _ _ => exact hb
      | two hb _ _ _ _ _ => exact hb
    · exact .base hb
  have hFE : F.epoch.toNat ≤ E₁ + 4 := by
    have : t / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right ht'
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    omega
  -- The block of `F` is the chain's block at the first slot of its epoch.
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hon : chainRoot A steps F.epoch.toNat = F.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm.base x hx).2)
  have hfit : F.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
    have h1 := Nat.div_mul_le_self t slotsPerEpoch
    have h2 := Nat.mul_le_mul_right slotsPerEpoch hft
    obtain ⟨cs, hcsn, -⟩ := (hset.held v hv t ht ht').slot
    have := cs.toNat_lt
    omega
  rw [computeStartSlotAtEpoch_ok_of_lt hfit] at hS
  injection hS with hS
  subst hS
  have hSv : (F.epoch * UInt64.ofNat slotsPerEpoch).toNat = F.epoch.toNat * slotsPerEpoch := by
    have hn' : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
      UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
    rw [UInt64.toNat_mul, hn', Nat.mod_eq_of_lt hfit]
  have hSr' := UInt64.lt_iff_toNat_lt.mp hSr
  obtain ⟨fb, hfb, hfle⟩ : ∃ fb, FcMap.lookup (run v t).store.blocks F.root = some fb ∧
      fb.slot ≤ rb.slot := by
    rcases chainRoot_block hpath hI.slot hset.anchorRoot hset.aligned (e := F.epoch.toNat)
        (by omega) (by omega) with h | ⟨b', hb', hbs'⟩
    · refine ⟨a, by rw [← hon, h]; exact ha, UInt64.le_iff_toNat_le.mpr ?_⟩
      have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
        rw [anchor_slot_eq hset.anchorHeader]
        exact hset.aligned
      have := Nat.mul_le_mul_right slotsPerEpoch (Nat.le_of_lt hFA)
      omega
    · rw [hon] at hb'
      exact ⟨b', hb', UInt64.le_iff_toNat_le.mpr (by omega)⟩
  obtain ⟨i, d, hhon, hvote, hd⟩ := justified_voter hw hrun hval hset.roots hset.cps hset.ord
    honestOf (B := E₁ + 5)
    (fun p q u hpq hu => hset.totals v hv t ht ht' p q u (hpq ▸ hsr) hu)
    (fun p q u hpq hu hB => hset.allChains v hv t ht ht' p q u (hpq ▸ hsr) hu hB)
    hjus (by simp only [toCp]; exact hFA) (by simp only [toCp]; exact hfv) h2
    (by simp only [toCp]; omega)
  have hde : d.target.epoch = F.epoch := UInt64.toNat_inj.mp (congrArg (·.epoch) hd)
  have hdr : d.target.root = F.root := congrArg (·.root) hd
  rw [← hdr] at hfb ⊢
  rw [← hde] at hSr ⊢
  exact (hset.target_above_r hw hcol hv ht ht' hV hrun hpath hsr hhon hvote hfb hfle
    (by rw [hde]; exact hFA)).2 hSr u

end Justified

end EthCLSpecs.Proofs.Heze
