import EthCLSpecs.Proofs.Heze.StoreFinality
import EthCLSpecs.Proofs.Heze.HonestVoter
import EthCLSpecs.Proofs.Heze.EmptyTarget
import EthCLSpecs.Proofs.Heze.RaceLong
import EthCLSpecs.Proofs.Heze.StoreClock

/-!
# `EthCLSpecs.Proofs.Heze.FinalizationLiveness`: the censored payload stays off the honest heads

Take the block `rb` at `r`, of slot `N`, whose payload the adversary wants. The window runs
from `N + 1` to the first slot of epoch `E₁ + 4`.

## The window

Each honest head run of the window takes one of two cases.

- The justified block of the store is no later than `rb`. The race step of
  `race_empty_persists_long` applies at that slot.
- The justified block is past `rb`. The justified checkpoint is justified on the chain of a
  run from the anchor. It is past the base, so a link reaches it. The link voters hold two
  thirds of the stake. The adversary holds less than two thirds (`FinalitySetting.allChains`),
  so an honest validator voted for the checkpoint. The target of an honest vote is the
  checkpoint block of the voter's head at an earlier slot (`FinalitySetting.honestVotes`).
  That head is below `empty r`, and the target is past `rb`, so the target is below
  `empty r` too. The head of the store is below its justified block.

## The end of the window

At the first slot of `E₁ + 4`, every honest store has finalized `E₁` or later
(`honestStore_finalizes`). The finalized checkpoint is justified on a chain, so the argument of
the window puts it on the EMPTY side. Later heads of the node take the finality lock
(`honestNode_finality_lock`). The conflict case of the lock gives slashing evidence
(`honestNodes_accountable`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure LawfulFcMap)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex SignedBeaconBlock SignedInclusionList AttestationData IndexedAttestation
  ExecutionPayload Transaction ExecutionRequests getHead getCheckpointBlock Epoch)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotDurationMs)

/-! ## The setting -/

section Setting
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The first slot of epoch `E₁ + 4`: the end of the window. -/
def finSlot (E₁ : Nat) : Nat := (E₁ + 4) * slotsPerEpoch

/-- The premises of the composed theorem, for the block `rb` at `r`, the anchor state `A`, the
anchor block `a`, and the epoch `E₁`.

- `fields`, `base`, `first`: the race premises over the window, without a justified state.
- `cases`: each honest head run of the window has one of two justified blocks. A justified
  block no later than `rb` comes with a justified state and the count of the race. The other
  case is a justified block past `rb`.
- The anchor premises of `honestNodes_accountable`, and the anchor premises of
  `honestStore_finalizes`. The header of the anchor state is no later than the first slot of
  its epoch (`aligned`), as at genesis and at a checkpoint-sync anchor. So the chain root of
  an epoch from the anchor epoch on is the anchor block or a block of the run.
- `totals`: each honest store of the window meets the totals premise of
  `honestNodes_accountable` (`StoreTotals`).
- `allChains`: on every prefix of a store run of an honest store of the window, up to epoch
  `E₁ + 5`, the adversary holds less than two thirds of the total active balance.
- `honestVotes`: an honest vote of the window, on a store run of an honest store of the
  window, targets the checkpoint block of the voter's head at the vote slot.
- `early`: from the first slot of `E₁`, the checkpoint blocks of an honest head at the epochs
  from `E₁` are past `rb`.
- `chain`: the honest chain of `HonestChain`, and the block of its last slot of `E₁ + 3`.
  Each honest node receives that block before `E₁ + 4`.

`totals`, `allChains` and `honestVotes` read only the runs whose blocks an honest store
holds. A store run ends at a stored block. So no state of the run is later than the last
block of the store. -/
structure FinalitySetting {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (committees : Nat → Nat → Array ValidatorIndex) : Prop
    where
  fields : RaceSetting.Fields honest node run r rb (finSlot E₁) nodeOf honestOf committees
  base : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → (run v t).Base (node v) r rb t
  cases : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
    (∃ jst, (run v t).Ok (node v) r rb jst t ∧
      (raceLo rb < t → RaceCount jst honestOf committees (raceLo rb) t)) ∨
    ∃ jb, FcMap.lookup (run v t).store.blocks (run v t).store.justifiedCheckpoint.root = some jb ∧
      rb.slot < jb.slot
  first : ∀ v, honest v →
    ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head
  anchorState : ∀ v, honest v → (node v).anchorState = A
  anchorBlock : ∀ v, honest v → (node v).anchor = a
  stateRoots : ∀ v, honest v → ∀ (sb : SignedBeaconBlock) (w : Nat),
    (TraceEvent.handler (.block sb), w) ∈ (node v).events →
    sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot
  anchorRoot : htr (filledHeader A) = htr a
  anchorHeader : filledHeader A = headerOf a
  anchorFilled : HdrFilled A
  aligned : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch
  ord : StateCkptOrd A
  roots : AnchorRoots A
  cps : AnchorCps A
  sphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot
  totals : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → StoreTotals A a (run v t).store
  late : max (epochOf A + 2) 3 * slotsPerEpoch ≤ rb.slot.toNat
  before : rb.slot.toNat < E₁ * slotsPerEpoch
  delay : 0 < EthCLSpecs.Heze.Const.minAttestationInclusionDelay.toNat
  seconds : 1000 ∣ slotDurationMs.toNat
  slotPos : 0 < slotDurationMs.toNat
  allChains : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → ∀ p q u,
    StoreRun A a (run v t).store (p ++ q) → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ E₁ + 5 →
    3 * advStake u honestOf < 2 * (totBal u).toNat
  honestVotes : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
    ∀ steps i (d : AttestationData), StoreRun A a (run v t).store steps → honestOf i = true →
    RunVote (2 ^ 64 - 1) A steps i d → raceLo rb ≤ d.slot.toNat → d.slot.toNat < finSlot E₁ →
    ∃ u u', (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (run (nodeOf i) d.slot.toNat).store (run (nodeOf i) d.slot.toNat).head.root
      d.target.epoch).run u = .ok (d.target.root, u')
  early : ∀ v, honest v → ∀ t, E₁ * slotsPerEpoch ≤ t → t < finSlot E₁ →
    ∀ (e : Epoch) (c : Root) (u u' : Store map), E₁ ≤ e.toNat →
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (run v t).store (run v t).head.root e).run u = .ok (c, u') →
    ∃ cb, FcMap.lookup (run v t).store.blocks c = some cb ∧ rb.slot < cb.slot
  chain : ∃ (hi : Nat) (steps : List ChainStep) (st : BeaconState)
    (vals : List ValidatorIndex), HonestChain hi steps A st vals honestOf E₁ ∧
    ∃ (p q : List ChainStep) (sb : SignedBeaconBlock) (vb : Bool) (u w : BeaconState),
      steps = p ++ .block sb vb :: .slot :: q ∧ ChainRun hi p A u ∧ BlockStep sb vb u w ∧
      (u.slot.toNat + 1) % slotsPerEpoch = 0 ∧ u.slot.toNat / slotsPerEpoch = E₁ + 3 ∧
      ∀ v, honest v → ∃ (es1 es2 : List TraceEvent),
        (run v (finSlot E₁)).events.map Prod.fst = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
        ∀ arr mid, NodeTrace (node v).seed es1 arr mid → storeSlot mid < finSlot E₁

end Setting

/-! ## The chain root of a justified checkpoint -/

section Root
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]

/-- **The chain root of an epoch is the anchor block or a stored block of the run.** Take a run
whose blocks form an ancestor path of `s`, and an epoch `e` from the anchor epoch on, after
epoch 0. The anchor header is no later than the first slot of the anchor epoch. Then the chain
root of `e` is the root of `a`, or the root of a stored block no later than the first slot of
`e` (`rootAtSlot_eq_lastRootOf`). -/
theorem chainRoot_block {A : BeaconState} {a : BeaconBlock} {s : Store map}
    {steps : List ChainStep} {k : Root} (hpath : AncestorPath a s k (blocksOf steps))
    (hslot : SlotInv a s) (hanc : htr (filledHeader A) = htr a)
    (hal : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch) {e : Nat}
    (he1 : 1 ≤ e) (he : epochOf A ≤ e) :
    chainRoot A steps e = htr a ∨ ∃ b, FcMap.lookup s.blocks (chainRoot A steps e) = some b ∧
      b.slot.toNat ≤ e * slotsPerEpoch := by
  have hT : A.latestBlockHeader.slot.toNat ≤ e * slotsPerEpoch :=
    Nat.le_trans hal (Nat.mul_le_mul_right _ he)
  rw [chainRoot_pos _ _ he1, rootAtSlot_eq_lastRootOf hanc steps hT]
  unfold lastRootOf
  cases hl : ((blocksOf steps).filter (fun b => b.slot.toNat ≤ e * slotsPerEpoch)).getLast? with
  | none => exact .inl rfl
  | some b =>
    right
    have hm := List.mem_filter.mp (List.mem_of_getLast? hl)
    obtain ⟨k', hk'⟩ := hpath.mem_lookup hm.1
    have hr : htr b = k' := hslot.atRoot _ _ hk'
    refine ⟨b, ?_, by simpa using hm.2⟩
    show FcMap.lookup s.blocks (htr b) = some b
    rw [hr]
    exact hk'

end Root

/-! ## The stores of the window -/

section Facts
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

/-- The anchor store of an honest node, at `A` and `a`. -/
theorem FinalitySetting.anchorStore
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {v : Node} (hv : honest v) :
    EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok (node v).seed := by
  rw [← hset.anchorState v hv, ← hset.anchorBlock v hv]
  exact (hset.fields.nodeOk v hv).anchorStore

/-- The events of the prefix of a head run are events of the node. -/
theorem FinalitySetting.mem_events
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t) (ht' : t ≤ finSlot E₁)
    {x : TraceEvent} (hx : x ∈ (run v t).events.map Prod.fst) :
    ∃ w, (x, w) ∈ (node v).events := by
  obtain ⟨y, hy, hy1⟩ := List.mem_map.mp hx
  obtain ⟨rest, hsplit⟩ := (hset.base v hv t ht ht').isPrefix
  exact ⟨y.2, by rw [hsplit, ← hy1]; exact List.mem_append_left _ hy⟩

include hw in
/-- A store on the prefix of an honest head run meets `CkptInv`, unless a root collision
exists. -/
theorem FinalitySetting.prefixInv
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {es1 es2 : List TraceEvent}
    (hes : (run v t).events.map Prod.fst = es1 ++ es2)
    {arr : List (SignedInclusionList × UInt64)} {mid : Store map}
    (h : NodeTrace (node v).seed es1 arr mid) : CkptInv A a mid := by
  have hn := hset.fields.nodeOk v hv
  have ha := hset.anchorBlock v hv
  have hmem : ∀ x, x ∈ es1 → ∃ w, (x, w) ∈ (node v).events := fun x hx =>
    hset.mem_events hv ht ht' (by rw [hes]; exact List.mem_append_left _ hx)
  have hself : a.parentRoot ≠ htr a := ha ▸ hn.anchorSelf
  rcases NodeTrace.ckptInv hw h (CkptInv.anchor A a _ (hset.anchorStore hv) hself) hset.ord
      (fun e he => by
        obtain ⟨w, hw'⟩ := hmem _ he
        exact ha ▸ hn.noAnchorParent e w hw')
      (fun sb he => by
        obtain ⟨w, hw'⟩ := hmem _ he
        exact hset.stateRoots v hv sb w hw') with hi | hc
  · exact hi
  · exact absurd hc hcol

/-- The anchor epoch is before the slots of the window. -/
theorem FinalitySetting.anchor_le
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) {t : Nat}
    (ht : raceLo rb ≤ t) : epochOf A ≤ t / slotsPerEpoch := by
  have hlate := hset.late
  have hp := slotsPerEpochPos
  unfold raceLo at ht
  rw [Nat.le_div_iff_mul_le hp]
  have : epochOf A * slotsPerEpoch ≤ max (epochOf A + 2) 3 * slotsPerEpoch :=
    Nat.mul_le_mul_right _ (by omega)
  omega

include hw in
/-- **The store of an honest head run of the window.** It meets `CkptInv` and `CkptAbove`. It
holds the anchor block at its root. Its justified and finalized epochs are at most the epoch of
the slot of the run. -/
theorem FinalitySetting.storeFacts
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) :
    CkptInv A a (run v t).store ∧ CkptAbove A a (run v t).store ∧
      FcMap.lookup (run v t).store.blocks (htr a) = some a ∧
      (run v t).store.justifiedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch ∧
      (run v t).store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch := by
  have hn := hset.fields.nodeOk v hv
  have hq := hset.base v hv t ht ht'
  have hI : CkptInv A a (run v t).store :=
    hset.prefixInv hw hcol hv ht ht' (es2 := []) (by simp) hq.trace
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hAbove : CkptAbove A a (run v t).store :=
    hq.trace.ckptAbove (SlotInv.anchor A a _ (hset.anchorStore hv)
        ((hset.anchorBlock v hv) ▸ hn.anchorSelf)).statesPure
      (CkptAbove.anchor A a _ (hset.anchorStore hv))
  -- The store holds the anchor block at its root.
  have ha : FcMap.lookup (run v t).store.blocks (htr a) = some a := by
    obtain ⟨b', hb'⟩ := NodeTrace.blocks_persist hq.trace _ _
      (getForkchoiceStore_anchor A a _ (hset.anchorStore hv))
    have he := hI.slot.atRoot _ _ hb'
    have : b' = a := Classical.byContradiction fun hne => hcb ⟨b', a, hne, he⟩
    rw [this] at hb'
    exact hb'
  -- Each checkpoint epoch has a witness: the anchor epoch, or a block event of the prefix.
  have h0 : CkptWit A [] (node v).seed := by
    obtain ⟨e1, e2, e3, e4⟩ := getForkchoiceStore_ckpts A a _ (hset.anchorStore hv)
    exact ⟨.inl (Nat.le_of_eq e1), .inl (Nat.le_of_eq e2), .inl (Nat.le_of_eq e3),
      .inl (Nat.le_of_eq e4)⟩
  obtain ⟨wj, wf, -, -⟩ := hq.trace.ckptWit hset.ord
    (fun es1 es2 arr1 mid hes h1 => hset.prefixInv hw hcol hv ht ht' hes h1) h0
  have hwit : ∀ x, EpochWit A ((run v t).events.map Prod.fst) x → x ≤ t / slotsPerEpoch := by
    intro x hx
    rcases hx with hx | ⟨sb, hm, hx⟩
    · exact Nat.le_trans hx (hset.anchor_le ht)
    · exact Nat.le_trans hx (Nat.div_le_div_right ((hq.event_slot_le hn hm)))
  exact ⟨hI, hAbove, ha, hwit _ wj, hwit _ wf⟩

include hw in
/-- **A checkpoint justified on a chain of the store is on the EMPTY side.** Take an honest head
run of slot `t` and a store run of its store. The chain of the run
justifies `x`, past the base and before epoch `E₁ + 5`. Every honest head before `t` lies below
`empty r`. Then:

- An honest validator voted for `x` on the run (`justified_honest_voter`).
- The vote is from a slot before its block, and so before `t`. It is in the window, since `x`
  starts after `rb` (`RunVote.slot_lt_block`).
- The target is the checkpoint block of the voter's head (`honestVotes`). That head is below
  `empty r`. The target block is past `rb` (`hpast`), so the target is on the EMPTY side of the
  voter's store (`checkpointBlock_emptySide`).
- `NodeBelow.transfer` moves the EMPTY side to the store of the run. -/
theorem FinalitySetting.target_empty
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {steps : List ChainStep} {k : Root} {v' : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v')
    (hpath : AncestorPath a (run v t).store k (blocksOf steps))
    (hsr : StoreRun A a (run v t).store steps) {x : Cp}
    (hj : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) x)
    (hxK : anchorK A < x.epoch) (hxB : x.epoch + 1 ≤ E₁ + 5)
    (hlo : rb.slot.toNat < x.epoch * slotsPerEpoch)
    (hblk : ∃ xb, FcMap.lookup (run v t).store.blocks x.root = some xb)
    (hIH : ∀ u, honest u → ∀ t', raceLo rb ≤ t' → t' < t →
      NodeBelow (run u t').store (.empty r) (run u t').head)
    (hpast : ∀ u, honest u → ∀ t', raceLo rb ≤ t' → t' < t → t' / slotsPerEpoch = x.epoch →
      ∀ (e : Epoch) (uu uu' : Store map), e.toNat = x.epoch →
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        (run u t').store (run u t').head.root e).run uu = .ok (x.root, uu') →
      ∀ cb, FcMap.lookup (run u t').store.blocks x.root = some cb → rb.slot < cb.slot) :
    OnEmptySide (run v t).store r x.root := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hn := hset.fields.nodeOk v hv
  have hq := hset.base v hv t ht ht'
  have hinvs : SlotInv a (run v t).store := (hset.storeFacts hw hcol hv ht ht').1.slot
  obtain ⟨i, d, hhon, hvote, htg⟩ :=
    justified_honest_voter hrun hset.cps hset.ord honestOf
      (fun p q u he hu hB => hset.allChains v hv t ht ht' p q u (he ▸ hsr) hu hB) hj hxK hxB
  subst htg
  -- The vote is from a slot of the window, before `t`.
  obtain ⟨hep, b, hbmem, hbs⟩ := RunVote.slot_lt_block hvote hrun
  obtain ⟨k', hk'⟩ := hpath.mem_lookup hbmem
  have hlt : rb.slot.toNat < t := by unfold raceLo at ht; omega
  have hbt := hq.block_slot_le hn hlt hk'
  have hdel := hset.delay
  have hdt : d.slot.toNat < t := by omega
  have hdlo : raceLo rb ≤ d.slot.toNat := by
    have := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
    simp only [toCp] at hlo hep
    unfold raceLo
    rw [← hep] at this
    omega
  -- The target is the checkpoint block of the voter's head, below `empty r`.
  obtain ⟨uu, uu', hck⟩ := hset.honestVotes v hv t ht ht' steps i d hsr hhon hvote hdlo
    (by omega)
  have hu := hset.fields.honestNode i hhon
  have hbelow := hIH (nodeOf i) hu d.slot.toNat hdlo hdt
  have hqu := hset.base (nodeOf i) hu d.slot.toNat hdlo (by omega)
  have hinvu : SlotInv a (run (nodeOf i) d.slot.toNat).store :=
    hset.anchorBlock _ hu ▸ hqu.slotInv hw (hset.fields.nodeOk _ hu) hcol
  obtain ⟨cb, hcbk⟩ := checkpointBlock_block _ hinvu.slots r rb hqu.block _ hbelow _ _ _ _ hck
  have hgt := hpast (nodeOf i) hu d.slot.toNat hdlo hdt (by simp only [toCp]; exact hep.symm)
    d.target.epoch uu uu' rfl hck cb hcbk
  have hE := checkpointBlock_emptySide _ hinvu.slots r rb hqu.block _ hbelow _ _ _ _ hck cb hcbk
    hgt
  -- Move the EMPTY side to the store of the run.
  exact NodeBelow.transfer _ _ hinvu.slots r rb hqu.block a
    (fun _ _ _ hx hy => SlotInv.block_eq hinvu hinvs hcb hx hy)
    (fun k x hx => hinvs.parentIn k x hx) (hset.anchorBlock v hv ▸ hn.anchorSlot) _ hE
    (Or.inr hblk)

include hw in
/-- **A justified block past `rb` is on the EMPTY side.** The justified checkpoint `j` of an
honest store of the window has a block past `rb`. Every honest head before the slot of the run
lies below `empty r`. Then:

- `j` is not the anchor checkpoint, whose block is the anchor (`CkptAbove`).
- `j` is justified on the chain of a run from `A` along an ancestor path of the store
  (`justified_source`). Its root is a stored block no later than the first slot of its epoch
  (`chainRoot_block`). That block is the block past `rb`, so `j` is past the base.
- `FinalitySetting.target_empty` applies. A block of a voter's store at the root of `j` is the
  block past `rb`. -/
theorem FinalitySetting.justified_empty
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {jb : BeaconBlock}
    (hjb : FcMap.lookup (run v t).store.blocks (run v t).store.justifiedCheckpoint.root = some jb)
    (hjlt : rb.slot < jb.slot)
    (hIH : ∀ u, honest u → ∀ t', raceLo rb ≤ t' → t' < t →
      NodeBelow (run u t').store (.empty r) (run u t').head) :
    OnEmptySide (run v t).store r (run v t).store.justifiedCheckpoint.root := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  obtain ⟨hI, hAbove, ha, hjt, -⟩ := hset.storeFacts hw hcol hv ht ht'
  have hjlt' := UInt64.lt_iff_toNat_lt.mp hjlt
  have haslot : a.slot ≤ rb.slot := hset.anchorBlock v hv ▸ (hset.fields.nodeOk v hv).anchorSlot
  -- The root of `j` is not the anchor root: the anchor block is no later than `rb`.
  have hnota : (run v t).store.justifiedCheckpoint.root ≠ htr a := fun he => by
    rw [he, ha] at hjb
    cases hjb
    exact absurd haslot (UInt64.not_le.mpr hjlt)
  generalize hj : (run v t).store.justifiedCheckpoint = j at hjb hjt hnota ⊢
  have hjA : epochOf A < j.epoch.toNat := by
    rcases (hj ▸ hAbove.1 : Above A a j) with rfl | h
    · exact absurd rfl hnota
    · exact h
  obtain ⟨k, steps, v', hrun, hpath, -, hjus, hsr⟩ := justified_source hw (hj ▸ hI.jSource)
    (by rw [currentEpochOf_epochOf]; exact hjA) hset.roots hset.cps hset.ord hset.sphr
    (hset.totals v hv t ht ht')
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hon : chainRoot A steps j.epoch.toNat = j.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm.base x hx).2)
  -- The block at the root of `j` is no later than the first slot of its epoch.
  have hjS : jb.slot.toNat ≤ j.epoch.toNat * slotsPerEpoch := by
    rcases chainRoot_block hpath hI.slot hset.anchorRoot hset.aligned (e := j.epoch.toNat)
        (by omega) (Nat.le_of_lt hjA) with h | ⟨b, hb, hbs⟩
    · exact absurd (hon ▸ h) hnota
    · rw [hon, hjb] at hb
      cases hb
      exact hbs
  have hlate := hset.late
  have hK : anchorK A < j.epoch.toNat := by
    unfold anchorK
    have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < j.epoch.toNat * slotsPerEpoch := by omega
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    omega
  have hjE : j.epoch.toNat ≤ E₁ + 4 := by
    have : t / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right ht'
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    omega
  exact hset.target_empty hw hcol hv ht ht' hrun hpath hsr (x := toCp j) hjus hK (by
    simp only [toCp]; omega) (by simp only [toCp]; omega) ⟨jb, hjb⟩ hIH
    (fun u hu t' hlo' hlt' _ e uu uu' _ _ cb hcb' => by
      have hqu := hset.base u hu t' hlo' (by omega)
      have hinvu : SlotInv a (run u t').store :=
        hset.anchorBlock _ hu ▸ hqu.slotInv hw (hset.fields.nodeOk _ hu) hcol
      have : cb = jb := SlotInv.block_eq hinvu hI.slot hcb hcb' hjb
      rw [this]
      exact hjlt)

end Facts

/-! ## The theorems -/

section Main
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **The window.** Every honest head of the window lies below `empty r` and not below
`full r`, or a root collision exists. -/
theorem heads_avoid_full_window {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  right
  -- One slot: from the honest heads before `s` to the honest heads of `s`.
  have hstep : ∀ s, raceLo rb ≤ s → s ≤ finSlot E₁ →
      (∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
        NodeBelow (run u t).store (.empty r) (run u t).head) →
      ∀ v, honest v → NodeBelow (run v s).store (.empty r) (run v s).head ∧
        ¬ NodeBelow (run v s).store (.full r) (run v s).head := by
    intro s hlo hs hP v hv
    have hQ := hset.base v hv s hlo hs
    have hinv := hQ.slotInv hw (hset.fields.nodeOk v hv) hcol
    by_cases hfirst : s = raceLo rb
    · subst hfirst
      have hnf := hset.first v hv
      rcases NodeBelow.pending_split _ r _ hQ.setting.1 hQ.setting.2 with h | h
      · exact ⟨h, hnf⟩
      · exact absurd h hnf
    have hlos : raceLo rb < s := by omega
    obtain ⟨s', hrun⟩ := hQ.headRun
    rcases hset.cases v hv s hlo hs with ⟨jst, hOk, hcount⟩ | ⟨jb, hjb, hjlt⟩
    · -- The justified block is no later than `rb`: the race step.
      have hahead := hset.fields.weightAhead hw hset.base hcol v hv s hlos hs hOk
        (hcount hlos) hP
      obtain ⟨jb, hjb, hjle⟩ := hOk.justified
      obtain ⟨havoid, hbelow⟩ := getHead_run_below_empty _ r hahead
        (hinv.justified_not_below hQ.block hjb hjle) _ s' _ hrun
      exact ⟨hbelow hQ.setting.1 hQ.setting.2, havoid⟩
    · -- The justified block is past `rb`: it is on the EMPTY side.
      have hj := hset.justified_empty hw hcol hv hlo hs hjb hjlt hP
      have hhead := getHead_run_below_justified _ _ _ _ hrun
      exact ⟨NodeBelow.trans _ _ _ _ hj hhead,
        below_emptySide_not_full _ hinv.slots r rb hQ.block _ _ hj hhead⟩
  -- The induction over the slots of the window.
  have hall : ∀ s, s ≤ finSlot E₁ + 1 → ∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
      NodeBelow (run u t).store (.empty r) (run u t).head := by
    intro s
    induction s with
    | zero => intro _ u _ t _ ht; omega
    | succ s ih =>
      intro hs u hu t hlo ht
      by_cases hts : t < s
      · exact ih (by omega) u hu t hlo hts
      · have hts' : t = s := by omega
        subst hts'
        exact (hstep t hlo (by omega) (ih (by omega)) u hu).1
  intro v hv t hlo ht
  exact hstep t hlo ht (hall t (by omega)) v hv

include hw in
/-- **Finalization on the EMPTY side.** At the end of the window, every honest store has
finalized `E₁` or later, on the EMPTY side of `r`, or a root collision exists. -/
theorem honestNodes_finalize_empty {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) :
    RootCollision ∨ ∀ v, honest v →
      E₁ ≤ (run v (finSlot E₁)).store.finalizedCheckpoint.epoch.toNat ∧
      OnEmptySide (run v (finSlot E₁)).store r
        (run v (finSlot E₁)).store.finalizedCheckpoint.root := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  right
  intro v hv
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have hwin := (heads_avoid_full_window hw hset).resolve_left hcol
  have ht : raceLo rb ≤ finSlot E₁ := by
    unfold raceLo finSlot
    have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    omega
  have ht' : finSlot E₁ ≤ finSlot E₁ := Nat.le_refl _
  have hq := hset.base v hv _ ht ht'
  obtain ⟨hI, -, ha, -, hft⟩ := hset.storeFacts hw hcol hv ht ht'
  -- The anchor epoch and `anchorK` are before `E₁`.
  have hKE : anchorK A < E₁ := by
    unfold anchorK
    have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < E₁ * slotsPerEpoch := by omega
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    omega
  -- The finalized epoch: the store received the last block of `E₁ + 3` in time.
  obtain ⟨hi, steps, st, vals, H, p, q, sb, vb, u, w, hs, hu, hstep, hlast, hep, hrecv⟩ :=
    hset.chain
  obtain ⟨es1, es2, hes, hslotA⟩ := hrecv v hv
  obtain ⟨sA, arr1, arr2, h1, h2, -⟩ := hq.trace.split hes
  obtain ⟨sB, a1, a2, hsingle, hrest, -⟩ :=
    h2.split (es1 := [TraceEvent.handler (.block sb)]) (es2 := es2) rfl
  have hinvA := hset.prefixInv hw hcol hv ht ht' hes h1
  obtain ⟨cs, hcs, hcur⟩ := hq.slot
  have hS : finSlot E₁ ≤ storeSlot (run v (finSlot E₁)).store := by
    rw [← getCurrentSlot_storeSlot hcur, hcs]
    exact Nat.le_refl _
  have hfE := honestStore_finalizes hset.seconds hset.slotPos hcb H hset.anchorFilled
    hset.anchorHeader hs hu hstep hlast hep hinvA hsingle.single_handler (hslotA arr1 sA h1)
    hrest hS
  refine ⟨hfE, ?_⟩
  -- The finalized checkpoint is justified on a chain of the store, past the base.
  generalize hf : (run v (finSlot E₁)).store.finalizedCheckpoint = f at hfE hft ⊢
  obtain ⟨k, steps', v', hrun, hpath, -, hfin, hsr⟩ := finalized_source hw (hf ▸ hI.fSource)
    (by rw [currentEpochOf_epochOf]; unfold anchorK at hKE; omega) hset.roots hset.cps hset.ord
    hset.sphr (hset.totals v hv _ ht ht')
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hjus :
      EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps' A regVals) (toCp f) := by
    rcases hfin with h | h
    · exact match h with
      | .one h _ _ _ => h
      | .two h _ _ _ _ _ => h
    · have := (hm.base _ h).1
      simp only [toCp] at this
      omega
  have hon : chainRoot A steps' f.epoch.toNat = f.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm.base x hx).2)
  have hblk : ∃ xb, FcMap.lookup (run v (finSlot E₁)).store.blocks f.root = some xb := by
    rcases chainRoot_block hpath hI.slot hset.anchorRoot hset.aligned (e := f.epoch.toNat)
        (by unfold anchorK at hKE; omega) (by unfold anchorK at hKE; omega) with h | ⟨b, hb, -⟩
    · exact ⟨a, by rw [← hon, h]; exact ha⟩
    · exact ⟨b, hon ▸ hb⟩
  have hfE4 : f.epoch.toNat ≤ E₁ + 4 := by
    rw [finSlot, Nat.mul_div_cancel _ hp] at hft
    exact hft
  refine hset.target_empty hw hcol hv ht ht' hrun hpath hsr (x := toCp f) hjus
    (by simp only [toCp]; omega) (by simp only [toCp]; omega) (by
      simp only [toCp]
      have : E₁ * slotsPerEpoch ≤ f.epoch.toNat * slotsPerEpoch := Nat.mul_le_mul_right _ hfE
      omega) hblk (fun u hu t' hlo' hlt' => (hwin u hu t' hlo' (by omega)).1) ?_
  intro u hu t' hlo' hlt' hdiv e uu uu' he hck cb hcb'
  simp only [toCp] at hdiv he hck hcb'
  have hE1 : E₁ * slotsPerEpoch ≤ t' := by
    rw [← Nat.le_div_iff_mul_le hp, hdiv]
    exact hfE
  obtain ⟨cb', hcb'', hgt⟩ := hset.early u hu t' hE1 hlt' e f.root uu uu' (by omega) hck
  rw [hcb'] at hcb''
  cases hcb''
  exact hgt

include hw in
/-- **The censored payload is final.** Every honest head of the window avoids `full r`. A later
store of an honest node extends the store of the end of the window, and it meets the totals
premise (`StoreTotals`). Its head avoids `full r`, or there is slashing evidence, or two
blocks, headers or attestation data share a root. -/
theorem censored_payload_final {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) :
    RootCollision ∨ HtrCollision AttestationData ∨
      ((∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
          ¬ NodeBelow (run v t).store (.full r) (run v t).head) ∧
        ∀ v, honest v → ∀ (es : List TraceEvent) (arr : List (SignedInclusionList × UInt64))
          (s' : Store map), NodeTrace (run v (finSlot E₁)).store es arr s' →
          (∀ e, TraceEvent.handler e ∈ es → e.NotAtAnchorParent a) →
          (∀ sb, TraceEvent.handler (.block sb) ∈ es →
            sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) →
          (∀ k₁ bs₁ k₂ bs₂, AncestorPath a (run v (finSlot E₁)).store k₁ bs₁ →
            AncestorPath a s' k₂ bs₂ →
            bs₁.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch) =
              bs₂.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch)) →
          StoreTotals A a s' →
          ∀ (runner t : Store map) (head : ForkChoiceNode),
          (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s').run runner
            = .ok (head, t) →
          ¬ NodeBelow s' (.full r) head ∨
          ∃ (st₀ : BeaconState) (p₁ r₁ p₂ r₂ : List ChainStep)
            (pairs : List (IndexedAttestation × IndexedAttestation)),
            ChainRun (2 ^ 64 - 1) p₁ A st₀ ∧ ChainRun (2 ^ 64 - 1) p₂ A st₀ ∧
            SlashingEvidence st₀ (OnRun (2 ^ 64 - 1) A (p₁ ++ r₁))
              (OnRun (2 ^ 64 - 1) A (p₂ ++ r₂))
              (runDrift (2 ^ 64 - 1) st₀ r₁) (runDrift (2 ^ 64 - 1) st₀ r₂) pairs) := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  by_cases hac : HtrCollision AttestationData
  · exact Or.inr (Or.inl hac)
  refine Or.inr (Or.inr ⟨fun v hv t h1 h2 =>
    ((heads_avoid_full_window hw hset).resolve_left hcol v hv t h1 h2).2, ?_⟩)
  intro v hv es arr s' h2 hev hsr hbase htot' runner t head hhead
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have ht : raceLo rb ≤ finSlot E₁ := by
    unfold raceLo finSlot
    have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    omega
  have ht' : finSlot E₁ ≤ finSlot E₁ := Nat.le_refl _
  have hn := hset.fields.nodeOk v hv
  have hq := hset.base v hv _ ht ht'
  have ha := hset.anchorBlock v hv
  have hself : a.parentRoot ≠ htr a := ha ▸ hn.anchorSelf
  have haslot : a.slot ≤ rb.slot := ha ▸ hn.anchorSlot
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv ht ht'
  obtain ⟨hfE, hside⟩ := (honestNodes_finalize_empty hw hset).resolve_left hcol v hv
  -- The events of the prefix and of the later trace.
  have hevP : ∀ e, TraceEvent.handler e ∈ (run v (finSlot E₁)).events.map Prod.fst →
      e.NotAtAnchorParent a := fun e he => by
    obtain ⟨w, hw'⟩ := hset.mem_events hv ht ht' he
    exact ha ▸ hn.noAnchorParent e w hw'
  have hsrP : ∀ sb, TraceEvent.handler (.block sb) ∈ (run v (finSlot E₁)).events.map Prod.fst →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot := fun sb he => by
    obtain ⟨w, hw'⟩ := hset.mem_events hv ht ht' he
    exact hset.stateRoots v hv sb w hw'
  have hevAll : ∀ e, TraceEvent.handler e ∈ (run v (finSlot E₁)).events.map Prod.fst ++ es →
      e.NotAtAnchorParent a := fun e he => by
    rcases List.mem_append.mp he with he | he
    · exact hevP e he
    · exact hev e he
  have hsrAll : ∀ sb, TraceEvent.handler (.block sb) ∈
      (run v (finSlot E₁)).events.map Prod.fst ++ es →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot := fun sb he => by
    rcases List.mem_append.mp he with he | he
    · exact hsrP sb he
    · exact hsr sb he
  -- The finality lock.
  rcases honestNode_finality_lock hw (hset.anchorStore hv) hself hq.trace h2 hevAll r rb hq.block
      haslot hside runner t head hhead with hrc | hconf | hnot
  · exact absurd hrc hcol
  · right
    have hW := hq.trace.append h2
    have hI' := (NodeTrace.ckptInv hw hW (CkptInv.anchor A a _ (hset.anchorStore hv) hself)
      hset.ord hevAll hsrAll).resolve_right hcol
    have hgrow := h2.ckptGrows hI.slot.statesPure
    have hep : (run v (finSlot E₁)).store.finalizedCheckpoint.epoch ≤
        s'.justifiedCheckpoint.epoch :=
      UInt64.le_trans hgrow.2.1 hI'.ord
    have hfX : max (epochOf A + 2) 3 ≤
        (run v (finSlot E₁)).store.finalizedCheckpoint.epoch.toNat := by
      have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < E₁ * slotsPerEpoch := by omega
      have h2 := Nat.lt_of_mul_lt_mul_right h1
      omega
    rcases honestNodes_accountable hw hset.fields.sort (hset.anchorStore hv) hself hW hq.trace
        hevAll hevP hsrAll hsrP hset.anchorRoot hset.ord hset.roots hset.cps hset.sphr
        htot' (hset.totals v hv _ ht ht') hconf hep hfX hbase with hrc | hac' | hev'
    · exact absurd hrc hcol
    · exact absurd hac' hac
    · exact hev'
  · exact Or.inl hnot

end Main

end EthCLSpecs.Proofs.Heze
