import EthCLSpecs.Proofs.Heze.TipCheckpoint

/-!
# `EthCLSpecs.Proofs.Heze.VoteStep`: each honest vote of the window is on the EMPTY side

The window induction (`heads_avoid_full_upto`) carries `VotesEmpty`: every honest vote of the
window comes from a head below `empty r` or at `pending r`. This module proves the step
(`VoteStep`) from `FinalitySetting` and the carrier chain `H`. It shows more: every honest head of
the window lies below EMPTY `r` (`CarrierWindow.head_window`).

With a justified block past `rb`, the head lies below it, on the EMPTY side. With a justified
block no later than `rb`, `FinalitySetting.settingAt` puts the head strictly below `pending r`.
It needs a node strictly below `pending r` that the walk of the viable node tree keeps. That node
lies below the tip `T` of `H`, the last block of `H` before the epoch of the slot. The walk keeps
it for two reasons:

- The state of `T` carries the honest votes of the epoch before, with two thirds of the stake
  (`included`). So each leaf below `T` has a recent voting source (`leaf_vs_store`).
- Each leaf passes the finalized test (`FinalitySetting.finRead_early`,
  `CarrierWindow.finRead_late`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState pureState_inj LawfulFcMap run_bind_eq_ok
  run_pure_eq_ok run_get_bind_eq_ok run_assert_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex ExecutionPayload Transaction ExecutionRequests Epoch Slot AttestationData
  SignedBeaconBlock getCheckpointBlock currentEpochOf previousEpochOf isPayloadVerified)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section StateRun
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- A state transition starts before the slot of its block: `process_slots` asserts it
(`phase0/beacon-chain.md`, `process_slots`). -/
theorem stateTransition_slot_lt {sb : SignedBeaconBlock} {pv w : BeaconState}
    (ht : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
      = .ok ((), pureState w)) :
    pv.slot.toNat < sb.message.slot.toNat := by
  obtain ⟨mid, hslots, -⟩ := stateTransition_split ht
  unfold EthCLSpecs.Heze.processSlots at hslots
  have h := run_get_bind_eq_ok _ _ _ hslots
  obtain ⟨hlt, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact UInt64.lt_iff_toNat_lt.mp hlt

/-- **Every block of an ancestor path comes after the anchor state.** The block is not the
anchor, so its parent state is the end of a run from the anchor state (`CkptInv.chains`), and
the transition of the block starts before the block's slot (`stateTransition_slot_lt`). -/
theorem AncestorPath.slot_gt_anchorState {store : Store map} {A : BeaconState} {a : BeaconBlock}
    (hI : CkptInv A a store) (hlink : StateLink (htr a) store)
    (ha : FcMap.lookup store.blocks (htr a) = some a) {k : Root} {L : List BeaconBlock}
    (h : AncestorPath a store k L) : ∀ b ∈ L, A.slot.toNat < b.slot.toNat := by
  induction h with
  | anchor => intro b hb; simp at hb
  | @cons k' b bs hk hba _ ih =>
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ih y hy
    · have hyb : y = b := List.mem_singleton.mp hy
      subst hyb
      have hka : k' ≠ htr a := fun hka => by
        rw [hka, ha] at hk
        exact hba (Option.some.inj hk).symm
      obtain ⟨sb, pv, w, hsb, hpv, -, ht⟩ := hlink k' y hk hka
      obtain ⟨steps, hrun, -⟩ := hI.chains _ pv hpv
      have h1 := (hrun.slot_le (Nat.le_refl _)).1
      have h2 := stateTransition_slot_lt ht
      rw [hsb] at h2
      omega

end StateRun

section Placed
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
  {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
  {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}

include hw in
/-- **The carrier chain places the honest vote of each epoch.** Take an honest validator `i`
and an epoch `e` from the epoch of `rb` to `E₁ + 2`. The state `W` of `H` that weighs `e + 1`
holds a placed vote of every honest validator of the target test of `e` (`included`), and `i`
is one of them (`active`, `unslashedH`). That vote sets the target flag of `i` for `e`, so a
placed vote of the prefix of `H` to `W` set it (`ChainRun.flag_located`). Its target is the
checkpoint of the prefix at `e` (`RunVote.target_eq`). -/
theorem CarrierWindow.placed
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    {i : ValidatorIndex} (hhon : honestOf i = true) {e : Epoch}
    (hre : rb.slot.toNat / slotsPerEpoch ≤ e.toNat) (he3 : e.toNat ≤ E₁ + 2) :
    ∃ (w₁ w₂ : List ChainStep) (W : BeaconState) (d₂ : AttestationData),
      stepsH = w₁ ++ .slot :: w₂ ∧ ChainRun hi w₁ A W ∧
      W.slot.toNat / slotsPerEpoch = e.toNat + 1 ∧ RunVote hi A w₁ i d₂ ∧
      d₂.target.epoch = e ∧ toCp d₂.target = cpOf A w₁ e.toNat := by
  have hp := slotsPerEpochPos
  have hhi := hH.hhi
  have hlate := hset.late
  -- The anchor epoch is at least two epochs before `rb`.
  have hAe : epochOf A + 1 < e.toNat := by
    have h1 : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
    have h2 : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr h1
    omega
  -- The weigh state of `e + 1` on `H`.
  have hends := hH.ends
  have hAs : A.slot.toNat < (epochOf A + 1) * slotsPerEpoch := by
    unfold epochOf
    have := Nat.lt_div_mul_add (a := A.slot.toNat) hp
    rw [Nat.add_one_mul]
    omega
  obtain ⟨W, hW⟩ := hH.chainRun.weighAt_of_cross hhi (e.toNat + 1)
    (by
      have : (epochOf A + 1) * slotsPerEpoch ≤ (e.toNat + 1 + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      have : slotsPerEpoch ≤ (epochOf A + 1) * slotsPerEpoch :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega)
    (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hends)
  have hW0 := hW
  obtain ⟨hinc, -⟩ := hH.included (e.toNat + 1) (by omega) (by omega) W hW
  obtain ⟨w₁, w₂, hws, hrW, -, heW⟩ := hW
  -- The voter is active and not slashed at `W`, so it is in the honest list of `e`.
  obtain ⟨hlt, hactW⟩ := hH.active w₁ (.slot :: w₂) W hws hrW i hhon e (by omega) (by omega)
  have hprev : previousEpochOf (pureState W) = e := by
    apply UInt64.toNat_inj.mp
    rw [previousEpochOf_toNat_sub, heW]
    omega
  have hsl : (W.validators.val[i.toNat]!).slashed = false := by
    have := hH.unslashedH w₁ (.slot :: w₂) W hws hrW i.toNat hlt
      (by rw [UInt64.ofNat_toNat]; exact hhon)
    exact this
  have hiH : i ∈ honestList W honestOf (previousEpochOf (pureState W)) := by
    rw [hprev]
    exact mem_honestList_of hlt hhon hactW hsl
  -- The placed vote sets the flag, and a placed vote of the prefix set it.
  have hpv := hinc i hiH
  rw [hprev] at hpv
  have hflag := hpv.flag_at_weigh hhi hW0
  rcases hrW.flag_located (p := []) (.nil A) i.toNat e hflag with hA0 | ⟨d₂, hd₂e, hv₂⟩
  · -- The anchor state carries no flag of `e`, which is past its epoch.
    have hcA := currentEpochOf_epochOf A
    have hpA := previousEpochOf_epochOf A
    rcases hA0.epoch_cases with h | h
    · rw [h] at hAe
      omega
    · rw [h] at hAe
      omega
  rw [List.nil_append, UInt64.ofNat_toNat] at hv₂
  have hvalW : ValidatedSteps w₁ := fun sb v hm => hH.val sb v (by
    rw [hws]; exact List.mem_append_left _ hm)
  have htgt := hv₂.target_eq hw hhi hvalW hset.roots hrW (by rw [hd₂e]; omega)
  rw [hd₂e] at htgt
  exact ⟨w₁, w₂, W, d₂, hws, hrW, heW, hv₂, hd₂e, htgt⟩

include hw in
/-- **The target of an honest vote is the checkpoint of the carrier chain.** For an honest vote
`d` of an epoch from the epoch of `rb` to `E₁ + 2`, the carrier chain places a vote of the same
validator and target epoch (`CarrierWindow.placed`), which is `d` (`CarrierWindow.single`). Its
target is the checkpoint of a prefix of `H` at the epoch. -/
theorem CarrierWindow.vote_target
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    {i : ValidatorIndex} (hhon : honestOf i = true) {d : AttestationData}
    (hd : HonestVoteOf honest node run rb A a E₁ i d)
    (hre : rb.slot.toNat / slotsPerEpoch ≤ d.target.epoch.toNat)
    (he3 : d.target.epoch.toNat ≤ E₁ + 2) :
    ∃ (w₁ w₂ : List ChainStep) (W : BeaconState), stepsH = w₁ ++ .slot :: w₂ ∧
      ChainRun hi w₁ A W ∧ W.slot.toNat / slotsPerEpoch = d.target.epoch.toNat + 1 ∧
      toCp d.target = cpOf A w₁ d.target.epoch.toNat := by
  obtain ⟨w₁, w₂, W, d₂, hws, hrW, heW, hv₂, hd₂e, htgt⟩ := hH.placed hw hset hhon hre he3
  have he := hH.single i hhon d hd w₁ (.slot :: w₂) d₂ hws hv₂ hd₂e
  subst he
  exact ⟨w₁, w₂, W, hws, hrW, heW, htgt⟩

include hw in
/-- **The tip `T` in the store of an honest head run of the epoch of `rb`.** `T` is the block of
`CarrierWindow.tipChain` for the epoch `E` of `rb`: the last block of `H` up to the end of
`E - 1`, so it comes before `rb`. The store holds `rb` with its ancestor path, which is the
prefix of `H` to `rb` (`CarrierWindow.tipState`). `T` is a block of that prefix, so the store
holds it, and its pending node lies above `pending r` (`AncestorPath.pendingBelow`). -/
theorem CarrierWindow.tipBefore
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hE : s / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch) :
    ∃ (T : Root) (tb : BeaconBlock) (sT : BeaconState) (preT : List ChainStep),
      FcMap.lookup (run v s).store.blocks T = some tb ∧ T ≠ htr a ∧
      FcMap.lookup (run v s).store.blockStates T = some (pureState sT) ∧
      ChainRun (2 ^ 64 - 1) preT A sT ∧ AncestorPath a (run v s).store T (blocksOf preT) ∧
      ValidatedSteps preT ∧ EndsAtBlock preT ∧
      sT.slot.toNat = tb.slot.toNat ∧ tb.slot.toNat < rb.slot.toNat ∧
      sT.slot.toNat / slotsPerEpoch + 1 = s / slotsPerEpoch ∧
      NodeBelow (run v s).store (.pending T) (.pending r) ∧
      (∀ j < sT.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (sT.validators.val[j]!).slashed = false) ∧
      CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState sT)) (pureState sT) ∧
      CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState sT)) (pureState sT) ∧
      (∀ x ∈ honestList sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)),
        TargetFlagSet sT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState sT))) ∧
      3 * honestStake sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)) ≥
        2 * (totBal sT).toNat := by
  have hp := slotsPerEpochPos
  have hq := hset.held v hv s hlo hs
  obtain ⟨hI, -, ha, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hslot := hI.slot
  have hlate := hset.late
  have hhi := hH.hhi
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hE2 : rb.slot.toNat / slotsPerEpoch ≤ E₁ + 4 := by
    have := (Nat.div_lt_iff_lt_mul hp).mpr hset.before
    omega
  obtain ⟨p, sbT, vbT, q, s₂, wT, W, hsH, hX, hY, hq0, -, -, hwT, hTlo, hThi, -, -, hus, hw₀,
    hw₁, hflags, hstake⟩ := hH.tipChain hlA (Nat.le_refl _) hE2
  have hrS : rb.slot.toNat / slotsPerEpoch * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.div_mul_le_self _ _
  have hTr : sbT.message.slot.toNat < rb.slot.toNat := by omega
  have hrbr : htr rb = r := hslot.atRoot r rb hq.block
  -- The anchor block is two epochs before `rb`.
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hA2 : epochOf A * slotsPerEpoch < (epochOf A + 2) * slotsPerEpoch :=
    Nat.mul_lt_mul_of_pos_right (by omega) hp
  -- The prefix of `H` to `rb` and the ancestor path of `rb` in the store.
  have hrunH := hH.chainRun
  rw [hH.split] at hrunH
  obtain ⟨u₀, hR1, hR2⟩ := hrunH.split
  obtain ⟨wR, hRb⟩ : ∃ wR, BlockStep sbR vbR u₀ wR := by
    cases hR2 with
    | block _ _ hb' _ => exact ⟨_, hb'⟩
  have hXR : ChainRun hi (aR ++ [.block sbR vbR]) A wR := hR1.append (.block sbR vbR hRb (.nil _))
  have hwR : wR.slot.toNat = sbR.message.slot.toNat := by
    obtain ⟨e1, e2⟩ := hRb.slot
    omega
  have hRk : FcMap.lookup (run v s).store.blocks (htr sbR.message) = some sbR.message := by
    rw [hH.isRb, hrbr]
    exact hq.block
  have hRa : htr sbR.message ≠ htr a := fun h => by
    rw [h, ha, hH.isRb] at hRk
    cases hRk
    omega
  obtain ⟨preR, -, -, hpathR, -, -, hblR⟩ :=
    hH.tipState hw hset hcol hv hlo hs hH.split hXR hwR hRk hRa
  rw [hH.isRb] at hblR hpathR
  rw [hrbr] at hpathR
  -- `T` is a block of the prefix to `rb`.
  have hstr := hH.chainRun.blocks_strict
  have hTH : sbT.message ∈ blocksOf stepsH := by
    rw [hsH]
    exact mem_blocksOf_block _ _ _ _
  have hTa' : sbT.message ∈ blocksOf aR := by
    rw [hH.split, blocksOf_append] at hTH hstr
    rcases List.mem_append.mp hTH with h | h
    · exact h
    · exfalso
      rw [← hH.isRb] at hTr
      simp only [blocksOf] at h hstr
      rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hTr
        omega
      · have := (List.pairwise_cons.mp (List.pairwise_append.mp hstr).2.1).1 _ h'
        omega
  obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hTa'
  have hLR : blocksOf preR = L₁ ++ sbT.message :: (L₂ ++ [rb]) := by
    rw [hblR, hL]
    simp
  have hpre := hpathR.prefix hslot (L₁ ++ [sbT.message]) (L₂ ++ [rb]) (by rw [hLR]; simp)
  rw [lastRootOf_snoc] at hpre
  have hTk : FcMap.lookup (run v s).store.blocks (htr sbT.message) = some sbT.message := by
    rcases hpre.inv with h0 | ⟨bs, b, hbs', hkc, -⟩
    · simp at h0
    · obtain ⟨-, hbb⟩ := List.append_inj' hbs' rfl
      rw [List.singleton_inj] at hbb
      rw [← hbb] at hkc
      exact hkc
  have hbelow : NodeBelow (run v s).store (.pending (htr sbT.message)) (.pending r) :=
    hpathR.pendingBelow hslot L₁ (L₂ ++ [rb]) hLR
  have hTa : htr sbT.message ≠ htr a := fun h => by
    rw [h, ha] at hTk
    have hat : a.slot.toNat = sbT.message.slot.toNat := by rw [Option.some.inj hTk]
    -- `T` is from the epoch before `rb`, at least one epoch after the anchor epoch.
    have h1 : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
    have h2 : (epochOf A + 1) * slotsPerEpoch ≤ (rb.slot.toNat / slotsPerEpoch - 1) *
        slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    have h3 : epochOf A * slotsPerEpoch < (epochOf A + 1) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    omega
  obtain ⟨preT, hw', hrunT, hpathT, hvalT, hendT, -⟩ :=
    hH.tipState hw hset hcol hv hlo hs (rest := q ++ .slot :: s₂) hsH hX hwT hTk hTa
  refine ⟨htr sbT.message, sbT.message, wT, preT, hTk, hTa, hw', hrunT, hpathT, hvalT, hendT,
    hwT, hTr, ?_, hbelow, hus, hw₀, hw₁, hflags, hstake⟩
  rw [hwT, hE]
  have h1 : rb.slot.toNat / slotsPerEpoch - 1 ≤ sbT.message.slot.toNat / slotsPerEpoch :=
    (Nat.le_div_iff_mul_le hp).mpr hTlo
  have h2 : sbT.message.slot.toNat / slotsPerEpoch < rb.slot.toNat / slotsPerEpoch :=
    (Nat.div_lt_iff_lt_mul hp).mpr hThi
  omega

include hw in
/-- **The finalized test passes below `r` when the finalized epoch starts before `rb`.** The
checkpoint block of a node `d` below `pending r` at the finalized epoch is the one of `r`
(`cb_below_eq`): the blocks below `r` come after `rb`. Past the anchor epoch, that block is the
finalized root (`FinalitySetting.fin_cb_r`). At the anchor checkpoint it is the anchor root:
every block of the path of `r` comes after the anchor state
(`AncestorPath.slot_gt_anchorState`), so after the first slot of the anchor epoch. -/
theorem FinalitySetting.finRead_early
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    {S : Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch (run v s).store.finalizedCheckpoint.epoch :
      Except StateTransitionError Slot) = .ok S)
    (hSv : S.toNat = (run v s).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch)
    (hSr : S < rb.slot) {d : ForkChoiceNode} (hdr : NodeBelow (run v s).store (.pending r) d)
    (u : Store map) : (finRead (run v s).store d.root).run u = .ok (true, u) := by
  have hp := slotsPerEpochPos
  have hq := hset.held v hv s hlo hs
  have hn := hset.fields.nodeOk v hv
  obtain ⟨hI, hAbove, ha, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hslot := hI.slot
  have hslots := hslot.slots
  have hord : StateCkptOrd (node v).anchorState := by rw [hset.anchorState v hv]; exact hset.ord
  obtain ⟨-, -, -, hlink, -⟩ := hq.viableInvs hw hcol hn hord (hset.stateRoots v hv)
  rw [hset.anchorBlock v hv] at hlink
  have hlate := hset.late
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hrb := hq.block
  have hr0 : r ≠ htr a := fun h => by
    rw [h, ha] at hrb
    have har : a.slot.toNat = rb.slot.toNat := by rw [Option.some.inj hrb]
    have h1 : epochOf A * slotsPerEpoch < (epochOf A + 2) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    have h2 := Nat.le_trans (Nat.mul_le_mul_right slotsPerEpoch (Nat.le_max_left _ 3)) hlate
    omega
  -- The checkpoint block of `r` at the finalized epoch is the finalized root.
  have hFr : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (run v s).store r (run v s).store.finalizedCheckpoint.epoch).run u =
      .ok ((run v s).store.finalizedCheckpoint.root, u) := by
    by_cases hFA : epochOf A < (run v s).store.finalizedCheckpoint.epoch.toNat
    · exact hset.fin_cb_r hw hcol hv hlo hs hV hFA hS hSr u
    · have hFa : (run v s).store.finalizedCheckpoint =
          { epoch := EthCLSpecs.Heze.currentEpochOf (pureState A), root := htr a } := by
        rcases hAbove.2.1 with h | h
        · exact h
        · exact absurd h hFA
      obtain ⟨-, -, wr, -, -, hwr, -⟩ := hlink r rb hrb hr0
      obtain ⟨preR, -, hpathR, -⟩ := hI.chains r wr hwr
      have hfit : (run v s).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
        rw [← hSv]; exact S.toNat_lt
      have hFe : (run v s).store.finalizedCheckpoint.epoch.toNat = epochOf A := by
        rw [hFa]; exact currentEpochOf_epochOf A
      have hSe : ((run v s).store.finalizedCheckpoint.epoch * UInt64.ofNat slotsPerEpoch).toNat =
          (run v s).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch := by
        have hn' : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
          UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
        rw [UInt64.toNat_mul, hn', Nat.mod_eq_of_lt hfit]
      have haE : a.slot ≤ (run v s).store.finalizedCheckpoint.epoch * UInt64.ofNat slotsPerEpoch := by
        rw [UInt64.le_iff_toNat_le, hSe, hFe]
        exact haS
      rw [hpathR.checkpointBlock hslot ha hfit haE u]
      have hnil : (blocksOf preR).filter (fun b =>
          b.slot ≤ (run v s).store.finalizedCheckpoint.epoch * UInt64.ofNat slotsPerEpoch) = [] := by
        refine List.filter_eq_nil_iff.mpr fun b hb => ?_
        have hgt := hpathR.slot_gt_anchorState hI hlink ha b hb
        have hAe : epochOf A * slotsPerEpoch ≤ A.slot.toNat := Nat.div_mul_le_self _ _
        simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hSe, hFe]
        omega
      rw [hnil, hFa]
      rfl
  have hcbd := cb_below_eq _ hslots hrb _ S hS hdr fun y hy _ hne => by
    obtain ⟨yb, hyb, hgt⟩ := below_slot_gt _ hslots hrb hy hne
    exact ⟨yb, hyb, UInt64.lt_trans hSr hgt⟩
  unfold finRead
  rw [StateT.run_map, hcbd u, hFr]
  simp [Functor.map, Except.map]

include hw in
/-- **The finalized test passes below the carrier tip when the finalized epoch starts at or
after `rb`.** Take an honest head run of a slot `s` after the epoch of `rb`, and the tip `T` of
`H` for the epoch of `s` (`CarrierWindow.tipStore`). The finalized checkpoint `F` is past the
anchor epoch, so an honest vote targets it (`finalized_source`, `justified_voter`). The epoch of
`F` is from the epoch of `rb` to `E₁ + 2` (`FinalitySetting.finLag`). So the target of that vote
is the checkpoint of `H` at that epoch (`CarrierWindow.vote_target`). The checkpoint block of a
node below `pending T` is the checkpoint block of `T` (`cb_below_eq`). That block is the same
checkpoint of `H` (`tip_cb_eq_chainRoot`), because the blocks of `H` after `T`, and after the
weigh state of the vote, come after the first slot of the epoch of `F`. -/
theorem CarrierWindow.finRead_late
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    {T : Root} {tb : BeaconBlock} {sT : BeaconState} {preT : List ChainStep}
    (hTk : FcMap.lookup (run v s).store.blocks T = some tb) (hTa : T ≠ htr a)
    (hpathT : AncestorPath a (run v s).store T (blocksOf preT))
    (hsTb : sT.slot.toNat = tb.slot.toNat)
    (hsTE : sT.slot.toNat / slotsPerEpoch + 1 = s / slotsPerEpoch)
    (hpre : ∃ pT rest, stepsH = pT ++ rest ∧ blocksOf preT = blocksOf pT)
    {S : Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch (run v s).store.finalizedCheckpoint.epoch :
      Except StateTransitionError Slot) = .ok S)
    (hSv : S.toNat = (run v s).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch)
    (hSr : ¬ S < rb.slot) {d : ForkChoiceNode} (hTd : NodeBelow (run v s).store (.pending T) d)
    (u : Store map) : (finRead (run v s).store d.root).run u = .ok (true, u) := by
  have hp := slotsPerEpochPos
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hhi := hH.hhi
  have hq := hset.held v hv s hlo hs
  obtain ⟨hI, -, ha, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hslot := hI.slot
  have hslots := hslot.slots
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have hSr' : rb.slot.toNat ≤ S.toNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hSr)
  generalize hF : (run v s).store.finalizedCheckpoint = F at hS hSv hSr' ⊢
  -- `F` is past the anchor epoch, and two epochs before the epoch of `s`.
  have hrF : rb.slot.toNat / slotsPerEpoch ≤ F.epoch.toNat :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm, ← hSv]; exact hSr')
  have hFA : epochOf A < F.epoch.toNat := by omega
  have hlag : F.epoch.toNat + 2 ≤ s / slotsPerEpoch := by
    rcases hset.finLag hw hcol hv hlo hs with h | h
    · rw [hF] at h; omega
    · rw [hF] at h; exact h
  have hE2 : s / slotsPerEpoch ≤ E₁ + 4 := by
    have : s / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right hs
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    exact this
  -- An honest vote targets `F`, and its target is the checkpoint of `H`.
  obtain ⟨k, steps, v', hrun, hpath, hfv, h2, hfin, hsr⟩ := finalized_source hw
    (hF ▸ hI.fSource) (by rw [currentEpochOf_epochOf]; exact hFA) hset.roots hset.cps hset.ord
    hset.sphr (hset.totals v hv s hlo hs)
  obtain ⟨-, -, -, -, hval, -⟩ := id hsr
  have hjus : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) (toCp F) := by
    rcases hfin with hf | hb
    · cases hf with
      | one hb _ _ _ => exact hb
      | two hb _ _ _ _ _ => exact hb
    · exact .base hb
  obtain ⟨i, d₀, hhon, hvote, hd₀⟩ := justified_voter hw hrun hval hset.roots hset.cps hset.ord
    honestOf (B := E₁ + 5)
    (fun p q u hpq hu => hset.totals v hv s hlo hs p q u (hpq ▸ hsr) hu)
    (fun p q u hpq hu hB => hset.allChains v hv s hlo hs p q u (hpq ▸ hsr) hu hB)
    hjus (by simp only [toCp]; exact hFA) (by simp only [toCp]; exact hfv) h2
    (by simp only [toCp]; omega)
  have hde : d₀.target.epoch.toNat = F.epoch.toNat := congrArg (·.epoch) hd₀
  have hdr : d₀.target.root = F.root := congrArg (·.root) hd₀
  have hvo : HonestVoteOf honest node run rb A a E₁ i d₀ :=
    ⟨v, hv, s, hlo, hs, .inr ⟨steps, hsr, hvote⟩⟩
  obtain ⟨w₁, w₂, W, hws, hrW, heW, htgt⟩ := hH.vote_target hw hset hhon hvo (by omega) (by omega)
  have hroot : F.root = chainRoot A w₁ F.epoch.toNat := by
    rw [← hdr, ← hde]
    exact congrArg (·.root) htgt
  -- The blocks of `H` after `W` come from the epoch after `F` on.
  have hw₂ : ∀ b ∈ blocksOf (.slot :: w₂), F.epoch.toNat * slotsPerEpoch < b.slot.toNat := by
    intro b hb
    have hrunH := hH.chainRun
    rw [hws] at hrunH
    obtain ⟨m, hm1, hm2⟩ := hrunH.split
    rw [← hrW.det hm1] at hm2
    have h1 := hm2.blocks_slot_ge hhi b hb
    have h2 : (F.epoch.toNat + 1) * slotsPerEpoch ≤ W.slot.toNat := by
      rw [← hde, ← heW]
      exact Nat.div_mul_le_self _ _
    rw [Nat.add_one_mul] at h2
    omega
  -- The blocks of `H` after the tip come after it.
  obtain ⟨pT, rest, hsH, hbl⟩ := hpre
  have hTlast : ∃ bs, blocksOf preT = bs ++ [tb] := by
    rcases hpathT.inv with h0 | ⟨bs, b, hbs, hk, -⟩
    · exfalso
      have hk1 := (hpathT.linked hslot).2
      rw [h0] at hk1
      exact hTa hk1
    · rw [hTk] at hk
      cases hk
      exact ⟨bs, hbs⟩
  obtain ⟨bs, hbs⟩ := hTlast
  have hrest : ∀ b ∈ blocksOf rest, F.epoch.toNat * slotsPerEpoch < b.slot.toNat := by
    intro b hb
    have hstr := hH.chainRun.blocks_strict
    rw [hsH, blocksOf_append, ← hbl, hbs, List.pairwise_append] at hstr
    have h1 := hstr.2.2 tb (by simp) b hb
    have h2 : (s / slotsPerEpoch - 1) * slotsPerEpoch ≤ tb.slot.toNat := by
      rw [← hsTb]
      have := Nat.div_mul_le_self sT.slot.toNat slotsPerEpoch
      have e : s / slotsPerEpoch - 1 = sT.slot.toNat / slotsPerEpoch := by omega
      rw [e]
      exact this
    have h3 : F.epoch.toNat * slotsPerEpoch < (s / slotsPerEpoch - 1) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    omega
  -- The checkpoint block of `T` is the checkpoint of `H`.
  have hfit : F.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by rw [← hSv]; exact S.toNat_lt
  have hSe : (F.epoch * UInt64.ofNat slotsPerEpoch).toNat = F.epoch.toNat * slotsPerEpoch := by
    have hn' : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
      UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
    rw [UInt64.toNat_mul, hn', Nat.mod_eq_of_lt hfit]
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hAF : epochOf A * slotsPerEpoch ≤ F.epoch.toNat * slotsPerEpoch :=
    Nat.mul_le_mul_right _ (by omega)
  have haE : a.slot ≤ F.epoch * UInt64.ofNat slotsPerEpoch := by
    rw [UInt64.le_iff_toNat_le, hSe]
    omega
  have hcbT := tip_cb_eq_chainRoot hslot ha hfit haE hpathT hset.anchorRoot
    (by have := hset.aligned; omega) (by omega) hsH hbl hws hrest hw₂
  -- The checkpoint block of `d` is the one of `T`.
  have hTS : S < tb.slot := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hSv]
    have h2 : (s / slotsPerEpoch - 1) * slotsPerEpoch ≤ tb.slot.toNat := by
      rw [← hsTb]
      have e : s / slotsPerEpoch - 1 = sT.slot.toNat / slotsPerEpoch := by omega
      rw [e]
      exact Nat.div_mul_le_self _ _
    have h3 : F.epoch.toNat * slotsPerEpoch < (s / slotsPerEpoch - 1) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    omega
  have hcbd := cb_below_eq _ hslots hTk _ S (hF ▸ hS) hTd fun y hy _ hne => by
    obtain ⟨yb, hyb, hgt⟩ := below_slot_gt _ hslots hTk hy hne
    exact ⟨yb, hyb, UInt64.lt_trans hTS hgt⟩
  unfold finRead
  rw [StateT.run_map, hF, ← hF, hcbd u, hF, hcbT u, ← hroot]
  simp [Functor.map, Except.map]

include hw in
/-- **The walk keeps a node below a carrier tip.** Take an honest head run of a slot `s` of the
window. Take a stored block `T` of the epoch before the epoch of `s`, other than the anchor. Its
stored state `sT` is the one of `leaf_vs_store`: it holds the honest flags of the epoch before,
with two thirds of the stake. Take a node `m` strictly below `pending r` and below `pending T`,
with verified payloads at its FULL nodes. Each leaf below `m` has a recent voting source
(`leaf_vs_store`). Suppose that each leaf below `m` also passes the finalized test (`hfin`).
Then the walk of the viable node tree keeps `m` (`kept_of_leaves`). -/
theorem CarrierWindow.kept_of_tip
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) {T : Root} {tb : BeaconBlock} {sT : BeaconState}
    {preT : List ChainStep} (hTk : FcMap.lookup (run v s).store.blocks T = some tb)
    (hTa : T ≠ htr a) (hsT : FcMap.lookup (run v s).store.blockStates T = some (pureState sT))
    (hrunT : ChainRun (2 ^ 64 - 1) preT A sT)
    (hpathT : AncestorPath a (run v s).store T (blocksOf preT)) (hvalT : ValidatedSteps preT)
    (hendT : EndsAtBlock preT) (hsTb : sT.slot.toNat = tb.slot.toNat)
    (hsTE : sT.slot.toNat / slotsPerEpoch + 1 = s / slotsPerEpoch)
    (hus : ∀ j < sT.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (sT.validators.val[j]!).slashed = false)
    (hw₀ : CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState sT)) (pureState sT))
    (hw₁ : CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState sT)) (pureState sT))
    (hflags : ∀ x ∈ honestList sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)),
      TargetFlagSet sT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState sT)))
    (hstake : 3 * honestStake sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)) ≥
      2 * (totBal sT).toNat)
    {m : ForkChoiceNode} (hrm : NodeBelow (run v s).store (.pending r) m)
    (hmne : m ≠ .pending r) (hTm : NodeBelow (run v s).store (.pending T) m)
    (hver : ∀ z, NodeBelow (run v s).store
        (.pending (run v s).store.justifiedCheckpoint.root) (.full z) →
      NodeBelow (run v s).store (.full z) m → isPayloadVerified (run v s).store z = true)
    (hfin : ∀ d, NodeBelow (run v s).store m d → ∀ u,
      (finRead (run v s).store d.root).run u = .ok (true, u)) :
    KeptBelow (run v s).store r m := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hq := hset.held v hv s hlo hs
  have hn := hset.fields.nodeOk v hv
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hslot := hI.slot
  have hslots := hslot.slots
  have hord : StateCkptOrd (node v).anchorState := by rw [hset.anchorState v hv]; exact hset.ord
  obtain ⟨-, hunr, hkeys, hlink, -⟩ := hq.viableInvs hw hcol hn hord (hset.stateRoots v hv)
  rw [hset.anchorBlock v hv] at hunr hlink
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have h3 : 3 * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_right _ _)) hlate
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have hr3 : 3 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr h3
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hlt : rb.slot.toNat < s := by unfold raceLo at hlo; omega
  have hrs : rb.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := Nat.div_le_div_right (by omega)
  obtain ⟨E, hEn, hEr⟩ := hq.storeEpoch
  have hclock : ∀ k b, FcMap.lookup (run v s).store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat := fun k b hk => by
    rw [computeEpochAtSlot_toNat, hEn]
    exact Nat.div_le_div_right (hq.block_slot_le hn (hn.anchor_le_of_lt hlt) hk)
  have hzr := CkptInv.stateRoot_ne hI hlink
  have hna := below_not_anchor hslot hcb hTk (by
    apply UInt64.le_iff_toNat_le.mpr
    have h1 : (epochOf A + 1) * slotsPerEpoch ≤ sT.slot.toNat / slotsPerEpoch * slotsPerEpoch :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 := Nat.div_mul_le_self sT.slot.toNat slotsPerEpoch
    have h3 : epochOf A * slotsPerEpoch ≤ (epochOf A + 1) * slotsPerEpoch :=
      Nat.mul_le_mul_right _ (by omega)
    omega)
  have hET : E.toNat = sT.slot.toNat / slotsPerEpoch + 1 := by rw [hEn]; omega
  have hE2 : s / slotsPerEpoch ≤ E₁ + 4 := by
    have : s / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right hs
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    exact this
  have hroom : E.toNat + 2 < 2 ^ 64 := by have := hH.room; omega
  have h2 : 2 ≤ sT.slot.toNat / slotsPerEpoch := by omega
  have hall : ∀ p q z, StoreRun A a (run v s).store (p ++ q) → ChainRun (2 ^ 64 - 1) p A z →
      (∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (z.validators.val[j]!).slashed = false) ∧ RunTotals z := fun p q z hsr hz =>
    ⟨hH.unslashed v hv s hlo hs p q z hsr hz, hset.totals v hv s hlo hs p q z hsr hz⟩
  refine ⟨kept_of_leaves _ hslots m fun d hd u cs _ _ => ?_, hrm, hmne, hver⟩
  have hdT : NodeBelow (run v s).store (.pending T) d := NodeBelow.trans _ _ _ _ hTm hd
  obtain ⟨db, hdb⟩ := below_stored hdT hTk
  obtain ⟨vs, hvs, hge, hfit⟩ := leaf_vs_store hslot hlink hzr hunr hkeys hTa hsT hrunT hpathT
    hvalT hendT hdT hna hdb u (hEr u) hET (hclock _ _ hdb) hroom h2 hw₀ hw₁ hus hflags hstake hall
  exact leafOk_true_of _ d u (hEr u) hvs hfit hge (hfin d hd u)

include hw in
/-- **EMPTY `r` is kept in the epoch of `rb`.** The tip `T` of `H` for the epoch of `rb` lies
above `pending r` (`CarrierWindow.tipBefore`), so EMPTY `r` lies below it. The finalized epoch
starts before `rb`: it is the anchor epoch, or an epoch before the epoch of `rb`
(`HeadRun.Held.finalizedStart`). So each leaf below EMPTY `r` passes the finalized test
(`FinalitySetting.finRead_early`), and `CarrierWindow.kept_of_tip` keeps EMPTY `r`. -/
theorem CarrierWindow.kept_sameEpoch
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hE : s / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s) :
    KeptBelow (run v s).store r (.empty r) := by
  have hp := slotsPerEpochPos
  have hq := hset.held v hv s hlo hs
  have hn := hset.fields.nodeOk v hv
  have hA0 := hset.anchorState v hv
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hord : StateCkptOrd (node v).anchorState := by rw [hA0]; exact hset.ord
  obtain ⟨-, -, -, -, hfv⟩ := hq.viableInvs hw hcol hn hord (hset.stateRoots v hv)
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have hlt : rb.slot.toNat < s := by unfold raceLo at hlo; omega
  obtain ⟨cs, hcsn, -⟩ := hq.slot
  have hs64 : s < 2 ^ 64 := hcsn ▸ cs.toNat_lt
  have hAt : A.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := by
    unfold epochOf at hrA
    omega
  obtain ⟨T, tb, sT, preT, hTk, hTa, hsT, hrunT, hpathT, hvalT, hendT, hsTb, -, hsTE, hbelow,
    hus, hw₀, hw₁, hflags, hstake⟩ := hH.tipBefore hw hset hcol hv hlo hs hE
  obtain ⟨S, hS, hSv, hF⟩ := hq.finalizedStart hn (by rw [hA0, hset.anchorBlock v hv]; exact hI)
    hord hlt hs64 (by rw [hA0]; exact hAt)
  rw [hA0] at hF
  -- The finalized epoch starts before `rb`.
  have hSr : S < rb.slot := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hSv]
    have hrd := Nat.div_mul_le_self rb.slot.toNat slotsPerEpoch
    rcases hF with h | h
    · rw [h]
      unfold epochOf at hrA
      have := Nat.mul_le_mul_right slotsPerEpoch (show A.slot.toNat / slotsPerEpoch + 1 ≤
        rb.slot.toNat / slotsPerEpoch by omega)
      rw [Nat.add_one_mul] at this
      omega
    · rw [hE] at h
      have h2' := Nat.mul_le_mul_right slotsPerEpoch h
      rw [Nat.sub_one_mul] at h2'
      have h3' : slotsPerEpoch ≤ rb.slot.toNat / slotsPerEpoch * slotsPerEpoch :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  have hrE : NodeBelow (run v s).store (.pending r) (.empty r) := .step _ _ .refl (NodeEdge.empty r)
  exact hH.kept_of_tip hw hset hcol hv hlo hs hTk hTa hsT hrunT hpathT hvalT hendT hsTb hsTE hus
    hw₀ hw₁ hflags hstake hrE
    (fun h => payloadStatus_empty_ne_pending (congrArg ForkChoiceNode.payloadStatus h))
    (NodeBelow.trans _ _ _ _ hbelow hrE)
    (fun z _ hz => hfv.path z r (below_decided_pending hz payloadStatus_empty_ne_pending
      (fun h => payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h).symm)))
    (fun d hd u => hset.finRead_early hw hcol hv hlo hs hV hS hSv hSr
      (NodeBelow.trans _ _ _ _ hrE hd) u)

include hw in
/-- **The walk keeps a node strictly below `pending r` after the epoch of `rb`.** Take the tip
`T` of `H` for the epoch of `s` (`CarrierWindow.tipStore`). Either `T` is `rb`, and the node is
EMPTY `r` below it, or `T` is a block of `H` below EMPTY `r`, and the node is `pending T`. Each leaf
below that node passes the finalized test. `FinalitySetting.finRead_early` gives the test when
the finalized epoch starts before `rb`, and `CarrierWindow.finRead_late` gives it otherwise. So
`CarrierWindow.kept_of_tip` keeps the node. -/
theorem CarrierWindow.kept_later
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hE1 : rb.slot.toNat / slotsPerEpoch < s / slotsPerEpoch)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s) :
    ∃ m, KeptBelow (run v s).store r m := by
  have hp := slotsPerEpochPos
  have hq := hset.held v hv s hlo hs
  have hn := hset.fields.nodeOk v hv
  have hA0 := hset.anchorState v hv
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv hlo hs
  have hslots := hI.slot.slots
  have hord : StateCkptOrd (node v).anchorState := by rw [hA0]; exact hset.ord
  obtain ⟨-, -, -, -, hfv⟩ := hq.viableInvs hw hcol hn hord (hset.stateRoots v hv)
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have hlt : rb.slot.toNat < s := by unfold raceLo at hlo; omega
  obtain ⟨cs, hcsn, -⟩ := hq.slot
  have hs64 : s < 2 ^ 64 := hcsn ▸ cs.toNat_lt
  have hAt : A.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := by
    unfold epochOf at hrA
    omega
  obtain ⟨T, tb, sT, preT, hTk, hTa, hsT, hrunT, hpathT, hvalT, hendT, hsTb, -, hsTE, -,
    hpre, hTm, hus, hw₀, hw₁, hflags, hstake⟩ := hH.tipStore hw hset hcol hv hlo hs hE1
  obtain ⟨S, hS, hSv, -⟩ := hq.finalizedStart hn (by rw [hA0, hset.anchorBlock v hv]; exact hI)
    hord hlt hs64 (by rw [hA0]; exact hAt)
  have hrE : NodeBelow (run v s).store (.pending r) (.empty r) := .step _ _ .refl (NodeEdge.empty r)
  -- The finalized test below `pending T`.
  have hfinT : ∀ d, NodeBelow (run v s).store (.pending T) d →
      NodeBelow (run v s).store (.pending r) d → ∀ u,
      (finRead (run v s).store d.root).run u = .ok (true, u) := fun d hTd hrd u => by
    by_cases hSr : S < rb.slot
    · exact hset.finRead_early hw hcol hv hlo hs hV hS hSv hSr hrd u
    · exact hH.finRead_late hw hset hcol hv hlo hs hTk hTa hpathT hsTb hsTE hpre hS hSv hSr hTd u
  rcases hTm with hTr | ⟨hrbtb, hTbelow⟩
  · -- `T` is `rb`: EMPTY `r` is kept.
    subst hTr
    refine ⟨.empty T, hH.kept_of_tip hw hset hcol hv hlo hs hTk hTa hsT hrunT hpathT hvalT hendT
      hsTb hsTE hus hw₀ hw₁ hflags hstake hrE
      (fun h => payloadStatus_empty_ne_pending (congrArg ForkChoiceNode.payloadStatus h)) hrE
      (fun z _ hz => hfv.path z T (below_decided_pending hz payloadStatus_empty_ne_pending
        (fun h => payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h).symm)))
      fun d hd u => hfinT d (NodeBelow.trans _ _ _ _ hrE hd) (NodeBelow.trans _ _ _ _ hrE hd) u⟩
  · -- `T` is a block of `H` below EMPTY `r`: its pending node is kept.
    have hrT : NodeBelow (run v s).store (.pending r) (.pending T) :=
      NodeBelow.trans _ _ _ _ hrE hTbelow
    have hTne : (ForkChoiceNode.pending T) ≠ .pending r := fun h => by
      have hTr : T = r := congrArg ForkChoiceNode.root h
      rw [hTr, hq.block] at hTk
      rw [Option.some.inj hTk] at hrbtb
      omega
    exact ⟨.pending T, hH.kept_of_tip hw hset hcol hv hlo hs hTk hTa hsT hrunT hpathT hvalT hendT
      hsTb hsTE hus hw₀ hw₁ hflags hstake hrT hTne .refl (fun z _ h => hfv.path z T h)
      fun d hd u => hfinT d hd (NodeBelow.trans _ _ _ _ hrT hd) u⟩

include hw in
/-- **Every honest head of the window is on the EMPTY side.** Take an honest head run of a slot
`s` of the window, after the honest votes before `s` are on the EMPTY side and no honest head up
to `s` is at or below FULL `r`.

- A justified block no later than `rb` lies above `pending r`
  (`FinalitySetting.justified_above_r`), with the counts at the forks of its path (`cases`).
  A node strictly below `pending r` is kept (`CarrierWindow.kept_sameEpoch` in the epoch of
  `rb`, `CarrierWindow.kept_later` after it). So the head lies strictly below `pending r`
  (`FinalitySetting.settingAt`), and not below FULL `r`.
- A justified block past `rb` is on the EMPTY side (`FinalitySetting.justified_empty`), and
  the head lies below it (`getHead_run_below_justified`). -/
theorem CarrierWindow.head_window
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    (hN : ¬ NodeBelow (run v s).store (.full r) (run v s).head) :
    NodeBelow (run v s).store (.empty r) (run v s).head := by
  have hq := hset.held v hv s hlo hs
  obtain ⟨sA, hrun⟩ := hq.headRun
  rcases hset.cases v hv s hlo hs with ⟨jst, ⟨jb, hjb, hjle⟩, hjst, -, hforks⟩ | ⟨jb, hjb, hjlt⟩
  · have hJr := hset.justified_above_r hw hcol hv hlo hs hjb hjle hV
    have hrs : rb.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch :=
      Nat.div_le_div_right (by unfold raceLo at hlo; omega)
    obtain ⟨m, hk⟩ : ∃ m, KeptBelow (run v s).store r m := by
      by_cases hE : s / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch
      · exact ⟨_, hH.kept_sameEpoch hw hset hcol hv hlo hs hE hV⟩
      · exact hH.kept_later hw hset hcol hv hlo hs (by omega) hV
    obtain ⟨hb, hne⟩ := hset.settingAt hw hcol hv hlo hs hV hjst hforks hJr hjb hk
    rcases NodeBelow.pending_split _ r _ hb hne with h | h
    · exact h
    · exact absurd h hN
  · have hj := hset.justified_empty hw hcol hv hlo hs hjb hjlt hV
    exact NodeBelow.trans _ _ _ _ hj (getHead_run_below_justified _ _ _ _ hrun)

include hw in
/-- **The vote step of the window.** The head of every honest node at a slot `s` of the window
is below EMPTY `r` (`CarrierWindow.head_window`), so in particular the head of a voter of `s`. -/
theorem CarrierWindow.voteStep
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR) :
    VoteStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁) := by
  intro hcol s hlo hs hV hNF i hhon _ _ _
  have hu := hset.fields.honestNode i hhon
  exact .inl (hH.head_window hw hset hcol hu hlo (Nat.le_of_lt hs) hV
    (hNF (nodeOf i) hu s hlo (Nat.lt_succ_self s)))

end Placed

end EthCLSpecs.Proofs.Heze
