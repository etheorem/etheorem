import EthCLSpecs.Proofs.Heze.KeyPrefix
import EthCLSpecs.Proofs.Heze.Committees
import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.StoreClock
import EthCLSpecs.Proofs.Heze.StoreChainState
import EthCLSpecs.Proofs.Heze.FinalizationProgress

/-!
# `EthCLSpecs.Proofs.Heze.FinalEmpty`: a checkpoint at `r` after `epoch(r)` has no honest voter

Take the block `rb` at `r`, a chain `C` of a store that justifies the checkpoint `(r, e)` with
`e` after the epoch of `rb`, and the carrier chain `H`. Both runs hold `rb`. `H` has a block
after `rb` and no later than the first slot of `e`. Suppose that an honest validator `i` voted
`(r, e)` on `C`. Then `i` has two votes of target epoch `e`, and their targets differ:

- The state after `rb` is one state on both runs (`ChainRun.fork_state`). The blocks of a run
  name their parents, so one root fixes the blocks before it.
- `i` is active at `e` on every prefix of `H` (a premise). It is then an honest validator of
  the target test of `e` on `H`. `H` places its vote of `e` (`HonestChain.included`). The
  target of that vote is the checkpoint of `H` at `e` (`RunVote.target_eq`). That root is the
  root of a block after `rb`, so it is not `r` (`chainRoot_ne_of_later`).

An honest validator signs one vote for each target epoch. The two votes are one vote, so the
targets are equal (`fcase_core_active`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState BeaconBlock SignedBeaconBlock ValidatorIndex
  AttestationData Epoch previousEpochOf isActiveValidator)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section Lists
variable [Preset] [HasherTag]

omit [Preset] [HasherTag] in
/-- In a list sorted by `f`, each entry is at most the last entry. -/
theorem le_of_getLast? {β : Type} (f : β → Nat) :
    ∀ (l : List β), l.Pairwise (fun x y => f x ≤ f y) → ∀ x ∈ l, ∀ y, l.getLast? = some y →
      f x ≤ f y
  | [], _, _, hx, _, _ => absurd hx List.not_mem_nil
  | [z], _, x, hx, y, hy => by
    simp only [List.mem_singleton] at hx
    simp only [List.getLast?_singleton, Option.some.injEq] at hy
    subst hx hy
    exact Nat.le_refl _
  | z :: w :: t, hp, x, hx, y, hy => by
    have hy' : (w :: t).getLast? = some y := by
      rw [List.getLast?_cons_cons] at hy
      exact hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (List.pairwise_cons.mp hp).1 y (List.mem_of_getLast? hy')
    · exact le_of_getLast? f (w :: t) (List.pairwise_cons.mp hp).2 x hx' y hy'

end Lists

section Runs
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **A prefix of a run that ends after a block of the run contains the block.** The run is
`a ++ [block x] ++ b`, and the prefix `w` ends at a state with a slot after the slot of `x`.
A prefix that ends before the block ends at a state with a slot at most the slot of `x`. -/
theorem ChainRun.after_block {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {L : List ChainStep}
    {A Z : BeaconState} (h : ChainRun hi L A Z) {a b : List ChainStep} {sbx : SignedBeaconBlock}
    {vx : Bool} (hL : L = a ++ .block sbx vx :: b) {w rest : List ChainStep} (hw : L = w ++ rest)
    {W : BeaconState} (hW : ChainRun hi w A W) (hslot : sbx.message.slot.toNat < W.slot.toNat) :
    ∃ c sR, w = a ++ .block sbx vx :: c ∧ ChainRun hi (a ++ [.block sbx vx]) A sR ∧
      ChainRun hi c sR W := by
  -- The state before the block has the block slot.
  rw [hL] at h
  obtain ⟨m, hm1, hm2⟩ := h.split
  have hmx : sbx.message.slot.toNat = m.slot.toNat := by
    cases hm2 with
    | block _ _ hb _ => exact hb.slot.2
  rw [hL] at hw
  rcases List.append_eq_append_iff.mp hw with ⟨a', hw1, hrest⟩ | ⟨c', hw1, hrest⟩
  · cases a' with
    | nil =>
      rw [List.append_nil] at hw1
      subst hw1
      rw [hW.det hm1] at hslot
      omega
    | cons s a'' =>
      simp only [List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      subst hw1
      have hW' : ChainRun hi ((a ++ [.block sbx vx]) ++ a'') A W := by
        rw [List.append_assoc]
        exact hW
      obtain ⟨sR, h1, h2⟩ := hW'.split
      exact ⟨a'', sR, rfl, h1, h2⟩
  · -- The prefix ends before the block: its end slot is at most the block slot.
    subst hw1
    obtain ⟨m', hm1', hm2'⟩ := hm1.split
    rw [← hW.det hm1'] at hm2'
    have := (hm2'.slot_le hhi).1
    omega

/-- **Two runs from the anchor state with one block reach one state after it.** The blocks of
each run are linked from the anchor block (`ChainRun.linked`), and the block names its parent,
the root after the blocks before it. Without a hash collision the two lists before the block
are one list (`Linked.eq_of_last`). The two runs end at the block slot, so they end in one
state (`ChainRun.det_blocks`). -/
theorem ChainRun.fork_state
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    (hc : ¬ RootCollision) {hi₁ hi₂ : Nat} (hhi₁ : hi₁ ≤ 2 ^ 64 - 1) (hhi₂ : hi₂ ≤ 2 ^ 64 - 1)
    {A : BeaconState} {a : BeaconBlock} (hroots : AnchorRoots A) (hfill : HdrFilled A)
    (hanc : filledHeader A = headerOf a) {p₁ p₂ : List ChainStep} {sb₁ sb₂ : SignedBeaconBlock}
    {v₁ v₂ : Bool} {u₁ u₂ w₁ w₂ : BeaconState}
    (h₁ : ChainRun hi₁ p₁ A u₁) (hv₁ : ValidatedSteps p₁) (hs₁ : BlockStep sb₁ v₁ u₁ w₁)
    (h₂ : ChainRun hi₂ p₂ A u₂) (hv₂ : ValidatedSteps p₂) (hs₂ : BlockStep sb₂ v₂ u₂ w₂)
    (hm : sb₁.message = sb₂.message) : w₁ = w₂ := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hc (.inr h)
  obtain ⟨hL₁, hf₁⟩ := h₁.linked hw hhi₁ hanc (p := []) hv₁ hroots.rootsInv hfill .nil
  obtain ⟨hL₂, hf₂⟩ := h₂.linked hw hhi₂ hanc (p := []) hv₂ hroots.rootsInv hfill .nil
  rw [List.nil_append] at hL₁ hL₂
  have hR₁ : RootsInv A p₁ u₁ := by
    have := h₁.rootsInv hw hhi₁ (p := []) hv₁ hroots.rootsInv
    rwa [List.nil_append] at this
  have hR₂ : RootsInv A p₂ u₂ := by
    have := h₂.rootsInv hw hhi₂ (p := []) hv₂ hroots.rootsInv
    rwa [List.nil_append] at this
  have hpar₁ := hs₁.parent_eq_lastRoot hR₁ hf₁
  have hpar₂ := hs₂.parent_eq_lastRoot hR₂ hf₂
  rw [lastRoot_eq_lastRootOf hw hanc] at hpar₁ hpar₂
  have he : blocksOf p₁ = blocksOf p₂ :=
    hL₁.eq_of_last hcb hL₂ (by rw [← hpar₁, ← hpar₂, hm])
  have X₁ : ChainRun hi₁ (p₁ ++ [.block sb₁ v₁]) A w₁ := h₁.append (.block sb₁ v₁ hs₁ (.nil _))
  have X₂ : ChainRun hi₂ (p₂ ++ [.block sb₂ v₂]) A w₂ := h₂.append (.block sb₂ v₂ hs₂ (.nil _))
  have hblocks : blocksOf (p₁ ++ [.block sb₁ v₁]) = blocksOf (p₂ ++ [.block sb₂ v₂]) := by
    rw [blocksOf_append_block, blocksOf_append_block, he, hm]
  obtain ⟨e1, e2⟩ := hs₁.slot
  obtain ⟨e3, e4⟩ := hs₂.slot
  have hms : sb₁.message.slot.toNat = sb₂.message.slot.toNat := by rw [hm]
  exact X₁.det_blocks hhi₁ hhi₂ X₂ hblocks (by omega)

/-- **The checkpoint root of an epoch is not a block before a later block of the run.** The
root of `e` is the root of the last block at or before the first slot of `e`. A block `b` of the
run lies there, after `rb`. The blocks come in slot order, so the last one is not before `b`,
and its root is not the root of `rb` unless the two roots collide. -/
theorem chainRoot_ne_of_later (hcb : ¬ HtrCollision BeaconBlock) {A Z : BeaconState}
    {a : BeaconBlock} (hanc : htr (filledHeader A) = htr a) {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {S : List ChainStep} (hrun : ChainRun hi S A Z) {e : Nat} (he1 : 1 ≤ e)
    (hT : A.latestBlockHeader.slot.toNat ≤ e * slotsPerEpoch) {b rb : BeaconBlock}
    (hb : b ∈ blocksOf S) (hlt : rb.slot.toNat < b.slot.toNat)
    (hle : b.slot.toNat ≤ e * slotsPerEpoch) : chainRoot A S e ≠ htr rb := by
  rw [chainRoot_pos _ _ he1, rootAtSlot_eq_lastRootOf hanc S hT]
  unfold lastRootOf
  have hbF : b ∈ (blocksOf S).filter (fun x => x.slot.toNat ≤ e * slotsPerEpoch) :=
    List.mem_filter.mpr ⟨hb, by simpa using hle⟩
  cases hl : ((blocksOf S).filter (fun x => x.slot.toNat ≤ e * slotsPerEpoch)).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl
    rw [hl] at hbF
    exact absurd hbF List.not_mem_nil
  | some y =>
    simp only [Option.elim]
    intro hy
    have hyx : y = rb := Classical.byContradiction fun hne => hcb ⟨y, rb, hne, hy⟩
    have hsort := (hrun.blocks_sorted hhi).filter (fun x => decide (x.slot.toNat ≤ e * slotsPerEpoch))
    have := le_of_getLast? (fun x : BeaconBlock => x.slot.toNat) _ hsort b hbF y hl
    rw [hyx] at this
    omega

omit [HasherTag] [Config] [CryptoBackend] in
/-- An honest index of the registry, active at `e` and not slashed, is in `honestList`. -/
theorem mem_honestList_of {W : BeaconState} {honestOf : ValidatorIndex → Bool} {e : Epoch}
    {i : ValidatorIndex} (hlt : i.toNat < W.validators.val.size) (hhon : honestOf i = true)
    (hact : isActiveValidator W.validators.val[i.toNat]! e = true)
    (hsl : (W.validators.val[i.toNat]!).slashed = false) : i ∈ honestList W honestOf e := by
  unfold honestList
  refine List.mem_map.mpr ⟨i.toNat, List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩,
    UInt64.ofNat_toNat⟩
  simp [UInt64.ofNat_toNat, hhon, hact, hsl]

end Runs

section Core
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **No honest validator votes `(r, e)` on a store chain when the carrier chain moved past `r`
by the first slot of `e`.** The setting:

- `C` is a validated run from `A` that holds the block `rb` (`hC`). An honest validator `i`
  votes `d` with the target root `htr rb` and a target epoch `e` after the epoch of `rb`.
- `H` is a validated run from `A` that holds `rb` (`hH`) and a block `b` after `rb`, no later
  than the first slot of `e`. Its state `W` weighs the epoch `e + 1`, and every honest validator
  of the target test of `e` there has a placed vote on `H` (`hinc`, the `included` premise of
  `HonestChain`). `i` is not slashed at `W`.
- `i` is a registry index, active at `e`, at every state of a prefix of `H` (`hactH`).
- An honest validator signs one vote for each target epoch (`hsingle`): a vote of `i` on a
  prefix of `H` with the target epoch of `d` is `d`.

Then the target root of `d` is the checkpoint root of `H` at `e`, which is not `htr rb`. -/
theorem fcase_core_active
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    (hc : ¬ RootCollision) {A : BeaconState} {a : BeaconBlock} (hroots : AnchorRoots A)
    (hfill : HdrFilled A) (hanc : filledHeader A = headerOf a)
    (hanc' : htr (filledHeader A) = htr a)
    (haligned : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch)
    {honestOf : ValidatorIndex → Bool} {rb : BeaconBlock}
    {stepsC : List ChainStep} {vC : BeaconState} (hrunC : ChainRun (2 ^ 64 - 1) stepsC A vC)
    (hvalC : ValidatedSteps stepsC) {aC bC : List ChainStep} {sbC : SignedBeaconBlock}
    {vbC : Bool} (hC : stepsC = aC ++ .block sbC vbC :: bC) (hrbC : sbC.message = rb)
    {i : ValidatorIndex} {d : AttestationData}
    (hd : d.target.root = htr rb)
    {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {stepsH : List ChainStep} {sH : BeaconState}
    (hrunH : ChainRun hi stepsH A sH) (hvalH : ValidatedSteps stepsH) {aH bH : List ChainStep}
    {sbH : SignedBeaconBlock} {vbH : Bool} (hH : stepsH = aH ++ .block sbH vbH :: bH)
    (hrbH : sbH.message = rb) {W : BeaconState}
    (hW : WeighAt hi stepsH A (d.target.epoch.toNat + 1) W)
    (hinc : ∀ x ∈ honestList W honestOf (previousEpochOf (pureState W)),
      PlacedVote hi A stepsH x (previousEpochOf (pureState W)))
    (hhon : honestOf i = true)
    (hsl : i.toNat < W.validators.val.size → (W.validators.val[i.toNat]!).slashed = false)
    (hactH : ∀ (p q : List ChainStep) (z : BeaconState), stepsH = p ++ q → ChainRun hi p A z →
      i.toNat < z.validators.val.size ∧
      isActiveValidator z.validators.val[i.toNat]! d.target.epoch = true)
    {b : BeaconBlock} (hb : b ∈ blocksOf stepsH) (hb1 : rb.slot.toNat < b.slot.toNat)
    (hb2 : b.slot.toNat ≤ d.target.epoch.toNat * slotsPerEpoch)
    (hgt : rb.slot.toNat < d.target.epoch.toNat * slotsPerEpoch)
    (hAe : epochOf A + 1 < d.target.epoch.toNat)
    (hsingle : ∀ (sR : BeaconState) (q s₂ : List ChainStep) (d₂ : AttestationData),
      ChainRun (2 ^ 64 - 1) (aC ++ [.block sbC vbC]) A sR →
      ChainRun hi (aH ++ [.block sbH vbH]) A sR → i.toNat < sR.validators.val.size →
      stepsH = (aH ++ [.block sbH vbH] ++ q) ++ s₂ →
      RunVote hi A (aH ++ [.block sbH vbH] ++ q) i d₂ →
      d₂.target.epoch = d.target.epoch → d₂ = d) : False := by
  have hp := slotsPerEpochPos
  have h64 : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hc (.inr h)
  have hW0 := hW
  -- The state after `rb` on each run.
  have hvalCa : ValidatedSteps aC := fun sb v hm => hvalC sb v (by
    rw [hC]; exact List.mem_append_left _ hm)
  have hvalHa : ValidatedSteps aH := fun sb v hm => hvalH sb v (by
    rw [hH]; exact List.mem_append_left _ hm)
  have hrunC' := hrunC
  rw [hC] at hrunC'
  obtain ⟨uC0, hC1, hC2⟩ := hrunC'.split
  obtain ⟨sRC, hsC, -⟩ : ∃ sR, BlockStep sbC vbC uC0 sR ∧ ChainRun (2 ^ 64 - 1) bC sR vC := by
    cases hC2 with
    | block _ _ hb' hr' => exact ⟨_, hb', hr'⟩
  have hrunH' := hrunH
  rw [hH] at hrunH'
  obtain ⟨uH0, hH1, hH2⟩ := hrunH'.split
  obtain ⟨sRH, hsH, -⟩ : ∃ sR, BlockStep sbH vbH uH0 sR ∧ ChainRun hi bH sR sH := by
    cases hH2 with
    | block _ _ hb' hr' => exact ⟨_, hb', hr'⟩
  have hR : sRC = sRH := ChainRun.fork_state hw hc h64 hhi hroots hfill hanc hC1 hvalCa hsC hH1
    hvalHa hsH (hrbC.trans hrbH.symm)
  -- The voter is a registry index of the state after `rb`: a prefix state of `H`.
  have hregR : i.toNat < sRC.validators.val.size := by
    rw [hR]
    exact (hactH (aH ++ [.block sbH vbH]) bH sRH (by rw [hH]; simp)
      (hH1.append (.block sbH vbH hsH (.nil _)))).1
  -- The weigh state `W` of `H`, and the voter active there.
  obtain ⟨w₁, w₂, hws, hrW, -, heW⟩ := hW
  obtain ⟨hlt, hactW⟩ := hactH w₁ (.slot :: w₂) W hws hrW
  have hprev : previousEpochOf (pureState W) = d.target.epoch := by
    apply UInt64.toNat_inj.mp
    rw [previousEpochOf_toNat_sub, heW]
    omega
  have hiH : i ∈ honestList W honestOf (previousEpochOf (pureState W)) := by
    rw [hprev]
    exact mem_honestList_of hlt hhon hactW (hsl hlt)
  have hWs : (d.target.epoch.toNat + 1) * slotsPerEpoch ≤ W.slot.toNat := by
    rw [← heW]
    exact Nat.div_mul_le_self _ _
  have hsucc : (d.target.epoch.toNat + 1) * slotsPerEpoch =
      d.target.epoch.toNat * slotsPerEpoch + slotsPerEpoch := Nat.succ_mul _ _
  obtain ⟨cH, sR'', hw₁, hH1', -⟩ := hrunH.after_block hhi hH hws hrW
    (by rw [hrbH]; omega)
  -- `H` places the vote of `i` for `e`, and a placed vote of a prefix of `H` sets the flag.
  have hpv := hinc i hiH
  rw [hprev] at hpv
  have hflag := hpv.flag_at_weigh hhi hW0
  rcases hrW.flag_located (p := []) (.nil A) i.toNat d.target.epoch hflag with hA | ⟨d₂, hd₂e, hv₂⟩
  · -- The anchor state carries no flag of `e`, which is past its epoch.
    have hcA := currentEpochOf_epochOf A
    have hpA := previousEpochOf_epochOf A
    rcases hA.epoch_cases with h | h
    · rw [h] at hAe
      omega
    · rw [h] at hAe
      omega
  rw [List.nil_append, UInt64.ofNat_toNat] at hv₂
  have hw₁' : w₁ = aH ++ [.block sbH vbH] ++ cH := by
    rw [hw₁, List.append_assoc, List.singleton_append]
  have hd₂ := hsingle sRC cH (.slot :: w₂) d₂ (hC1.append (.block sbC vbC hsC (.nil _)))
    (by rw [hR]; exact hH1.append (.block sbH vbH hsH (.nil _))) hregR
    (by rw [← hw₁']; exact hws) (by rw [← hw₁']; exact hv₂) hd₂e
  rw [hd₂] at hv₂
  -- The target of the vote is the checkpoint root of `H` at `e`.
  have hvalW : ValidatedSteps w₁ := fun sb v hm => hvalH sb v (by
    rw [hws]; exact List.mem_append_left _ hm)
  have htgt := hv₂.target_eq hw hhi hvalW hroots hrW (by omega)
  have hroot := congrArg (fun c : Cp => c.root) htgt
  simp only [toCp, cpOf] at hroot
  -- The block `b` lies on the prefix `w₁`: the blocks after `W` come at or after its slot.
  have hbw : b ∈ blocksOf w₁ := by
    rw [hws, blocksOf_append] at hb
    rcases List.mem_append.mp hb with hb' | hb'
    · exact hb'
    · exfalso
      have hrunH2 := hrunH
      rw [hws] at hrunH2
      obtain ⟨m, hm1, hm2⟩ := hrunH2.split
      rw [← hrW.det hm1] at hm2
      have := hm2.blocks_slot_ge hhi b hb'
      omega
  have hT : A.latestBlockHeader.slot.toNat ≤ d.target.epoch.toNat * slotsPerEpoch :=
    Nat.le_trans haligned (Nat.mul_le_mul_right _ (by omega))
  exact chainRoot_ne_of_later hcb hanc' hhi hrW (by omega) hT hbw hb1 hb2 (hroot.symm.trans hd)

end Core

end EthCLSpecs.Proofs.Heze
