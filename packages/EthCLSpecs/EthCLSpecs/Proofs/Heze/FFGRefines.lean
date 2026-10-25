import EthCLLib.Proofs.FFG.Model
import EthCLSpecs.Proofs.Heze.JustificationBits
import EthCLSpecs.Proofs.Heze.TargetStake
import EthCLSpecs.Proofs.Heze.Committees

/-!
# `EthCLSpecs.Proofs.Heze.FFGRefines`: a chain run refines Casper FFG

A chain run from the anchor state `st₀` justifies and finalizes checkpoints by the weigh step
of `process_justification_and_finalization`. This module builds the abstract chain of the run
(`ffgChain`, in the model of `EthCLLib.Proofs.FFG.Model`) and proves that the run's justified
and finalized checkpoints are justified and finalized there (`chain_refines`).

## The chain

- The votes are the placed votes of the run (`RunVote`): one vote per validator of `vals` and
  per attestation data of a block of the run.
- The checkpoint of epoch `e` is the root at the first slot of `e` (`rootAtSlot`). At epoch 0
  it is the root of an anchor checkpoint of epoch 0, when one exists. A genesis state holds
  checkpoints with the zero root, and the votes of the first epochs name them as source.
- The stake and the total at epoch `e` are those of the state that weighs `e` (`stakeState`):
  the weigh state of `e` (`WeighAt`), or the end state of the run when the run has no weigh
  state at `e`. The stake counts a validator active at the current or the previous epoch
  (`linkStake`).
- The base holds the three anchor checkpoints, and the checkpoints that the weigh steps of
  epochs `e₀`, `e₀ + 1`, and 2 justify. Here `e₀` is the epoch of `st₀`. Epoch 2 counts only
  when `e₀` is at most 2. Those weigh steps can count flags of votes from before the run, or
  votes with two sources.

`ChainMatches` states what the chain holds, as the later results read it.

## The pull-up

A store can hold the checkpoints of `process_justification_and_finalization` on a block state
(`computePulledUpTip`). That weigh step runs on the end state of the run, in the epoch of that
state. The run has no weigh state at that epoch, so the end state weighs it in the chain too.
`chain_refines_pullup` states the refinement for the pull-up. Both refinements share the
weigh step `refInv_weigh`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState Root Slot Epoch ValidatorIndex AttestationData
  currentEpochOf previousEpochOf getTotalActiveBalance)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerHistoricalRoot)

/-- A checkpoint of the FFG model over block roots. -/
abbrev Cp := EthCLLib.Proofs.FFG.Checkpoint Root

section Chain
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- The abstract checkpoint of a spec checkpoint. -/
def toCp (c : EthCLSpecs.Heze.Checkpoint) : Cp := { epoch := c.epoch.toNat, root := c.root }

/-- The epoch of a state, as a `Nat`. -/
def epochOf (u : BeaconState) : Nat := u.slot.toNat / slotsPerEpoch

/-- The three checkpoints of the anchor state. -/
def anchorCps (st₀ : BeaconState) : List EthCLSpecs.Heze.Checkpoint :=
  [st₀.currentJustifiedCheckpoint, st₀.previousJustifiedCheckpoint, st₀.finalizedCheckpoint]

/-- The root of the chain at epoch `e`: the root at the first slot of `e`. At epoch 0 it is
the root of the first anchor checkpoint of epoch 0, when one exists. -/
def chainRoot (st₀ : BeaconState) (steps : List ChainStep) (e : Nat) : Root :=
  if e = 0 then
    match (anchorCps st₀).find? (fun x => x.epoch.toNat == 0) with
    | some x => x.root
    | none => rootAtSlot st₀ steps 0
  else rootAtSlot st₀ steps (e * slotsPerEpoch)

/-- The checkpoint of the chain at epoch `n`. -/
def cpOf (st₀ : BeaconState) (steps : List ChainStep) (n : Nat) : Cp :=
  { epoch := n, root := chainRoot st₀ steps n }

/-- The epoch from which a justification has a link: after the epoch of the anchor state, and
after the first two epochs. -/
def anchorK (st₀ : BeaconState) : Nat := max (epochOf st₀ + 1) 2

/-- The target test of the previous epoch at `u`. -/
def jpOf (u : BeaconState) : Bool :=
  decide ((tgtBal u (previousEpochOf (pureState u))).toNat * 3 ≥
    (totBal u).toNat * 2)

/-- The target test of the current epoch at `u`. -/
def jcOf (u : BeaconState) : Bool :=
  decide ((tgtBal u (currentEpochOf (pureState u))).toNat * 3 ≥
    (totBal u).toNat * 2)

variable [Config] [CryptoBackend]

open Classical in
/-- The weigh state of epoch `e`, when the run has one. -/
noncomputable def weighState (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) (e : Nat) :
    Option BeaconState :=
  if h : ∃ u, WeighAt hi steps st₀ e u then some h.choose else none

open Classical in
/-- The end state of the run, when the steps run from `st₀`. -/
noncomputable def endState (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) :
    Option BeaconState :=
  if h : ∃ u, ChainRun hi steps st₀ u then some h.choose else none

/-- The state that weighs epoch `e`: the weigh state of `e`, or the end state of the run when
the run has no weigh state at `e`. A pull-up of the end state weighs its epoch with the end
state. -/
noncomputable def stakeState (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) (e : Nat) :
    Option BeaconState :=
  match weighState hi steps st₀ e with
  | some u => some u
  | none => endState hi steps st₀

/-- The checkpoints that the weigh step of epoch `e` justifies, on the state that weighs `e`. -/
noncomputable def weighCps (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) (e : Nat) :
    List Cp :=
  match stakeState hi steps st₀ e with
  | some u =>
    if 2 ≤ e then (if jcOf u then [cpOf st₀ steps e] else []) ++
      (if jpOf u then [cpOf st₀ steps (e - 1)] else [])
    else []
  | none => []

/-- The base of the chain: the anchor checkpoints, and the checkpoints that the weigh steps
of epochs `e₀`, `e₀ + 1`, and 2 justify. Epoch 2 counts only when the anchor epoch `e₀` is at
most 2. A run from a later anchor has no weigh step at epoch 2. -/
noncomputable def chainBase (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) : List Cp :=
  (anchorCps st₀).map toCp ++ weighCps hi steps st₀ (epochOf st₀) ++
    weighCps hi steps st₀ (epochOf st₀ + 1) ++
    (if epochOf st₀ ≤ 2 then weighCps hi steps st₀ 2 else [])

/-- The attestation data of the blocks of the run. -/
def attDatas (steps : List ChainStep) : List AttestationData :=
  (blocksOf steps).flatMap fun b => b.body.attestations.toArray.toList.map (·.data)

open Classical in
/-- The votes of the chain: one per validator of `vals` and per placed vote of the run. -/
noncomputable def chainVotes (hi : Nat) (st₀ : BeaconState) (steps : List ChainStep)
    (vals : List ValidatorIndex) : List (EthCLLib.Proofs.FFG.Vote ValidatorIndex Root) :=
  vals.flatMap fun i => (attDatas steps).filterMap fun d =>
    if RunVote hi st₀ steps i d then some { val := i, source := toCp d.source, target := toCp d.target }
    else none

/-- The abstract chain of a run from `st₀`, over the validators `vals`. The stake and the total
of each epoch are those of the state that weighs it. -/
noncomputable def ffgChain (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState)
    (vals : List ValidatorIndex) : EthCLLib.Proofs.FFG.Chain ValidatorIndex Root where
  votes := chainVotes hi st₀ steps vals
  stake e i := match stakeState hi steps st₀ e with
    | some u => linkStake u i
    | none => 0
  total e := match stakeState hi steps st₀ e with
    | some u => (totBal u).toNat
    | none => 0
  vals := vals
  cpAt e := some (chainRoot st₀ steps e)
  base := chainBase hi steps st₀

/-- The weigh state of an epoch is the one the run reaches. -/
theorem weighState_of {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ : BeaconState} {e : Nat} {u : BeaconState} (h : WeighAt hi steps st₀ e u) :
    weighState hi steps st₀ e = some u := by
  have hex : ∃ u, WeighAt hi steps st₀ e u := ⟨u, h⟩
  unfold weighState
  rw [dif_pos hex]
  exact congrArg some (hex.choose_spec.unique hhi h)

/-- A weigh state comes before the end of the run: the next slot step leaves its epoch. -/
theorem WeighAt.epoch_lt {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ st : BeaconState} {e : Nat} {u : BeaconState} (h : WeighAt hi steps st₀ e u)
    (hrun : ChainRun hi steps st₀ st) : e < epochOf st := by
  obtain ⟨s₁, s₂, hs, hr, hb, he⟩ := h
  rw [hs] at hrun
  obtain ⟨m, hm1, hm2⟩ := hrun.split
  rw [← hr.det hm1] at hm2
  cases hm2 with
  | slot hlt hstep hrest =>
    have hlt' : u.slot.toNat < hi := hlt
    have h1 := hstep.slot (by omega)
    have h2 := hrest.epoch_le hhi
    rw [h1, succ_div_of_mod_eq hb, he] at h2
    unfold epochOf
    omega

/-- The weigh state weighs its epoch. -/
theorem stakeState_of_weigh {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ : BeaconState} {e : Nat} {u : BeaconState} (h : WeighAt hi steps st₀ e u) :
    stakeState hi steps st₀ e = some u := by
  unfold stakeState
  rw [weighState_of hhi h]

/-- The end state is the one the run reaches. -/
theorem endState_of {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    (h : ChainRun hi steps st₀ st) : endState hi steps st₀ = some st := by
  have hex : ∃ u, ChainRun hi steps st₀ u := ⟨st, h⟩
  unfold endState
  rw [dif_pos hex]
  exact congrArg some (hex.choose_spec.det h)

/-- At an epoch with no weigh state, the end state weighs the epoch. -/
theorem stakeState_of_end {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState} {e : Nat}
    (h : ChainRun hi steps st₀ st) (hno : ∀ u, ¬ WeighAt hi steps st₀ e u) :
    stakeState hi steps st₀ e = some st := by
  have hw : weighState hi steps st₀ e = none := by
    unfold weighState
    rw [dif_neg fun ⟨u, hu⟩ => hno u hu]
  unfold stakeState
  rw [hw, endState_of h]

/-- The end state weighs its own epoch. -/
theorem stakeState_end {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ st : BeaconState} (h : ChainRun hi steps st₀ st) :
    stakeState hi steps st₀ (epochOf st) = some st :=
  stakeState_of_end h fun _ hu => Nat.lt_irrefl _ (hu.epoch_lt hhi h)

/-- A placed vote names attestation data of a block of the run. -/
theorem RunVote.mem_attDatas {hi : Nat} {st₀ : BeaconState} {steps : List ChainStep}
    {i : ValidatorIndex} {d : AttestationData} (h : RunVote hi st₀ steps i d) :
    d ∈ attDatas steps := by
  obtain ⟨s₁, s₂, sb, v, -, -, -, att, hs, -, ha, hd, -⟩ := h
  unfold attDatas
  rw [List.mem_flatMap]
  refine ⟨sb.message, ?_, List.mem_map.mpr ⟨att, Array.mem_toList_iff.mpr ha, hd⟩⟩
  rw [hs, blocksOf_append]
  exact List.mem_append_right _ List.mem_cons_self

/-- The votes of the chain are the placed votes of validators of `vals`. -/
theorem mem_chainVotes {hi : Nat} {st₀ : BeaconState} {steps : List ChainStep}
    {vals : List ValidatorIndex} (x : EthCLLib.Proofs.FFG.Vote ValidatorIndex Root) :
    x ∈ chainVotes hi st₀ steps vals ↔ x.val ∈ vals ∧ ∃ d, RunVote hi st₀ steps x.val d ∧
      x.source = toCp d.source ∧ x.target = toCp d.target := by
  unfold chainVotes
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, d, -, hx⟩
    split at hx
    · rename_i hv
      cases hx
      exact ⟨hi, d, hv, rfl, rfl⟩
    · cases hx
  · rintro ⟨hi, d, hv, hs, ht⟩
    refine ⟨x.val, hi, d, hv.mem_attDatas, ?_⟩
    rw [if_pos hv, hs.symm, ht.symm]

/-- A validator of `vals` with a placed vote votes for its link in the chain. -/
theorem voted_of_runVote {hi : Nat} {st₀ : BeaconState} {steps : List ChainStep}
    {vals : List ValidatorIndex} {i : ValidatorIndex} {d : AttestationData} (hi' : i ∈ vals)
    (hv : RunVote hi st₀ steps i d) :
    EthCLLib.Proofs.FFG.voted (ffgChain hi steps st₀ vals) (toCp d.source) (toCp d.target) i
      = true := by
  unfold EthCLLib.Proofs.FFG.voted
  refine List.any_eq_true.mpr ⟨{ val := i, source := toCp d.source, target := toCp d.target },
    (mem_chainVotes _).mpr ⟨hi', d, hv, rfl, rfl⟩, ?_⟩
  simp

/-- The anchor checkpoints are on the anchor history. Two of epoch 0 share a root, and one of
a later epoch has the root that the anchor state records at the first slot of its epoch. -/
structure AnchorCps (st₀ : BeaconState) : Prop where
  zero : ∀ x ∈ anchorCps st₀, ∀ y ∈ anchorCps st₀, x.epoch.toNat = 0 → y.epoch.toNat = 0 →
    x.root = y.root
  roots : ∀ x ∈ anchorCps st₀, 1 ≤ x.epoch.toNat →
    x.root = anchorRoot st₀ (x.epoch.toNat * slotsPerEpoch)

omit [Config] [CryptoBackend] in
/-- After epoch 0, the root of the chain is the root at the first slot. -/
theorem chainRoot_pos (st₀ : BeaconState) (steps : List ChainStep) {e : Nat} (he : 1 ≤ e) :
    chainRoot st₀ steps e = rootAtSlot st₀ steps (e * slotsPerEpoch) := by
  unfold chainRoot
  rw [if_neg (by omega)]

omit [Config] [CryptoBackend] in
/-- Each anchor checkpoint has an epoch at most the previous epoch of the anchor state. -/
theorem anchorCps_epoch_le {st₀ : BeaconState} (hord : StateCkptOrd st₀)
    {x : EthCLSpecs.Heze.Checkpoint} (hx : x ∈ anchorCps st₀) :
    x.epoch.toNat ≤ epochOf st₀ - 1 := by
  obtain ⟨h1, h2, h3⟩ := hord
  rw [UInt64.le_iff_toNat_le] at h1 h2 h3
  rw [previousEpochOf_toNat_sub] at h3
  simp only [anchorCps, List.mem_cons, List.not_mem_nil, or_false] at hx
  unfold epochOf
  rcases hx with rfl | rfl | rfl <;> omega

omit [Config] [CryptoBackend] in
/-- An anchor checkpoint is on the chain of a run whose blocks come at or after the anchor
slot. -/
theorem anchorCp_onChain {st₀ : BeaconState} {steps : List ChainStep} (hcps : AnchorCps st₀)
    (hord : StateCkptOrd st₀) (hb : ∀ b ∈ blocksOf steps, st₀.slot.toNat ≤ b.slot.toNat)
    {x : EthCLSpecs.Heze.Checkpoint} (hx : x ∈ anchorCps st₀) :
    chainRoot st₀ steps x.epoch.toNat = x.root := by
  by_cases h0 : x.epoch.toNat = 0
  · unfold chainRoot
    rw [h0, if_pos rfl]
    cases hf : (anchorCps st₀).find? (fun y => y.epoch.toNat == 0) with
    | none =>
      exact absurd (List.find?_eq_none.mp hf x hx) (by simp [h0])
    | some y =>
      have hy := List.mem_of_find?_eq_some hf
      have hy0 := List.find?_some hf
      exact hcps.zero y hy x hx (by simpa using hy0) h0
  · have hle := anchorCps_epoch_le hord hx
    have hpos := slotsPerEpochPos
    rw [chainRoot_pos _ _ (by omega), rootAtSlot_of_lt st₀ steps _ fun b hb' => ?_,
      ← hcps.roots x hx (by omega)]
    have := hb b hb'
    have hdiv := Nat.div_mul_le_self st₀.slot.toNat slotsPerEpoch
    unfold epochOf at hle
    have : x.epoch.toNat * slotsPerEpoch + slotsPerEpoch ≤
        st₀.slot.toNat / slotsPerEpoch * slotsPerEpoch := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- The base checkpoints have epochs at most `anchorK` and are on the chain. -/
theorem base_onChain {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState}
    {vals : List ValidatorIndex} (hcps : AnchorCps st₀) (hord : StateCkptOrd st₀)
    (hb : ∀ b ∈ blocksOf steps, st₀.slot.toNat ≤ b.slot.toNat) :
    ∀ x ∈ (ffgChain hi steps st₀ vals).base, x.epoch ≤ anchorK st₀ ∧
      (ffgChain hi steps st₀ vals).OnChain x := by
  -- A weigh checkpoint is the chain's checkpoint at its epoch.
  have hw : ∀ e, e ≤ anchorK st₀ → ∀ x ∈ weighCps hi steps st₀ e, x.epoch ≤ anchorK st₀ ∧
      (ffgChain hi steps st₀ vals).OnChain x := by
    intro e he x hx
    unfold weighCps at hx
    split at hx
    · split at hx
      · simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> split at hx <;>
          simp only [List.mem_singleton, List.not_mem_nil] at hx <;> subst hx <;>
          exact ⟨by simp only [cpOf]; omega, rfl⟩
      · cases hx
    · cases hx
  intro x hx
  change x ∈ chainBase hi steps st₀ at hx
  unfold chainBase at hx
  simp only [List.mem_append, List.mem_map] at hx
  have hK : epochOf st₀ + 1 ≤ anchorK st₀ ∧ 2 ≤ anchorK st₀ := ⟨Nat.le_max_left _ _,
    Nat.le_max_right _ _⟩
  rcases hx with ((⟨y, hy, rfl⟩ | hx) | hx) | hx
  · refine ⟨?_, ?_⟩
    · have := anchorCps_epoch_le hord hy
      simp only [toCp]
      omega
    · change some (chainRoot st₀ steps y.epoch.toNat) = some y.root
      rw [anchorCp_onChain hcps hord hb hy]
  · exact hw _ (by omega) x hx
  · exact hw _ hK.1 x hx
  · split at hx
    · exact hw _ hK.2 x hx
    · cases hx

/-- What the chain of a run holds. The votes are the placed votes of validators of `vals`.
The checkpoint of each epoch is `chainRoot`. At each epoch, the total and the stake are those
of the state that weighs it (`stakeState`): the weigh state, or the end state of the run. The
base checkpoints have epochs at most `anchorK` and are on the chain. -/
structure ChainMatches (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState)
    (vals : List ValidatorIndex) (c : EthCLLib.Proofs.FFG.Chain ValidatorIndex Root) : Prop where
  votes : ∀ x, x ∈ c.votes ↔ x.val ∈ vals ∧ ∃ d, RunVote hi st₀ steps x.val d ∧
    x.source = toCp d.source ∧ x.target = toCp d.target
  vals : c.vals = vals
  cpAt : ∀ e, c.cpAt e = some (chainRoot st₀ steps e)
  stake : ∀ e u, stakeState hi steps st₀ e = some u →
    c.total e = (totBal u).toNat ∧ ∀ i, c.stake e i = linkStake u i
  base : ∀ x ∈ c.base, x.epoch ≤ anchorK st₀ ∧ c.OnChain x

/-- The chain of a run matches the run. -/
theorem ffgChain_matches {hi : Nat} {steps : List ChainStep}
    {st₀ : BeaconState} {vals : List ValidatorIndex} (hcps : AnchorCps st₀)
    (hord : StateCkptOrd st₀) (hb : ∀ b ∈ blocksOf steps, st₀.slot.toNat ≤ b.slot.toNat) :
    ChainMatches hi steps st₀ vals (ffgChain hi steps st₀ vals) := by
  refine ⟨mem_chainVotes, rfl, fun _ => rfl, fun e u hs => ?_, base_onChain hcps hord hb⟩
  refine ⟨?_, fun i => ?_⟩
  · change (match stakeState hi steps st₀ e with
      | some u => (totBal u).toNat
      | none => 0) = _
    rw [hs]
  · change (match stakeState hi steps st₀ e with
      | some u => linkStake u i
      | none => 0) = _
    rw [hs]

end Chain

/-! ## The placed votes -/

section Votes
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- The fields that `locView` names. -/
theorem locView_eq {a b : BeaconState} (h : locView (pureState a) = locView (pureState b)) :
    ckView (pureState a) = ckView (pureState b) ∧ a.slot = b.slot ∧
      a.blockRoots = b.blockRoots := by
  simp only [locView, ordView, Prod.mk.injEq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

omit [Config] [CryptoBackend] in
/-- The current epoch as a `Nat`. -/
theorem currentEpochOf_epochOf (u : BeaconState) :
    (currentEpochOf (pureState u)).toNat = epochOf u := currentEpochOf_toNat u

omit [Config] [CryptoBackend] in
/-- The previous epoch as a `Nat`. -/
theorem previousEpochOf_epochOf (u : BeaconState) :
    (previousEpochOf (pureState u)).toNat = epochOf u - 1 := previousEpochOf_toNat_sub u

omit [Config] [CryptoBackend] in
/-- Two states with one slot have one current epoch and one previous epoch. -/
theorem epochs_of_slot {a b : BeaconState} (h : a.slot = b.slot) :
    currentEpochOf (pureState a) = currentEpochOf (pureState b) ∧
      previousEpochOf (pureState a) = previousEpochOf (pureState b) :=
  epochs_eq_of_toNat (by rw [h])

omit [Config] [CryptoBackend] in
/-- `get_block_root` reads `get_block_root_at_slot` at the start slot of the epoch. A successful
read computed that start slot without a fault, so it is the product `n * SLOTS_PER_EPOCH`. -/
theorem getBlockRoot_runPure_ok {u w : BeaconState} {n : Epoch} {r : Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u) n) u
      = .ok (r, w)) :
    runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun) (pureState u)
      (n * UInt64.ofNat slotsPerEpoch)) u = .ok (r, w) := by
  rw [EthCLLib.Proofs.runPure_eq] at h ⊢
  unfold EthCLSpecs.Heze.getBlockRoot at h
  rw [EthCLLib.Proofs.run_bind] at h
  cases hs : (liftErr (m := HezeRun) (EthCLSpecs.Heze.computeStartSlotAtEpoch n)).run
      (pureState u) with
  | error e => rw [hs] at h; cases h
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hs, EthCLLib.Proofs.except_bind_ok] at h
    obtain ⟨hx, rfl⟩ := liftErr_run_ok_spec hs
    rw [computeStartSlotAtEpoch_ok_eq hx] at h
    exact h

/-- A placed vote with a target epoch after epoch 0 targets the chain's checkpoint at that
epoch. `processAttestation` read the target root with `getBlockRoot` on a state with the slot
and the block roots of the state before the block. That read gives the root at the first slot
of the epoch, and the later blocks of the run come after it. -/
theorem RunVote.target_eq
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ st : BeaconState} {steps : List ChainStep}
    {i : ValidatorIndex} {d : AttestationData} (hv : RunVote hi st₀ steps i d)
    (hval : ValidatedSteps steps) (hroots : AnchorRoots st₀) (hrun : ChainRun hi steps st₀ st)
    (h1 : 1 ≤ d.target.epoch.toNat) :
    toCp d.target = cpOf st₀ steps d.target.epoch.toNat := by
  obtain ⟨s₁, s₂, sb, v, ub, pre, post, att, hs, hr, -, hd, ⟨-, -, -, htgt⟩, hloc, -, hep⟩ := hv
  subst hd hs
  obtain ⟨-, hsl, hbr⟩ := locView_eq hloc
  have hinv := hr.rootsInv hw hhi (fun sb v hm => hval sb v (List.mem_append_left _ hm))
    hroots.rootsInv
  rw [List.nil_append] at hinv
  replace htgt := getBlockRoot_runPure_ok htgt
  have hroot := hinv.read_of hsl hbr htgt
  obtain ⟨hlt, -⟩ := getBlockRootAtSlot_run_ok htgt
  -- The target epoch is at most the epoch of the state, so its first slot fits a `uint64`.
  have hle : att.data.target.epoch.toNat ≤ ub.slot.toNat / slotsPerEpoch := by
    rcases hep with he | he <;> rw [he]
    · exact Nat.le_of_eq (currentEpochOf_epochOf ub)
    · rw [previousEpochOf_epochOf]
      exact Nat.sub_le _ _
  have hfit : att.data.target.epoch.toNat * slotsPerEpoch < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_right _ hle)
      (Nat.div_mul_le_self _ _)) ub.slot.toNat_lt
  rw [epochStart_toNat _ hfit] at hroot hlt
  rw [hsl] at hlt
  -- The blocks after the prefix come at or after the slot of `ub`.
  obtain ⟨m, hm1, hm2⟩ := hrun.split
  rw [← hr.det hm1] at hm2
  have hb := hm2.blocks_slot_ge hhi
  unfold toCp cpOf
  rw [chainRoot_pos _ _ h1, rootAtSlot_append_of_lt _ _ _ _ fun b hb' => by
    have := hb b hb'
    omega, ← hroot]

/-- The source of a placed vote for the current epoch of a later state `u` of the run is the
current justified checkpoint of `u`. The vote was cast in the epoch of `u`, and the steps in
an epoch keep the checkpoints. -/
theorem RunVote.source_cur {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ u : BeaconState}
    {p : List ChainStep} {i : ValidatorIndex} {d : AttestationData}
    (hv : RunVote hi st₀ p i d) (hu : ChainRun hi p st₀ u)
    (he : d.target.epoch = currentEpochOf (pureState u)) (h2 : 2 ≤ epochOf u) :
    d.source = u.currentJustifiedCheckpoint := by
  obtain ⟨s₁, s₂, sb, v, ub, pre, post, att, hs, hr, -, hd, ⟨-, -, hsrc, -⟩, hloc, -, hep⟩ := hv
  subst hd hs
  obtain ⟨hck, hsl, -⟩ := locView_eq hloc
  obtain ⟨m, hm1, hm2⟩ := hu.split
  rw [← hr.det hm1] at hm2
  have hBE := hm2.epoch_le hhi
  have hE := congrArg UInt64.toNat he
  rw [currentEpochOf_epochOf] at hE
  obtain ⟨hc, -⟩ := epochs_of_slot hsl
  simp only [ckView, Prod.mk.injEq] at hck
  rw [hsrc]
  unfold sourceFor
  rcases hep with ht | ht
  · rw [if_pos (ht.trans hc.symm)]
    rw [ht, currentEpochOf_epochOf] at hE
    have hk := hm2.ckView_of_epoch hhi hE
    simp only [ckView, Prod.mk.injEq] at hk
    exact hck.2.1.trans hk.2.1.symm
  · exfalso
    rw [ht, previousEpochOf_epochOf] at hE
    unfold epochOf at hE h2
    omega

/-- The source of a placed vote for the previous epoch of a later state `u` of the run is the
previous justified checkpoint of `u`. A vote cast in the epoch of `u` names that checkpoint. A
vote cast in the epoch before names the current justified checkpoint of that epoch, which the
weigh step at its end makes the previous one. -/
theorem RunVote.source_prev {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ u : BeaconState}
    {p : List ChainStep} {i : ValidatorIndex} {d : AttestationData}
    (hv : RunVote hi st₀ p i d) (hu : ChainRun hi p st₀ u)
    (he : d.target.epoch = previousEpochOf (pureState u)) (h3 : 3 ≤ epochOf u) :
    d.source = u.previousJustifiedCheckpoint := by
  obtain ⟨s₁, s₂, sb, v, ub, pre, post, att, hs, hr, -, hd, ⟨-, -, hsrc, -⟩, hloc, -, hep⟩ := hv
  subst hd hs
  obtain ⟨hck, hsl, -⟩ := locView_eq hloc
  obtain ⟨m, hm1, hm2⟩ := hu.split
  rw [← hr.det hm1] at hm2
  have hBE := hm2.epoch_le hhi
  have hE := congrArg UInt64.toNat he
  rw [previousEpochOf_epochOf] at hE
  obtain ⟨hc, -⟩ := epochs_of_slot hsl
  simp only [ckView, Prod.mk.injEq] at hck
  rw [hsrc]
  unfold sourceFor
  by_cases ht : att.data.target.epoch = currentEpochOf (pureState ub)
  · -- Cast in the epoch before: the weigh step made its current checkpoint the previous one.
    rw [if_pos (ht.trans hc.symm)]
    rw [ht, currentEpochOf_epochOf] at hE
    unfold epochOf at hE h3 hBE
    have hn := hm2.prevJ_next_epoch hhi (by omega) (by omega)
    exact hck.2.1.trans hn.symm
  · rw [if_neg (fun h' => ht (h'.trans hc))]
    rcases hep with ht' | ht'
    · exact absurd ht' ht
    rw [ht', previousEpochOf_epochOf] at hE
    unfold epochOf at hE h3 hBE
    have hk := hm2.ckView_of_epoch hhi (by omega)
    simp only [ckView, Prod.mk.injEq] at hk
    exact hck.1.trans hk.1.symm

end Votes

/-! ## The links -/

section Links
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The premises of the refinement, for a run from `st₀` through `steps` to `st`, over the
validators `vals`. -/
structure RefSetting (hi : Nat) (steps : List ChainStep) (st₀ st : BeaconState)
    (vals : List ValidatorIndex) : Prop where
  hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32
  hhi : hi ≤ 2 ^ 64 - 1
  run : ChainRun hi steps st₀ st
  val : ValidatedSteps steps
  roots : AnchorRoots st₀
  cps : AnchorCps st₀
  ord : StateCkptOrd st₀
  sphr : 2 * slotsPerEpoch ≤ slotsPerHistoricalRoot
  tot : ∀ s₁ s₂ u, steps = s₁ ++ s₂ → ChainRun hi s₁ st₀ u → RunTotals u
  nodup : vals.Nodup
  vals : ∀ s₁ s₂ u, steps = s₁ ++ s₂ → ChainRun hi s₁ st₀ u →
    ∀ i < u.validators.val.size, UInt64.ofNat i ∈ vals

/-- A passed target test at the state `u` that weighs its epoch is a link of the chain. Its
source is the checkpoint `src` that each placed vote for the target epoch names. Its target is
the chain's checkpoint at the target epoch. The link is weighed at the epoch of `u`, with the
stake and the total of `u`. The state `u` is the weigh state, or the end state of the run. -/
theorem RefSetting.weigh_link {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p r : List ChainStep}
    {u : BeaconState} (hsteps : steps = p ++ r) (hu : ChainRun hi p st₀ u)
    (hstk : stakeState hi steps st₀ (epochOf u) = some u) {e : Epoch}
    (he : e = currentEpochOf (pureState u) ∨ e = previousEpochOf (pureState u))
    (heK : anchorK st₀ ≤ e.toNat)
    (htest : (tgtBal u e).toNat * 3 ≥ (totBal u).toNat * 2)
    (src : EthCLSpecs.Heze.Checkpoint)
    (hsrc : ∀ i d, RunVote hi st₀ p i d → d.target.epoch = e → d.source = src)
    (hlt : src.epoch.toNat < e.toNat) (hon : (ffgChain hi steps st₀ vals).OnChain (toCp src)) :
    EthCLLib.Proofs.FFG.Link (ffgChain hi steps st₀ vals) (toCp src)
      (cpOf st₀ steps e.toNat) := by
  have hK : epochOf st₀ + 1 ≤ anchorK st₀ ∧ 2 ≤ anchorK st₀ :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hm := ffgChain_matches (hi := hi) (vals := vals) S.cps S.ord (S.run.blocks_slot_ge S.hhi)
  obtain ⟨htot, hst⟩ := hm.stake _ _ hstk
  have hT := S.tot p r u hsteps hu
  have heE : e.toNat = epochOf u ∨ e.toNat = epochOf u - 1 := by
    rcases he with he | he <;> rw [he]
    · exact .inl (currentEpochOf_epochOf u)
    · exact .inr (previousEpochOf_epochOf u)
  refine ⟨hlt, hon, rfl, epochOf u, show e.toNat ≤ epochOf u by omega,
    show epochOf u ≤ e.toNat + 1 by omega, ?_⟩
  rw [htot]
  unfold EthCLLib.Proofs.FFG.stakeSum
  rw [show (ffgChain hi steps st₀ vals).stake (epochOf u) = linkStake u from funext hst]
  refine link_weight hT he htest _ fun idx hidx x hx => ?_
  -- Each counted index is a validator of `vals` with a placed vote for this link.
  have h64 := hT.2.2
  have hxs := (mem_participating hidx h64 hx).1
  have hxv : x ∈ vals := by
    have := S.vals p r u hsteps hu x.toNat hxs
    rwa [UInt64.ofNat_toNat] at this
  refine List.mem_filter.mpr ⟨hxv, ?_⟩
  have hf := targetFlag_of_participating hidx h64 he hx
  rcases hu.flag_located (p := []) (.nil _) x.toNat e hf with h0 | ⟨d, hd, hv⟩
  · exfalso
    have := h0.le_current
    rw [currentEpochOf_epochOf] at this
    omega
  · rw [List.nil_append, UInt64.ofNat_toNat] at hv
    have hv' : RunVote hi st₀ steps x d := by
      rw [hsteps]
      exact hv.append _
    have ht := hv'.target_eq S.hw S.hhi S.val S.roots S.run (by rw [hd]; omega)
    rw [← hsrc x d hv hd, ← hd, ← ht]
    exact voted_of_runVote hxv hv'

/-- A justified checkpoint is on the chain. -/
theorem RefSetting.onChain {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {x : Cp}
    (h : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals) x) :
    (ffgChain hi steps st₀ vals).OnChain x :=
  h.onChain fun y hy => (base_onChain S.cps S.ord (S.run.blocks_slot_ge S.hhi) y hy).2

/-- The root that the weigh step reads for epoch `n`, at the end of epoch `E`, is the chain's
root at `n`, for `n` the current or the previous epoch. The read runs on `slotWrite u`. The
slot of `u` is the last slot of `E`, so the first slot of `n` is less than
`SLOTS_PER_HISTORICAL_ROOT` behind. -/
theorem RefSetting.weigh_root {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p q : List ChainStep}
    {u : BeaconState} (hsteps : steps = p ++ .slot :: q) (hu : ChainRun hi p st₀ u)
    (hb : (u.slot.toNat + 1) % slotsPerEpoch = 0) {n : Epoch} {r : Root}
    (hn : n.toNat + 1 = epochOf u ∨ n.toNat = epochOf u) (h1 : 1 ≤ n.toNat)
    (h : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun)
      (pureState (slotWrite u)) n) (slotWrite u) = .ok (r, slotWrite u)) :
    r = chainRoot st₀ steps n.toNat := by
  have hpos := slotsPerEpochPos
  have hsphr := S.sphr
  -- The slot of `u` is the last slot of its epoch.
  have hslot : u.slot.toNat + 1 = (epochOf u + 1) * slotsPerEpoch := by
    have := Nat.div_add_mod (u.slot.toNat + 1) slotsPerEpoch
    rw [hb, Nat.add_zero, succ_div_of_mod_eq hb] at this
    unfold epochOf
    rw [Nat.mul_comm]
    exact this.symm
  have hle : n.toNat * slotsPerEpoch + slotsPerEpoch ≤ u.slot.toNat + 1 := by
    rw [hslot, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hfit : n.toNat * slotsPerEpoch < 2 ^ 64 := by
    have := u.slot.toNat_lt
    omega
  have hinv := hu.rootsInv S.hw S.hhi
    (fun sb v hm => S.val sb v (by rw [hsteps]; exact List.mem_append_left _ hm))
    S.roots.rootsInv
  rw [List.nil_append] at hinv
  replace h := getBlockRoot_runPure_ok h
  have hr := hinv.read_slotWrite h (by
    rw [epochStart_toNat _ hfit]
    have : (epochOf u + 1) * slotsPerEpoch ≤ n.toNat * slotsPerEpoch + 2 * slotsPerEpoch := by
      rw [Nat.add_mul, Nat.one_mul]
      rcases hn with hn | hn
      · rw [← hn, Nat.add_mul, Nat.one_mul]
        omega
      · rw [hn]
        omega
    omega)
  rw [epochStart_toNat _ hfit] at hr
  rw [hr, chainRoot_pos _ _ h1, hsteps]
  -- The blocks after the prefix come after the slot of `u`.
  obtain ⟨m, hm1, hm2⟩ := (show ChainRun hi (p ++ .slot :: q) st₀ st from hsteps ▸ S.run).split
  rw [← hu.det hm1] at hm2
  cases hm2 with
  | slot hlt' hstep hrest =>
    have hlt'' : u.slot.toNat < hi := hlt'
    have hs := hstep.slot (by have := S.hhi; omega)
    have hb' := hrest.blocks_slot_ge S.hhi
    exact (rootAtSlot_append_of_lt _ _ _ _ fun b hb'' => by
      have := hb' b hb''
      omega).symm

/-! ## The base -/

/-- An anchor checkpoint is in the base. -/
theorem mem_base_anchor {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState}
    {vals : List ValidatorIndex} {x : EthCLSpecs.Heze.Checkpoint} (hx : x ∈ anchorCps st₀) :
    toCp x ∈ (ffgChain hi steps st₀ vals).base :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem hx)))

/-- A checkpoint of the weigh step of epoch `e₀`, `e₀ + 1`, or 2 is in the base. Epoch 2
needs `e₀ ≤ 2`. -/
theorem mem_base_weigh {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState}
    {vals : List ValidatorIndex} {e : Nat}
    (he : e = epochOf st₀ ∨ e = epochOf st₀ + 1 ∨ (e = 2 ∧ epochOf st₀ ≤ 2)) {y : Cp}
    (hy : y ∈ weighCps hi steps st₀ e) : y ∈ (ffgChain hi steps st₀ vals).base := by
  change y ∈ chainBase hi steps st₀
  unfold chainBase
  rcases he with rfl | rfl | ⟨rfl, h2⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hy))
  · exact List.mem_append_left _ (List.mem_append_right _ hy)
  · rw [if_pos h2]
    exact List.mem_append_right _ hy

/-- The weigh step of epoch `e` justifies the checkpoint of `e` when the current test passes. -/
theorem mem_weighCps_cur {hi : Nat} {steps : List ChainStep}
    {st₀ u : BeaconState} {e : Nat} (hs : stakeState hi steps st₀ e = some u) (h2 : 2 ≤ e)
    (hjc : jcOf u = true) : cpOf st₀ steps e ∈ weighCps hi steps st₀ e := by
  unfold weighCps
  rw [hs]
  dsimp only
  rw [if_pos h2, hjc]
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- The weigh step of epoch `e` justifies the checkpoint of `e - 1` when the previous test
passes. -/
theorem mem_weighCps_prev {hi : Nat} {steps : List ChainStep}
    {st₀ u : BeaconState} {e : Nat} (hs : stakeState hi steps st₀ e = some u) (h2 : 2 ≤ e)
    (hjp : jpOf u = true) : cpOf st₀ steps (e - 1) ∈ weighCps hi steps st₀ e := by
  unfold weighCps
  rw [hs]
  dsimp only
  rw [if_pos h2, hjp]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-! ## The two justifications of the weigh step -/

/-- The weigh step at `u`, the state that weighs its epoch `E`, justifies the chain's
checkpoint at `E` when the current test passes. From epoch `anchorK` on, a link from the
current justified checkpoint of `u` justifies it. Before, the base holds it. -/
theorem RefSetting.justify_cur {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p r : List ChainStep}
    {u : BeaconState} (hsteps : steps = p ++ r) (hu : ChainRun hi p st₀ u)
    (hstk : stakeState hi steps st₀ (epochOf u) = some u) (hE2 : 2 ≤ epochOf u)
    (hj1 : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
      (toCp u.currentJustifiedCheckpoint))
    (hjc : jcOf u = true) :
    (anchorK st₀ ≤ epochOf u → EthCLLib.Proofs.FFG.Link (ffgChain hi steps st₀ vals)
      (toCp u.currentJustifiedCheckpoint) (cpOf st₀ steps (epochOf u))) ∧
    EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals) (cpOf st₀ steps (epochOf u)) := by
  have hordu := hu.stateCkptOrd S.hhi S.ord
  have hE := currentEpochOf_epochOf u
  by_cases hK : anchorK st₀ ≤ epochOf u
  · have hl := S.weigh_link hsteps hu hstk (e := currentEpochOf (pureState u)) (.inl rfl)
      (by rw [hE]; exact hK) (of_decide_eq_true hjc) u.currentJustifiedCheckpoint
      (fun i d hv hd => hv.source_cur S.hhi hu hd hE2)
      (by
        have h3 := UInt64.le_iff_toNat_le.mp hordu.2.2
        rw [previousEpochOf_epochOf] at h3
        omega)
      (S.onChain hj1)
    rw [hE] at hl
    exact ⟨fun _ => hl, .link hj1 hl⟩
  · -- Before `anchorK`, the weigh step is the one of the anchor epoch.
    have hle := hu.epoch_le S.hhi
    have hK' : anchorK st₀ = max (epochOf st₀ + 1) 2 := rfl
    have he0 : epochOf u = epochOf st₀ := by
      unfold epochOf at *
      omega
    exact ⟨fun h => absurd h hK, .base (mem_base_weigh (.inl he0)
      (mem_weighCps_cur hstk hE2 hjc))⟩

/-- The weigh step at `u`, the state that weighs its epoch `E`, justifies the chain's
checkpoint at `E - 1` when the previous test passes. From epoch `anchorK + 1` on, a link from
the previous justified checkpoint of `u` justifies it. Before, the base holds it. -/
theorem RefSetting.justify_prev {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p r : List ChainStep}
    {u : BeaconState} (hsteps : steps = p ++ r) (hu : ChainRun hi p st₀ u)
    (hstk : stakeState hi steps st₀ (epochOf u) = some u) (hE2 : 2 ≤ epochOf u)
    (hj2 : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
      (toCp u.previousJustifiedCheckpoint))
    (hprevLt : anchorK st₀ ≤ epochOf u →
      u.previousJustifiedCheckpoint.epoch.toNat + 2 ≤ epochOf u)
    (hjp : jpOf u = true) :
    (anchorK st₀ ≤ epochOf u - 1 → EthCLLib.Proofs.FFG.Link (ffgChain hi steps st₀ vals)
      (toCp u.previousJustifiedCheckpoint) (cpOf st₀ steps (epochOf u - 1))) ∧
    EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
      (cpOf st₀ steps (epochOf u - 1)) := by
  have hE := previousEpochOf_epochOf u
  have hK2 : 2 ≤ anchorK st₀ := Nat.le_max_right _ _
  by_cases hK : anchorK st₀ ≤ epochOf u - 1
  · have hl := S.weigh_link hsteps hu hstk (e := previousEpochOf (pureState u)) (.inr rfl)
      (by rw [hE]; exact hK) (of_decide_eq_true hjp) u.previousJustifiedCheckpoint
      (fun i d hv hd => hv.source_prev S.hhi hu hd (by omega))
      (by
        have := hprevLt (by omega)
        rw [hE]
        omega)
      (S.onChain hj2)
    rw [hE] at hl
    exact ⟨fun _ => hl, .link hj2 hl⟩
  · -- Before `anchorK + 1`, the weigh step is that of epoch `e₀`, `e₀ + 1`, or 2.
    have hle := hu.epoch_le S.hhi
    have hK' : anchorK st₀ = max (epochOf st₀ + 1) 2 := rfl
    have he0 : epochOf u = epochOf st₀ ∨ epochOf u = epochOf st₀ + 1 ∨
        (epochOf u = 2 ∧ epochOf st₀ ≤ 2) := by
      unfold epochOf at *
      omega
    exact ⟨fun h => absurd h hK, .base (mem_base_weigh he0
      (mem_weighCps_prev hstk hE2 hjp))⟩

end Links

/-! ## The invariant -/

section Inv
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The invariant of the refinement at a state `u`, read as a state of epoch `E`, with
`K = anchorK st₀`. A state of the run is read at its own epoch. A pull-up of the end state is
read at the next epoch, since its weigh step writes the fields that the next epoch holds.

- The two justified checkpoints are justified in the chain. The finalized checkpoint is
  finalized there, or it is a base checkpoint.
- Up to epoch `K`, both justified checkpoints are base checkpoints. In epoch `K + 1`, the
  previous one is a base checkpoint.
- From epoch `K` on, the previous justified epoch is at least two epochs back.
- Bit `k` of the justification bits records the checkpoint of epoch `E - 1 - k`. That
  checkpoint is justified, or its epoch is before `K`.
- Bit 0 records a link from the previous justified checkpoint to the checkpoint of `E - 1`,
  from epoch `K + 1` on. -/
structure RefInv (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState)
    (vals : List ValidatorIndex) (E : Nat) (u : BeaconState) : Prop where
  j1 : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
    (toCp u.currentJustifiedCheckpoint)
  j2 : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
    (toCp u.previousJustifiedCheckpoint)
  fin : EthCLLib.Proofs.FFG.Finalized (ffgChain hi steps st₀ vals)
      (toCp u.finalizedCheckpoint) ∨
    toCp u.finalizedCheckpoint ∈ (ffgChain hi steps st₀ vals).base
  early : E ≤ anchorK st₀ →
    toCp u.currentJustifiedCheckpoint ∈ (ffgChain hi steps st₀ vals).base ∧
    toCp u.previousJustifiedCheckpoint ∈ (ffgChain hi steps st₀ vals).base
  early' : E = anchorK st₀ + 1 →
    toCp u.previousJustifiedCheckpoint ∈ (ffgChain hi steps st₀ vals).base
  prevLt : anchorK st₀ ≤ E → u.previousJustifiedCheckpoint.epoch.toNat + 2 ≤ E
  bits : ∀ k, k < 4 → bitGet u.justificationBits k = true →
    EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
      (cpOf st₀ steps (E - 1 - k)) ∨ E - 1 - k < anchorK st₀
  b0 : bitGet u.justificationBits 0 = true → anchorK st₀ ≤ E - 1 →
    EthCLLib.Proofs.FFG.Link (ffgChain hi steps st₀ vals) (toCp u.previousJustifiedCheckpoint)
      (cpOf st₀ steps (E - 1))

/-- The anchor state meets the invariant: its checkpoints are base checkpoints, and its bits
record epochs before `K`. -/
theorem RefInv.anchor {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState}
    {vals : List ValidatorIndex} : RefInv hi steps st₀ vals (epochOf st₀) st₀ := by
  have hK : epochOf st₀ + 1 ≤ anchorK st₀ := Nat.le_max_left _ _
  have m1 := mem_base_anchor (hi := hi) (steps := steps) (st₀ := st₀) (vals := vals)
    (x := st₀.currentJustifiedCheckpoint) (by simp [anchorCps])
  have m2 := mem_base_anchor (hi := hi) (steps := steps) (st₀ := st₀) (vals := vals)
    (x := st₀.previousJustifiedCheckpoint) (by simp [anchorCps])
  have m3 := mem_base_anchor (hi := hi) (steps := steps) (st₀ := st₀) (vals := vals)
    (x := st₀.finalizedCheckpoint) (by simp [anchorCps])
  exact ⟨.base m1, .base m2, .inr m3, fun _ => ⟨m1, m2⟩, fun h => by omega, fun h => by omega,
    fun _ _ _ => .inr (by omega), fun _ h => by omega⟩

/-- A step that keeps the four checkpoint fields and the epoch keeps the invariant. -/
theorem RefInv.of_ckView {hi : Nat} {steps : List ChainStep} {st₀ : BeaconState}
    {vals : List ValidatorIndex} {u u' : BeaconState}
    (h : RefInv hi steps st₀ vals (epochOf u) u)
    (hck : ckView (pureState u') = ckView (pureState u)) (he : epochOf u' = epochOf u) :
    RefInv hi steps st₀ vals (epochOf u') u' := by
  simp only [ckView, Prod.mk.injEq] at hck
  obtain ⟨hp, hc, hf, hb⟩ := hck
  change u'.previousJustifiedCheckpoint = u.previousJustifiedCheckpoint at hp
  change u'.currentJustifiedCheckpoint = u.currentJustifiedCheckpoint at hc
  change u'.finalizedCheckpoint = u.finalizedCheckpoint at hf
  change u'.justificationBits = u.justificationBits at hb
  rw [he]
  obtain ⟨j1, j2, fin, early, early', prevLt, bits, b0⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hp, hc, hf, hb] <;> assumption

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- A `uint64` sum of a value and a small number, equal to a value no less than the first, has
no wrap. -/
theorem toNat_add_small {a b : UInt64} {k : Nat} (hk : k < 4) (h : a + UInt64.ofNat k = b)
    (hle : a.toNat ≤ b.toNat) : a.toNat + k = b.toNat := by
  have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hk (by decide))
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_add, hk'] at this
  have ha := a.toNat_lt
  by_cases hw : a.toNat + k < 2 ^ 64
  · rwa [Nat.mod_eq_of_lt hw] at this
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- The weigh step at `u`, after the first two epochs, takes the invariant at the epoch `E` of
`u` to the invariant at `E + 1` for the state `u'` it writes. The state `u` weighs `E`
(`stakeState`). The two roots that the step read are the chain's roots at `E` and `E - 1`.

- `justify_cur` or `justify_prev` justifies a new justified checkpoint.
- A new finalized checkpoint follows one of the four tests. Each test reads bits that the
  invariant ties to justified checkpoints and links, or it finalizes a base checkpoint.
- The new bits shift the old ones, with bits 0 and 1 from the two tests (`weighBits_get`). -/
theorem RefSetting.refInv_weigh {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p r : List ChainStep}
    {u u' : BeaconState} (hsteps : steps = p ++ r) (hu : ChainRun hi p st₀ u)
    (hstk : stakeState hi steps st₀ (epochOf u) = some u) (hE2 : 2 ≤ epochOf u)
    (h : RefInv hi steps st₀ vals (epochOf u) u) {pr cr : Root}
    (hp : u'.previousJustifiedCheckpoint = u.currentJustifiedCheckpoint)
    (hc' : u'.currentJustifiedCheckpoint =
      (if jcOf u = true then { epoch := currentEpochOf (pureState u), root := cr }
       else if jpOf u = true then { epoch := previousEpochOf (pureState u), root := pr }
       else u.currentJustifiedCheckpoint))
    (hbits' : u'.justificationBits = weighBits u.justificationBits (jpOf u) (jcOf u))
    (hf' : u'.finalizedCheckpoint = finalizeRules
      (weighBits u.justificationBits (jpOf u) (jcOf u)) u.previousJustifiedCheckpoint
      u.currentJustifiedCheckpoint u.finalizedCheckpoint (currentEpochOf (pureState u)))
    (hRc : jcOf u = true → cr = chainRoot st₀ steps (epochOf u))
    (hRp : jpOf u = true → pr = chainRoot st₀ steps (epochOf u - 1)) :
    RefInv hi steps st₀ vals (epochOf u + 1) u' := by
  have hordu := hu.stateCkptOrd S.hhi S.ord
  have hK : epochOf st₀ + 1 ≤ anchorK st₀ ∧ 2 ≤ anchorK st₀ :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hc3 := UInt64.le_iff_toNat_le.mp hordu.2.2
  rw [previousEpochOf_epochOf] at hc3
  have hp2 := UInt64.le_iff_toNat_le.mp hordu.2.1
  obtain ⟨g0, g1, g2, g3⟩ := weighBits_get u.justificationBits (jpOf u) (jcOf u)
  -- The two justifications, with the roots the step read.
  have Jc := fun hjc => S.justify_cur hsteps hu hstk hE2 h.j1 hjc
  have Jp := fun hjp => S.justify_prev hsteps hu hstk hE2 h.j2 h.prevLt hjp
  have Rc : jcOf u = true →
      toCp { epoch := currentEpochOf (pureState u), root := cr } = cpOf st₀ steps (epochOf u) :=
    fun hjc => by
      unfold toCp cpOf
      rw [hRc hjc, currentEpochOf_epochOf]
  have Rp : jpOf u = true →
      toCp { epoch := previousEpochOf (pureState u), root := pr } =
        cpOf st₀ steps (epochOf u - 1) := fun hjp => by
      unfold toCp cpOf
      rw [hRp hjp, previousEpochOf_epochOf]
  -- Before `K`, the weigh step is the one of the anchor epoch.
  have hle := hu.epoch_le S.hhi
  have hK' : anchorK st₀ = max (epochOf st₀ + 1) 2 := rfl
  have early0 : epochOf u < anchorK st₀ → epochOf u = epochOf st₀ := fun h' => by
    unfold epochOf at *
    omega
  -- The checkpoint of `E - 1` is justified, from epoch `K + 1` on, when bit 1 is set.
  have J1 : bitGet (weighBits u.justificationBits (jpOf u) (jcOf u)) 1 = true →
      anchorK st₀ ≤ epochOf u - 1 →
      EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
        (cpOf st₀ steps (epochOf u - 1)) ∧
      EthCLLib.Proofs.FFG.Link (ffgChain hi steps st₀ vals)
        (toCp u.previousJustifiedCheckpoint) (cpOf st₀ steps (epochOf u - 1)) := by
    intro hb1 hK1
    rw [g1, Bool.or_eq_true] at hb1
    rcases hb1 with hjp | hold
    · exact ⟨(Jp hjp).2, (Jp hjp).1 hK1⟩
    · refine ⟨?_, h.b0 hold hK1⟩
      rcases h.bits 0 (by omega) hold with hj | hlt'
      · exact hj
      · omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `j1`: the new current justified checkpoint.
    rw [hc']
    split
    · rename_i hjc
      rw [Rc hjc]
      exact (Jc hjc).2
    · split
      · rename_i hjp
        rw [Rp hjp]
        exact (Jp hjp).2
      · exact h.j1
  · rw [hp]
    exact h.j1
  · -- `fin`: the four finalization tests.
    rw [hf']
    rcases finalizeRules_cases (weighBits u.justificationBits (jpOf u) (jcOf u))
      u.previousJustifiedCheckpoint u.currentJustifiedCheckpoint u.finalizedCheckpoint
      (currentEpochOf (pureState u)) with h0 | ⟨h0, hb0, hb1, hd⟩ | ⟨h0, hb1, hb2, hd⟩
    · rw [h0]
      exact h.fin
    · rw [h0]
      by_cases hEK : epochOf u ≤ anchorK st₀
      · exact .inr (h.early hEK).1
      rw [g0] at hb0
      obtain ⟨hl, hjt⟩ := Jc hb0
      have hl' := hl (by omega)
      have hEc := currentEpochOf_epochOf u
      rcases hd with hd | ⟨hb2, hd⟩
      · have := toNat_add_small (k := 1) (by omega) hd (by rw [hEc]; omega)
        rw [hEc] at this
        exact .inl (.one h.j1 hjt (by simp only [cpOf, toCp]; omega) hl')
      · have := toNat_add_small (k := 2) (by omega) hd (by rw [hEc]; omega)
        rw [hEc] at this
        exact .inl (.two h.j1 (J1 hb1 (by omega)).1 hjt (by simp only [cpOf, toCp]; omega)
          (by simp only [cpOf, toCp]; omega) hl')
    · rw [h0]
      by_cases hEK : epochOf u ≤ anchorK st₀ + 1
      · rcases Nat.lt_or_ge (anchorK st₀) (epochOf u) with h' | h'
        · exact .inr (h.early' (by omega))
        · exact .inr (h.early h').2
      obtain ⟨hjt, hl⟩ := J1 hb1 (by omega)
      have hEc := currentEpochOf_epochOf u
      rcases hd with hd | ⟨hb3, hd⟩
      · have := toNat_add_small (k := 2) (by omega) hd (by rw [hEc]; omega)
        rw [hEc] at this
        exact .inl (.one h.j2 hjt (by simp only [cpOf, toCp]; omega) hl)
      · have := toNat_add_small (k := 3) (by omega) hd (by rw [hEc]; omega)
        rw [hEc] at this
        rw [g2] at hb2
        have hm : EthCLLib.Proofs.FFG.Justified (ffgChain hi steps st₀ vals)
            (cpOf st₀ steps (epochOf u - 2)) := by
          rcases h.bits 1 (by omega) hb2 with hj | hlt'
          · rwa [show epochOf u - 1 - 1 = epochOf u - 2 by omega] at hj
          · omega
        exact .inl (.two h.j2 hm hjt (by simp only [cpOf, toCp]; omega)
          (by simp only [cpOf, toCp]; omega) hl)
  · -- `early`: before `K`, the new checkpoints are base checkpoints.
    intro hEK
    have he0 := early0 (by omega)
    refine ⟨?_, by rw [hp]; exact (h.early (by omega)).1⟩
    rw [hc']
    split
    · rename_i hjc
      rw [Rc hjc]
      exact mem_base_weigh (.inl he0) (mem_weighCps_cur hstk hE2 hjc)
    · split
      · rename_i hjp
        rw [Rp hjp]
        exact mem_base_weigh (.inl he0) (mem_weighCps_prev hstk hE2 hjp)
      · exact (h.early (by omega)).1
  · intro hEK
    rw [hp]
    exact (h.early (by omega)).1
  · intro _
    rw [hp]
    omega
  · -- `bits`: the shift, and the two tests.
    intro k hk hbk
    rw [hbits'] at hbk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [g0] at hbk
      rw [show epochOf u + 1 - 1 - 0 = epochOf u by omega]
      exact .inl (Jc hbk).2
    · rw [show epochOf u + 1 - 1 - 1 = epochOf u - 1 by omega]
      rw [g1, Bool.or_eq_true] at hbk
      rcases hbk with hjp | hold
      · exact .inl (Jp hjp).2
      · rcases h.bits 0 (by omega) hold with hj | hlt'
        · exact .inl hj
        · exact .inr (by omega)
    · rw [g2] at hbk
      rw [show epochOf u + 1 - 1 - 2 = epochOf u - 1 - 1 by omega]
      exact h.bits 1 (by omega) hbk
    · rw [g3] at hbk
      rw [show epochOf u + 1 - 1 - 3 = epochOf u - 1 - 2 by omega]
      exact h.bits 2 (by omega) hbk
  · -- `b0`: bit 0 is the current test, a link from the old current checkpoint.
    intro hb0 hK0
    rw [hbits', g0] at hb0
    rw [hp, show epochOf u + 1 - 1 = epochOf u by omega]
    exact (Jc hb0).1 (by omega)

/-- A slot step at the end of epoch `E` keeps the invariant. In the first two epochs the four
fields stay. After them, the weigh step on `slotWrite u` writes them (`refInv_weigh`). Its two
root reads give the chain's roots (`weigh_root`). -/
theorem RefSetting.refInv_boundary {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {p q : List ChainStep}
    {u u' : BeaconState} (hsteps : steps = p ++ .slot :: q) (hu : ChainRun hi p st₀ u)
    (hstep : SlotStep u u') (hlt : u.slot.toNat + 1 < 2 ^ 64)
    (hb : (u.slot.toNat + 1) % slotsPerEpoch = 0)
    (h : RefInv hi steps st₀ vals (epochOf u) u) :
    RefInv hi steps st₀ vals (epochOf u') u' := by
  have hK : epochOf st₀ + 1 ≤ anchorK st₀ ∧ 2 ≤ anchorK st₀ :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hE' : epochOf u' = epochOf u + 1 := by
    unfold epochOf
    rw [hstep.slot hlt]
    exact succ_div_of_mod_eq hb
  rcases hstep.weigh hlt hb with ⟨hE1, hck⟩ | ⟨hE2, pr, cr, hw⟩
  · -- The first two epochs: the four fields stay, and the epoch advances.
    simp only [ckView, Prod.mk.injEq] at hck
    obtain ⟨hp, hc, hf, hbits⟩ := hck
    change u'.previousJustifiedCheckpoint = u.previousJustifiedCheckpoint at hp
    change u'.currentJustifiedCheckpoint = u.currentJustifiedCheckpoint at hc
    change u'.finalizedCheckpoint = u.finalizedCheckpoint at hf
    change u'.justificationBits = u.justificationBits at hbits
    change epochOf u ≤ 1 at hE1
    have hordu := hu.stateCkptOrd S.hhi S.ord
    have hc3 := UInt64.le_iff_toNat_le.mp hordu.2.2
    rw [previousEpochOf_epochOf] at hc3
    have hp2 := UInt64.le_iff_toNat_le.mp hordu.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hp, hc, hf, hbits, hE']
    · exact h.j1
    · exact h.j2
    · exact h.fin
    · exact fun _ => h.early (by omega)
    · intro h'
      omega
    · intro h'
      omega
    · exact fun k _ _ => .inr (by omega)
    · intro _ h'
      omega
  · change 2 ≤ epochOf u at hE2
    obtain ⟨hp, hc, hbits, hf, hrp, hrc⟩ := hw
    rw [hE']
    refine S.refInv_weigh hsteps hu (stakeState_of_weigh S.hhi ⟨p, q, hsteps, hu, hb, rfl⟩) hE2 h
      hp hc hbits hf (fun hjc => ?_) (fun hjp => ?_)
    · have hr := S.weigh_root hsteps hu hb (.inr (currentEpochOf_epochOf u))
        (by rw [currentEpochOf_epochOf]; omega) (hrc hjc)
      rwa [currentEpochOf_epochOf] at hr
    · have hr := S.weigh_root hsteps hu hb (.inl (by rw [previousEpochOf_epochOf]; omega))
        (by rw [previousEpochOf_epochOf]; omega) (hrp hjp)
      rwa [previousEpochOf_epochOf] at hr

/-- Each step of the run keeps the invariant. A block step and a slot step inside an epoch keep
the four fields and the epoch. A slot step at the end of an epoch is `refInv_boundary`. -/
theorem RefSetting.refInv_run {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    ∀ {p : List ChainStep}, steps = p ++ q → ChainRun hi p st₀ u →
      RefInv hi steps st₀ vals (epochOf u) u → RefInv hi steps st₀ vals (epochOf w) w := by
  induction h with
  | nil => exact fun _ _ h => h
  | @slot rest x y z hlt hstep hrest ih =>
    intro p hs hp hinv
    have hlt' : x.slot.toNat < hi := hlt
    have hx : x.slot.toNat + 1 < 2 ^ 64 := by
      have := S.hhi
      omega
    refine ih (p := p ++ [.slot]) (by rw [hs]; simp) (hp.append (.slot hlt hstep (.nil _))) ?_
    by_cases hb : (x.slot.toNat + 1) % slotsPerEpoch = 0
    · exact S.refInv_boundary hs hp hstep hx hb hinv
    · refine hinv.of_ckView (hstep.ckView_of_not_boundary hx hb) ?_
      unfold epochOf
      rw [hstep.slot hx]
      exact succ_div_of_mod_ne hb
  | @block rest x y z sb v hstep hrest ih =>
    intro p hs hp hinv
    refine ih (p := p ++ [.block sb v]) (by rw [hs]; simp)
      (hp.append (.block sb v hstep (.nil _))) ?_
    have e := processBlock_frame_ord hstep.2.1
    simp only [ordView, Prod.mk.injEq] at e
    refine hinv.of_ckView e.1 ?_
    unfold epochOf
    rw [hstep.slot.1]

/-- The root that a pull-up of the end state reads for epoch `n` is the chain's root at `n`,
for `n` the current or the previous epoch. The read runs on the end state itself, and the run
has no block after it. -/
theorem RefSetting.end_root {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {n : Epoch} {r : Root}
    (hn : n.toNat ≤ epochOf st) (h1 : 1 ≤ n.toNat)
    (h : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun)
      (pureState st) n) st = .ok (r, st)) :
    r = chainRoot st₀ steps n.toNat := by
  have hinv := S.run.rootsInv S.hw S.hhi S.val S.roots.rootsInv
  rw [List.nil_append] at hinv
  replace h := getBlockRoot_runPure_ok h
  have hroot := hinv.read_of rfl rfl h
  -- The epoch is at most the epoch of the state, so its first slot fits a `uint64`.
  have hfit : n.toNat * slotsPerEpoch < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_right _ hn)
      (Nat.div_mul_le_self _ _)) st.slot.toNat_lt
  rw [epochStart_toNat _ hfit] at hroot
  rw [hroot, chainRoot_pos _ _ h1]

/-- A pull-up of the end state keeps the invariant, read at the next epoch. In the first two
epochs `process_justification_and_finalization` returns the state as it is. After them, the
weigh step runs on the end state, which weighs its own epoch (`stakeState_end`), and reads the
chain's roots (`end_root`). -/
theorem RefSetting.refInv_pullup {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals)
    (h : RefInv hi steps st₀ vals (epochOf st) st) {w : BeaconState}
    (hjf : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) st = .ok ((), w)) :
    w = st ∨ RefInv hi steps st₀ vals (epochOf st + 1) w := by
  by_cases hg : currentEpochOf (pureState st) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1
  · rw [processJustificationAndFinalization_run_eq, if_pos hg] at hjf
    injection hjf with hjf
    injection hjf with _ hw
    exact .inl hw.symm
  · have hE := currentEpochOf_epochOf st
    have hE2 : 2 ≤ epochOf st := by
      have hg' : ¬ (currentEpochOf (pureState st)).toNat ≤ 1 := fun h' =>
        hg (UInt64.le_iff_toNat_le.mpr (by simpa [EthCLSpecs.Heze.Const.genesisEpoch] using h'))
      omega
    -- The five reads succeed, so the weigh step runs on `totBal` and `tgtBal`.
    obtain ⟨prevIdx, currIdx, tot, prev, curr, h1, h2, h3, h4, h5, hjf⟩ :=
      processJustificationAndFinalization_run_ok hjf hg
    have et : totBal st = tot := totBal_of_ok h3
    have etp : tgtBal st (previousEpochOf (pureState st)) = prev := tgtBal_of_ok h1 h4
    have etc : tgtBal st (currentEpochOf (pureState st)) = curr := tgtBal_of_ok h2 h5
    subst et etp etc
    obtain ⟨pr, cr, hp, hc, hbits, hf, hrp, hrc⟩ :=
      weighJustificationAndFinalization_run_ok _ _ _ _ _ hjf
    refine .inr (S.refInv_weigh (p := steps) (r := []) (List.append_nil _).symm S.run
      (stakeState_end S.hhi S.run) hE2 h hp hc hbits hf (fun hjc => ?_) (fun hjp => ?_))
    · have hr := S.end_root (n := currentEpochOf (pureState st)) (by omega) (by omega) (hrc hjc)
      rwa [hE] at hr
    · have hP := previousEpochOf_epochOf st
      have hr := S.end_root (n := previousEpochOf (pureState st)) (by omega) (by omega)
        (hrp hjp)
      rwa [hP] at hr

end Inv

/-! ## The refinement -/

section Refines
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A chain run refines Casper FFG. Its abstract chain matches the run (`ChainMatches`). The
two justified checkpoints of the end state are justified in the chain. The finalized
checkpoint is finalized there, or it is a base checkpoint.

The premises are those of `RefSetting`: the combine-width law, a run below the slot bound with
validated blocks of nonzero state root, an anchor state that records its own block roots and
whose checkpoints are on that history and ordered, `2 * SLOTS_PER_EPOCH` at most
`SLOTS_PER_HISTORICAL_ROOT`, `RunTotals` at every state of the run, and a list `vals` without
duplicates that holds every registry index of every state of the run. -/
theorem chain_refines {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) :
    ∃ c, ChainMatches hi steps st₀ vals c ∧
      EthCLLib.Proofs.FFG.Justified c (toCp st.currentJustifiedCheckpoint) ∧
      EthCLLib.Proofs.FFG.Justified c (toCp st.previousJustifiedCheckpoint) ∧
      (EthCLLib.Proofs.FFG.Finalized c (toCp st.finalizedCheckpoint) ∨
        toCp st.finalizedCheckpoint ∈ c.base) := by
  have hinv := S.refInv_run S.run (p := []) rfl (.nil _) RefInv.anchor
  exact ⟨ffgChain hi steps st₀ vals,
    ffgChain_matches S.cps S.ord (S.run.blocks_slot_ge S.hhi), hinv.j1, hinv.j2, hinv.fin⟩

/-- The pull-up of the end state refines Casper FFG too. `process_justification_and_finalization`
on the end state `st` gives `w`. Then the two justified checkpoints of `w` are justified in the
chain of the run, and its finalized checkpoint is finalized there or a base checkpoint. The
weigh step of the pull-up weighs the epoch of `st` with the stake of `st`. The chain holds that
stake at an epoch with no weigh state. -/
theorem chain_refines_pullup {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {w : BeaconState}
    (hjf : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) st = .ok ((), w)) :
    ∃ c, ChainMatches hi steps st₀ vals c ∧
      EthCLLib.Proofs.FFG.Justified c (toCp w.currentJustifiedCheckpoint) ∧
      EthCLLib.Proofs.FFG.Justified c (toCp w.previousJustifiedCheckpoint) ∧
      (EthCLLib.Proofs.FFG.Finalized c (toCp w.finalizedCheckpoint) ∨
        toCp w.finalizedCheckpoint ∈ c.base) := by
  have hinv := S.refInv_run S.run (p := []) rfl (.nil _) RefInv.anchor
  have hm := ffgChain_matches (hi := hi) (vals := vals) S.cps S.ord (S.run.blocks_slot_ge S.hhi)
  rcases S.refInv_pullup hinv hjf with rfl | hw
  · exact ⟨_, hm, hinv.j1, hinv.j2, hinv.fin⟩
  · exact ⟨_, hm, hw.j1, hw.j2, hw.fin⟩

end Refines

end EthCLSpecs.Proofs.Heze
