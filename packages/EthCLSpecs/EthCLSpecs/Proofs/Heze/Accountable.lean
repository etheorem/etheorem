import EthCLSpecs.Proofs.Heze.ChainAgree
import EthCLSpecs.Proofs.Heze.RefDrift
import EthCLSpecs.Proofs.Heze.VoteValid
import EthCLSpecs.Proofs.Heze.AttesterSlashing

/-!
# `EthCLSpecs.Proofs.Heze.Accountable`: conflicting checkpoints of honest nodes leave slashing evidence

Two honest nodes start at one anchor. One node justifies a checkpoint `j`, and the other
finalizes a checkpoint `f`. The two conflict: the walk of `getCheckpointBlock` from `j` does
not reach `f`. Then a root collision exists, or there is slashing evidence
(`honestNodes_accountable`). The evidence is a list of pairs of indexed attestations. Each pair
passes `is_slashable_attestation_data` and has one attestation valid on a state of each chain.
The common validators of the pairs hold a third of the fork-point stake, less `5/3` of the
measured drift of the two chains.

## The evidence

`SlashingEvidence` states the three facts. A pair has one attestation on each chain, in either
order. A surround vote has a direction, and the surrounding link can be on either chain.
`SlashingEvidence.valid_at` moves the validity of an attestation to a state with the same
public keys, fork, and genesis validators root. `SlashingEvidence.accepted` takes a state where
both attestations of a pair are valid and a common validator is slashable. On that state,
`process_attester_slashing` accepts the pair.

## The proof

The checkpoint sources of the two stores give two chain runs from the anchor state
(`CkptInv`). The blocks of each run lie on an ancestor path of its store. The FFG refinement
gives a chain for each run. Chain 1 finalizes `f`, and chain 2 justifies `j` (`chain_refines`,
`chain_refines_pullup`). The two runs split at their fork point `st₀` (`ForkAt`). Then the premises of
`ffg_accountable_safety` hold:

- `f` is not on the chain of `j`, since the checkpoints conflict (`conflicting_not_onChain`).
- The two chains share their base (`ForkAt.commonBase`), and agree below a shared root
  (`ffgChain_agree`).
- Each chain stays within its measured drift of `st₀` from the epoch of `st₀` on
  (`ForkAt.stakeClose`).

Each validator of the slashable list cast a vote on each chain. Each vote is a placed vote of
its run. The indexed attestation of each vote is valid on a state of its run
(`RunVote.indexed`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure)
open EthCLLib.Spec
open EthCLLib.Proofs.FFG (stakeSum)
open EthCLSpecs.Heze (Preset Config BeaconState BeaconBlock AttestationData IndexedAttestation
  AttesterSlashing ValidatorIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## The evidence -/

section Evidence
variable [Preset] [HasherTag] [CryptoBackend]

/-- The indexed attestation is valid on a state of the chain. -/
def ValidOn (chain : BeaconState → Prop) (ia : IndexedAttestation) : Prop :=
  ∃ u, chain u ∧ EthCLSpecs.Heze.isValidIndexedAttestation (pureState u) ia = .ok true

/-- The validators in both attestations of a pair, as a list without duplicates. -/
def commonOf (pairs : List (IndexedAttestation × IndexedAttestation)) : List ValidatorIndex :=
  regVals.filter fun v => pairs.any fun p =>
    p.1.attestingIndices.toArray.contains v && p.2.attestingIndices.toArray.contains v

/-- **Slashing evidence.** Every pair passes the slashing test. Every pair has one attestation
valid on a state of each chain, in either order. Under the stake of `st₀`, the common validators
hold a third of the total of `st₀`, less `5/3` of the two drifts. -/
def SlashingEvidence (st₀ : BeaconState) (chain₁ chain₂ : BeaconState → Prop) (d₁ d₂ : Nat)
    (pairs : List (IndexedAttestation × IndexedAttestation)) : Prop :=
  (∀ p ∈ pairs, EthCLSpecs.Heze.isSlashableAttestationData p.1.data p.2.data = true) ∧
  (∀ p ∈ pairs, (ValidOn chain₁ p.1 ∧ ValidOn chain₂ p.2) ∨
    (ValidOn chain₂ p.1 ∧ ValidOn chain₁ p.2)) ∧
  3 * activeStake st₀ (commonOf pairs) + 5 * (d₁ + d₂) ≥ totalOf st₀

/-- An attestation valid on `u` is valid on every state with the public keys, the fork, and the
genesis validators root of `u`. -/
theorem SlashingEvidence.valid_at {u st : BeaconState}
    (hk : keyView (pureState u) = keyView (pureState st)) {ia : IndexedAttestation}
    (h : EthCLSpecs.Heze.isValidIndexedAttestation (pureState u) ia = .ok true) :
    EthCLSpecs.Heze.isValidIndexedAttestation (pureState st) ia = .ok true := by
  rw [← isValidIndexedAttestation_of_keyView hk ia]
  exact h

variable [Config]

/-- Take a state where both attestations of a pair are valid and a common validator is
slashable. On that state, no assert of `process_attester_slashing` rejects the pair. -/
theorem SlashingEvidence.accepted (hq : QsortMem) (st : BeaconState)
    (p : IndexedAttestation × IndexedAttestation)
    (hs : EthCLSpecs.Heze.isSlashableAttestationData p.1.data p.2.data = true)
    (h₁ : EthCLSpecs.Heze.isValidIndexedAttestation (pureState st) p.1 = .ok true)
    (h₂ : EthCLSpecs.Heze.isValidIndexedAttestation (pureState st) p.2 = .ok true)
    (hi : ∃ i ∈ p.1.attestingIndices.toArray, i ∈ p.2.attestingIndices.toArray ∧
      ∃ hlt : i.toNat < st.validators.toArray.size,
        EthCLSpecs.Heze.isSlashableValidator st.validators.toArray[i.toNat]
          (EthCLSpecs.Heze.currentEpochOf (pureState st)) = true)
    (d : String) :
    runPure (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun)
      { attestation1 := p.1, attestation2 := p.2 : AttesterSlashing }) st ≠ .error (.assert d) := by
  obtain ⟨a₁, a₂⟩ := p
  exact processAttesterSlashing_run_not_assert hq st ⟨a₁, a₂⟩ hs h₁ h₂ hi d

end Evidence

/-! ## From slashable votes to evidence -/

section Votes
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [HasherTag] [Config] [CryptoBackend] in
/-- A validator of `regVals` in both attestations of a pair is a common validator. -/
theorem mem_commonOf {pairs : List (IndexedAttestation × IndexedAttestation)}
    {v : ValidatorIndex} (hv : v ∈ regVals) {p : IndexedAttestation × IndexedAttestation}
    (hp : p ∈ pairs) (h₁ : v ∈ p.1.attestingIndices.toArray)
    (h₂ : v ∈ p.2.attestingIndices.toArray) : v ∈ commonOf pairs := by
  unfold commonOf
  refine List.mem_filter.mpr ⟨hv, List.any_eq_true.mpr ⟨p, hp, ?_⟩⟩
  simp only [Bool.and_eq_true, Array.contains_iff_mem]
  exact ⟨h₁, h₂⟩

/-- Take one slashable pair of votes of `v`, with one vote on each chain. It gives a pair of
indexed attestations that passes the slashing test. Each attestation is valid on a state of its
run, and both hold `v`. Otherwise two attestation data share a root. -/
theorem pair_of_slashable (hq : QsortMem) (hcol : ¬ HtrCollision AttestationData) {hi : Nat}
    {A : BeaconState} {steps₁ steps₂ : List ChainStep}
    {c₁ c₂ : EthCLLib.Proofs.FFG.Chain ValidatorIndex EthCLSpecs.Heze.Root}
    (hm₁ : ChainMatches hi steps₁ A regVals c₁) (hm₂ : ChainMatches hi steps₂ A regVals c₂)
    {v : ValidatorIndex} (hsl : EthCLLib.Proofs.FFG.Slashable c₁.votes c₂.votes v) :
    v ∈ regVals ∧ ∃ p : IndexedAttestation × IndexedAttestation,
      EthCLSpecs.Heze.isSlashableAttestationData p.1.data p.2.data = true ∧
      ((ValidOn (OnRun hi A steps₁) p.1 ∧ ValidOn (OnRun hi A steps₂) p.2) ∨
        (ValidOn (OnRun hi A steps₂) p.1 ∧ ValidOn (OnRun hi A steps₁) p.2)) ∧
      v ∈ p.1.attestingIndices.toArray ∧ v ∈ p.2.attestingIndices.toArray := by
  obtain ⟨x, hx, y, hy, hxv, hyv, hcase⟩ := hsl
  obtain ⟨hxval, d₁, hv₁, hxs, hxt⟩ := (hm₁.votes x).mp hx
  obtain ⟨-, d₂, hv₂, hys, hyt⟩ := (hm₂.votes y).mp hy
  rw [hxv] at hxval hv₁
  rw [hyv] at hv₂
  refine ⟨hxval, ?_⟩
  -- Find the indexed attestation of each vote, valid on a state of its run.
  obtain ⟨s₁, s₁', sb₁, b₁, u₁, ia₁, hs₁, hr₁, hd₁, hm₁', hok₁⟩ := hv₁.indexed hq
  obtain ⟨s₂, s₂', sb₂, b₂, u₂, ia₂, hs₂, hr₂, hd₂, hm₂', hok₂⟩ := hv₂.indexed hq
  have hon₁ : ValidOn (OnRun hi A steps₁) ia₁ := ⟨u₁, ⟨s₁, _, hs₁, hr₁⟩, hok₁⟩
  have hon₂ : ValidOn (OnRun hi A steps₂) ia₂ := ⟨u₂, ⟨s₂, _, hs₂, hr₂⟩, hok₂⟩
  -- Check the slashing test of the two data.
  have ep_eq : ∀ a b : EthCLSpecs.Heze.Epoch, a.toNat = b.toNat → a = b :=
    fun a b h => UInt64.toNat_inj.mp h
  rcases hcase with ⟨-, he, hne⟩ | ⟨-, hs, ht⟩ | ⟨-, hs, ht⟩
  · -- A double vote: two different targets at one epoch.
    rw [hxt, hyt] at he hne
    have hte : d₁.target.epoch = d₂.target.epoch := ep_eq _ _ he
    have hdne : d₁ ≠ d₂ := fun h => hne (by rw [h])
    rcases isSlashableAttestationData_of_ne d₁ d₂ hdne hte with hc | hsl
    · exact absurd hc hcol
    · refine ⟨(ia₁, ia₂), by rw [hd₁, hd₂]; exact hsl, .inl ⟨hon₁, hon₂⟩, hm₁', hm₂'⟩
  · -- The vote of chain 1 surrounds the vote of chain 2.
    rw [hxs, hys] at hs
    rw [hxt, hyt] at ht
    refine ⟨(ia₁, ia₂), ?_, .inl ⟨hon₁, hon₂⟩, hm₁', hm₂'⟩
    rw [hd₁, hd₂, isSlashableAttestationData_iff]
    exact .inr ⟨UInt64.lt_iff_toNat_lt.mpr hs, UInt64.lt_iff_toNat_lt.mpr ht⟩
  · -- The vote of chain 2 surrounds the vote of chain 1.
    rw [hxs, hys] at hs
    rw [hxt, hyt] at ht
    refine ⟨(ia₂, ia₁), ?_, .inr ⟨hon₂, hon₁⟩, hm₂', hm₁'⟩
    rw [hd₁, hd₂, isSlashableAttestationData_iff]
    exact .inr ⟨UInt64.lt_iff_toNat_lt.mpr hs, UInt64.lt_iff_toNat_lt.mpr ht⟩

/-- Every validator of a list with slashable votes gives a pair. The pairs pass the slashing
test, have one attestation valid on a state of each run, and hold every validator of the list
in common. -/
theorem pairs_of_slashable (hq : QsortMem) (hcol : ¬ HtrCollision AttestationData) {hi : Nat}
    {A : BeaconState} {steps₁ steps₂ : List ChainStep}
    {c₁ c₂ : EthCLLib.Proofs.FFG.Chain ValidatorIndex EthCLSpecs.Heze.Root}
    (hm₁ : ChainMatches hi steps₁ A regVals c₁) (hm₂ : ChainMatches hi steps₂ A regVals c₂) :
    ∀ X : List ValidatorIndex, (∀ v ∈ X, EthCLLib.Proofs.FFG.Slashable c₁.votes c₂.votes v) →
      ∃ pairs : List (IndexedAttestation × IndexedAttestation),
        (∀ p ∈ pairs, EthCLSpecs.Heze.isSlashableAttestationData p.1.data p.2.data = true) ∧
        (∀ p ∈ pairs, (ValidOn (OnRun hi A steps₁) p.1 ∧ ValidOn (OnRun hi A steps₂) p.2) ∨
          (ValidOn (OnRun hi A steps₂) p.1 ∧ ValidOn (OnRun hi A steps₁) p.2)) ∧
        ∀ v ∈ X, v ∈ commonOf pairs
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | v :: X, hX => by
    obtain ⟨pairs, hs, hv, hc⟩ := pairs_of_slashable hq hcol hm₁ hm₂ X
      fun w hw => hX w (List.mem_cons_of_mem _ hw)
    obtain ⟨hreg, p, hps, hpv, h₁, h₂⟩ :=
      pair_of_slashable hq hcol hm₁ hm₂ (hX v List.mem_cons_self)
    refine ⟨p :: pairs, fun q hq' => ?_, fun q hq' => ?_, fun w hw => ?_⟩
    · rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hps
      · exact hs q hq'
    · rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hpv
      · exact hv q hq'
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact mem_commonOf hreg List.mem_cons_self h₁ h₂
      · -- A common validator of the old pairs stays common.
        have hw' := hc w hw
        unfold commonOf at hw' ⊢
        obtain ⟨hwr, hany⟩ := List.mem_filter.mp hw'
        refine List.mem_filter.mpr ⟨hwr, ?_⟩
        rw [List.any_cons, hany, Bool.or_true]

end Votes

/-! ## The chains of the checkpoint sources -/

section Sources
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

omit [Config] [CryptoBackend] in
/-- A store run of `s`: a validated chain run from the anchor state `A` along an ancestor path
of `s`, empty or ending with a block step. The checkpoint sources of `s` come from store
runs. -/
def StoreRun (A : BeaconState) (a : BeaconBlock) (s : EthCLSpecs.Heze.Store map)
    (steps : List ChainStep) : Prop :=
  ∃ (k : EthCLSpecs.Heze.Root) (v : BeaconState), ChainRun (2 ^ 64 - 1) steps A v ∧
    AncestorPath a s k (blocksOf steps) ∧ ValidatedSteps steps ∧ EndsAtBlock steps

omit [Config] [CryptoBackend] in
/-- The totals premise of a store. Every state on a prefix of a store run of `s` meets
`RunTotals`. A store run ends at a stored block, so that block bounds its end slot. -/
def StoreTotals (A : BeaconState) (a : BeaconBlock) (s : EthCLSpecs.Heze.Store map) : Prop :=
  ∀ p q u, StoreRun A a s (p ++ q) → ChainRun (2 ^ 64 - 1) p A u → RunTotals u

include hw in
/-- The premises of the refinement for a validated run from the anchor state, over `regVals`.
Every state on a prefix of the run meets `RunTotals`. -/
theorem refSetting_of {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hval : ValidatedSteps steps)
    (hroots : AnchorRoots A) (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (hsphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (htot : ∀ s₁ s₂ u, steps = s₁ ++ s₂ → ChainRun (2 ^ 64 - 1) s₁ A u → RunTotals u) :
    RefSetting (2 ^ 64 - 1) steps A v regVals :=
  ⟨hw, Nat.le_refl _, hrun, hval, hroots, hcps, hord, hsphr, htot,
    regVals_nodup, fun _ _ u _ _ _ hi => mem_regVals u hi⟩

/-- The checkpoints of a state of a run are at or before the epoch of the run. -/
theorem ckpt_epoch_le {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hord : StateCkptOrd A) :
    v.finalizedCheckpoint.epoch.toNat ≤ epochOf v ∧
      v.currentJustifiedCheckpoint.epoch.toNat ≤ epochOf v := by
  obtain ⟨h1, h2, h3⟩ := hrun.stateCkptOrd (Nat.le_refl _) hord
  rw [UInt64.le_iff_toNat_le] at h1 h2 h3
  rw [previousEpochOf_toNat_sub] at h3
  unfold epochOf
  generalize v.slot.toNat / slotsPerEpoch = E at h3 ⊢
  omega

/-- The checkpoints that `process_justification_and_finalization` writes on a state of a run
are at or before the epoch of the run. -/
theorem pullup_epoch_le {steps : List ChainStep} {A v w : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hord : StateCkptOrd A)
    (hjf : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) v = .ok ((), w)) :
    w.finalizedCheckpoint.epoch.toNat ≤ epochOf v ∧
      w.currentJustifiedCheckpoint.epoch.toNat ≤ epochOf v := by
  obtain ⟨h1, h2, h3, -⟩ := processJustificationAndFinalization_run_ord v w
    (hrun.stateCkptOrd (Nat.le_refl _) hord) hjf
  rw [UInt64.le_iff_toNat_le] at h1 h2
  unfold epochOf
  omega

include hw in
/-- **The finalized checkpoint of a store.** A finalized checkpoint after the anchor epoch comes
from a validated run from the anchor state. The blocks of the run form an ancestor path of the
store, and the run is a store run. The chain of the run finalizes the checkpoint, or holds it
in its base. The epoch of the checkpoint is at most the epoch of the run. -/
theorem finalized_source {A : BeaconState} {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    {f : EthCLSpecs.Heze.Checkpoint} (hsrc : CheckpointSource A a s .finalized f)
    (hfA : (EthCLSpecs.Heze.currentEpochOf (pureState A)).toNat < f.epoch.toNat)
    (hroots : AnchorRoots A) (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (hsphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (htot : StoreTotals A a s) :
    ∃ (k : EthCLSpecs.Heze.Root) (steps : List ChainStep) (v : BeaconState),
      ChainRun (2 ^ 64 - 1) steps A v ∧ AncestorPath a s k (blocksOf steps) ∧
      f.epoch.toNat ≤ epochOf v ∧
      (EthCLLib.Proofs.FFG.Finalized (ffgChain (2 ^ 64 - 1) steps A regVals) (toCp f) ∨
        toCp f ∈ (ffgChain (2 ^ 64 - 1) steps A regVals).base) ∧ StoreRun A a s steps := by
  rcases hsrc with hf | ⟨k, steps, v, hrun, hpath, hval, hend, hc⟩
  · rw [hf] at hfA
    exact absurd hfA (Nat.lt_irrefl _)
  have hsr : StoreRun A a s steps := ⟨k, v, hrun, hpath, hval, hend⟩
  have S := refSetting_of hw hrun hval hroots hcps hord hsphr
    fun s₁ s₂ u he hu => htot s₁ s₂ u (he ▸ hsr) hu
  -- The refinement invariant at the end of the run, as in `chain_refines`.
  have hinv := S.refInv_run S.run (p := []) rfl (.nil _) RefInv.anchor
  rcases hc with hc | ⟨w, hjf, hc⟩
  · change f = v.finalizedCheckpoint at hc
    subst hc
    exact ⟨k, steps, v, hrun, hpath, (ckpt_epoch_le hrun hord).1, hinv.fin, hsr⟩
  · change f = w.finalizedCheckpoint at hc
    subst hc
    refine ⟨k, steps, v, hrun, hpath, (pullup_epoch_le hrun hord hjf).1, ?_, hsr⟩
    rcases S.refInv_pullup hinv hjf with rfl | hw'
    · exact hinv.fin
    · exact hw'.fin

include hw in
/-- **The justified checkpoint of a store.** A justified checkpoint after the anchor epoch comes
from a validated run from the anchor state. The blocks of the run form an ancestor path of the
store, and the run is a store run. The chain of the run justifies the checkpoint. The epoch of
the checkpoint is at most the epoch of the run. -/
theorem justified_source {A : BeaconState} {a : BeaconBlock} {s : EthCLSpecs.Heze.Store map}
    {j : EthCLSpecs.Heze.Checkpoint} (hsrc : CheckpointSource A a s .justified j)
    (hjA : (EthCLSpecs.Heze.currentEpochOf (pureState A)).toNat < j.epoch.toNat)
    (hroots : AnchorRoots A) (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (hsphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (htot : StoreTotals A a s) :
    ∃ (k : EthCLSpecs.Heze.Root) (steps : List ChainStep) (v : BeaconState),
      ChainRun (2 ^ 64 - 1) steps A v ∧ AncestorPath a s k (blocksOf steps) ∧
      j.epoch.toNat ≤ epochOf v ∧
      EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) (toCp j) ∧
      StoreRun A a s steps := by
  rcases hsrc with hj | ⟨k, steps, v, hrun, hpath, hval, hend, hc⟩
  · rw [hj] at hjA
    exact absurd hjA (Nat.lt_irrefl _)
  have hsr : StoreRun A a s steps := ⟨k, v, hrun, hpath, hval, hend⟩
  have S := refSetting_of hw hrun hval hroots hcps hord hsphr
    fun s₁ s₂ u he hu => htot s₁ s₂ u (he ▸ hsr) hu
  have hinv := S.refInv_run S.run (p := []) rfl (.nil _) RefInv.anchor
  rcases hc with hc | ⟨w, hjf, hc⟩
  · change j = v.currentJustifiedCheckpoint at hc
    subst hc
    exact ⟨k, steps, v, hrun, hpath, (ckpt_epoch_le hrun hord).2, hinv.j1, hsr⟩
  · change j = w.currentJustifiedCheckpoint at hc
    subst hc
    refine ⟨k, steps, v, hrun, hpath, (pullup_epoch_le hrun hord hjf).2, ?_, hsr⟩
    rcases S.refInv_pullup hinv hjf with rfl | hw'
    · exact hinv.j1
    · exact hw'.j1

end Sources

/-! ## The theorem -/

section Main
open EthCLLib.Proofs (LawfulFcMap)

variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]
  [LawfulFcMap map EthCLSpecs.Heze.Root]
  [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
    EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

omit [CryptoBackend] [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability] in
/-- The anchor store holds the anchor block at its root. -/
theorem getForkchoiceStore_anchor (A : BeaconState) (a : BeaconBlock)
    (s0 : EthCLSpecs.Heze.Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0) :
    FcMap.lookup s0.blocks (htr a) = some a := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  exact LawfulFcMap.lookup_insert_self _ _ _

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **Accountable safety for two honest nodes.** Two honest nodes start at the anchor store of
the anchor state `A` and the anchor block `a`. The justified checkpoint `j` of the store `sW`
conflicts with the finalized checkpoint `f` of the store `sU`. The checkpoint `f` is not later
than `j`. Then two blocks or two headers share a root, or two attestation data share a root, or
there is slashing evidence. The evidence is against the fork point `st₀` of two runs from `A`.
Run 1 (`p₁ ++ r₁`) finalizes `f`, and run 2 (`p₂ ++ r₂`) justifies `j`. The two runs reach
`st₀` after `p₁` and after `p₂`. `runDrift` measures the drift of each chain along its run after
`st₀`.

The premises:

- The anchor premises of `honestNode_finality_lock`. The anchor block is the block of `A`: its
  root is the root of the filled header of `A`.
- `A` has ordered checkpoints, its own block roots, and anchor checkpoints on its history.
- `2 * SLOTS_PER_EPOCH ≤ SLOTS_PER_HISTORICAL_ROOT`. Every state on a prefix of a store run
  of `sW` or of `sU` meets `RunTotals` (`StoreTotals`).
- No block event of either trace has a zero state root.
- The sorted attesting indices hold the indices (`QsortMem`).
- `f` comes after the first two epochs past the anchor: `max (e₀ + 2) 3 ≤ f.epoch`.
- Every ancestor path of `sU` and every ancestor path of `sW` have the same blocks before the
  first slot of that epoch. -/
theorem honestNodes_accountable (hq : QsortMem) {A : BeaconState} {a : BeaconBlock}
    {s0 sW sU : EthCLSpecs.Heze.Store map} {esW esU : List TraceEvent}
    {arrW arrU : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)}
    (hanchor : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0)
    (hself : a.parentRoot ≠ htr a)
    (hW : NodeTrace s0 esW arrW sW) (hU : NodeTrace s0 esU arrU sU)
    (hevW : ∀ e, TraceEvent.handler e ∈ esW → e.NotAtAnchorParent a)
    (hevU : ∀ e, TraceEvent.handler e ∈ esU → e.NotAtAnchorParent a)
    (hsrW : ∀ sb, TraceEvent.handler (.block sb) ∈ esW →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hsrU : ∀ sb, TraceEvent.handler (.block sb) ∈ esU →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hanc : htr (filledHeader A) = htr a)
    (hord : StateCkptOrd A) (hroots : AnchorRoots A) (hcps : AnchorCps A)
    (hsphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (htotW : StoreTotals A a sW) (htotU : StoreTotals A a sU)
    (hconf : Conflicting sW sW.justifiedCheckpoint sU.finalizedCheckpoint)
    (hep : sU.finalizedCheckpoint.epoch ≤ sW.justifiedCheckpoint.epoch)
    (hfX : max (epochOf A + 2) 3 ≤ sU.finalizedCheckpoint.epoch.toNat)
    (hbase : ∀ k₁ bs₁ k₂ bs₂, AncestorPath a sU k₁ bs₁ → AncestorPath a sW k₂ bs₂ →
      bs₁.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch) =
        bs₂.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch)) :
    RootCollision ∨ HtrCollision AttestationData ∨
      ∃ (st₀ : BeaconState) (p₁ r₁ p₂ r₂ : List ChainStep)
        (pairs : List (IndexedAttestation × IndexedAttestation)),
        ChainRun (2 ^ 64 - 1) p₁ A st₀ ∧ ChainRun (2 ^ 64 - 1) p₂ A st₀ ∧
        SlashingEvidence st₀ (OnRun (2 ^ 64 - 1) A (p₁ ++ r₁)) (OnRun (2 ^ 64 - 1) A (p₂ ++ r₂))
          (runDrift (2 ^ 64 - 1) st₀ r₁) (runDrift (2 ^ 64 - 1) st₀ r₂) pairs := by
  by_cases hrc : RootCollision
  · exact .inl hrc
  by_cases hac : HtrCollision AttestationData
  · exact .inr (.inl hac)
  refine .inr (.inr ?_)
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hrc (.inr h)
  have hhi : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  have hspe := slotsPerEpochPos
  -- The invariant of the two stores.
  have h0 := CkptInv.anchor A a s0 hanchor hself
  have IW := (NodeTrace.ckptInv hw hW h0 hord hevW hsrW).resolve_right hrc
  have IU := (NodeTrace.ckptInv hw hU h0 hord hevU hsrU).resolve_right hrc
  generalize hfdef : sU.finalizedCheckpoint = f at hconf hep hfX
  generalize hjdef : sW.justifiedCheckpoint = j at hconf hep
  have heA : (EthCLSpecs.Heze.currentEpochOf (pureState A)).toNat = epochOf A :=
    currentEpochOf_epochOf A
  have hfj : f.epoch.toNat ≤ j.epoch.toNat := UInt64.le_iff_toNat_le.mp hep
  -- The two runs: run 1 finalizes `f`, run 2 justifies `j`.
  obtain ⟨k₁, steps₁, v₁, hr₁, hp₁, hf₁, hfin, hsr₁⟩ := finalized_source hw (hfdef ▸ IU.fSource)
    (by omega) hroots hcps hord hsphr htotU
  obtain ⟨k₂, steps₂, v₂, hr₂, hp₂, hj₂, hjus, -⟩ := justified_source hw (hjdef ▸ IW.jSource)
    (by omega) hroots hcps hord hsphr htotW
  have hm₁ := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hcps hord
    (hr₁.blocks_slot_ge hhi)
  have hm₂ := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hcps hord
    (hr₂.blocks_slot_ge hhi)
  have hK : anchorK A = max (epochOf A + 1) 2 := rfl
  -- Chain 1 finalizes `f`. The checkpoint `f` is outside the base, and it is on chain 1.
  have hfin' : EthCLLib.Proofs.FFG.Finalized (ffgChain (2 ^ 64 - 1) steps₁ A regVals) (toCp f) := by
    rcases hfin with h | h
    · exact h
    · have := (hm₁.base _ h).1
      simp only [toCp] at this
      omega
  have hJf : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps₁ A regVals) (toCp f) :=
    match hfin' with
    | .one h _ _ _ => h
    | .two h _ _ _ _ _ => h
  have hon₁ : chainRoot A steps₁ f.epoch.toNat = f.root :=
    Option.some.inj (hJf.onChain fun x hx => (hm₁.base x hx).2)
  have hon₂j : chainRoot A steps₂ j.epoch.toNat = j.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm₂.base x hx).2)
  -- The store `sW` holds the anchor block.
  have ha : FcMap.lookup sW.blocks (htr a) = some a := by
    obtain ⟨b', hb'⟩ := NodeTrace.blocks_persist hW _ _ (getForkchoiceStore_anchor A a s0 hanchor)
    have he := IW.slot.atRoot _ _ hb'
    have : b' = a := Classical.byContradiction fun hne => hcb ⟨b', a, hne, he⟩
    rw [this] at hb'
    exact hb'
  -- `f` is not on chain 2: the checkpoints conflict.
  have hv₂ : v₂.slot.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hdiv₂ := Nat.div_mul_le_self v₂.slot.toNat slotsPerEpoch
  have hjE : j.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
    have := Nat.mul_le_mul_right slotsPerEpoch hj₂
    unfold epochOf at this
    omega
  have hAf : A.slot.toNat ≤ f.epoch.toNat * slotsPerEpoch := by
    have h1 := Nat.lt_mul_div_succ A.slot.toNat hspe
    have h2 : (A.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ f.epoch.toNat * slotsPerEpoch :=
      Nat.mul_le_mul_right _ (by unfold epochOf at hfX; omega)
    rw [Nat.mul_comm] at h1
    omega
  have hoff : chainRoot A steps₂ f.epoch.toNat ≠ f.root :=
    conflicting_not_onChain hw hrc hhi IW.slot ha hanc hroots hr₂ hp₂ hon₂j hfj (by omega) hjE
      hAf hconf
  have hnot : ¬ (ffgChain (2 ^ 64 - 1) steps₂ A regVals).OnChain (toCp f) := fun h =>
    hoff (Option.some.inj h)
  -- Find the fork point. It comes at or after the first slot of epoch `max (e₀ + 2) 3`.
  obtain ⟨st₀, p₁, r₁, p₂, r₂, F⟩ := hr₁.forkAt hr₂
  generalize hX : max (epochOf A + 2) 3 = X at hfX hbase
  have hT₁ : X * slotsPerEpoch ≤ v₁.slot.toNat := by
    have := Nat.mul_le_mul_right slotsPerEpoch (Nat.le_trans hfX hf₁)
    have := Nat.div_mul_le_self v₁.slot.toNat slotsPerEpoch
    unfold epochOf at *
    omega
  have hT₂ : X * slotsPerEpoch ≤ v₂.slot.toNat := by
    have := Nat.mul_le_mul_right slotsPerEpoch (Nat.le_trans (Nat.le_trans hfX hfj) hj₂)
    unfold epochOf at *
    omega
  have hst₀ : X * slotsPerEpoch ≤ st₀.slot.toNat :=
    F.slot_ge hhi hr₁ hr₂ hT₁ hT₂ (hbase _ _ _ _ hp₁ hp₂)
  -- The epoch of the fork point is at most the epoch of `f`.
  have hL : epochOf st₀ ≤ f.epoch.toNat := by
    refine Nat.le_of_not_lt fun hlt => hnot ?_
    have h1 : (f.epoch.toNat + 1) * slotsPerEpoch ≤ st₀.slot.toNat := by
      have := Nat.mul_le_mul_right slotsPerEpoch (show f.epoch.toNat + 1 ≤ epochOf st₀ from hlt)
      have := Nat.div_mul_le_self st₀.slot.toNat slotsPerEpoch
      unfold epochOf at *
      omega
    have hk : f.epoch.toNat * slotsPerEpoch < st₀.slot.toNat := by
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hc := congrArg EthCLLib.Proofs.FFG.Checkpoint.root (F.cpOf_eq hhi hr₁ hr₂ hk)
    simp only [cpOf] at hc
    change some (chainRoot A steps₂ f.epoch.toNat) = some f.root
    rw [← hc, hon₁]
  -- The premises of accountable safety.
  have hshared := F.commonBase hhi hr₁ hr₂ regVals hcps hord (hX ▸ hst₀) (b := toCp f)
    (by rw [hX]; exact hfX)
  have hagree := ffgChain_agree hw hrc hhi hr₁ hr₂ (hp₁.linked IU.slot).1 (hp₂.linked IW.slot).1
    regVals regVals
  have htot₀ : RunTotals st₀ := htotU p₁ r₁ st₀ (F.eq₁ ▸ hsr₁) F.run₁
  let E := max (j.epoch.toNat + 1) (f.epoch.toNat + 3)
  have hc₁ := F.stakeClose hhi hr₁ hcps hord htot₀ E
  have hc₂ := F.symm.stakeClose hhi hr₂ hcps hord htot₀ E
  obtain ⟨Xs, hnd, hsl, hstake⟩ := EthCLLib.Proofs.FFG.ffg_accountable_safety (activeOf st₀)
    (totalOf st₀) (epochOf st₀) E (runDrift (2 ^ 64 - 1) st₀ r₁) (runDrift (2 ^ 64 - 1) st₀ r₂)
    (ffgChain (2 ^ 64 - 1) steps₁ A regVals) (ffgChain (2 ^ 64 - 1) steps₂ A regVals) rfl hfin'
    hjus (by simp only [toCp]; exact hfj) hnot hshared hagree hc₁ hc₂
    (by simp only [toCp]; exact hL) ⟨by simp only [toCp, E]; omega, by simp only [toCp, E]; omega⟩
  -- The evidence.
  obtain ⟨pairs, hps, hpv, hpc⟩ := pairs_of_slashable hq hac hm₁ hm₂ Xs hsl
  refine ⟨st₀, p₁, r₁, p₂, r₂, pairs, F.run₁, F.run₂, hps, ?_, ?_⟩
  · rw [← F.eq₁, ← F.eq₂]
    exact hpv
  · have hsub := sum_map_le_of_subset (activeOf st₀) Xs (commonOf pairs) hnd hpc
    unfold activeStake
    unfold stakeSum at hstake ⊢
    omega

end Main

end EthCLSpecs.Proofs.Heze
