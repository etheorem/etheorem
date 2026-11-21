import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.TargetStake

/-!
# `EthCLSpecs.Proofs.Heze.VoteValid`: a placed vote is a valid indexed attestation on the run

`processAttestation` builds the indexed attestation of an attestation from the attesting
indices in sorted order. Then it asserts `isValidIndexedAttestation` on it. So each
attestation that the function accepts gives an indexed attestation that is valid on the state
of that run (`processAttestation_indexed`).

`isValidIndexedAttestation` reads the public keys of the registry, the fork, and the genesis
validators root: the three parts of `keyView` (`isValidIndexedAttestation_of_keyView`).
`processAttestation` accepted a placed vote (`RunVote`) on a state with the `keyView` of the
run state `u` before its block. So the indexed attestation of the vote is valid on `u`, a state
of the run. It also holds the voter (`RunVote.indexed`).

The sort is `Array.qsort`. Core Lean does not export its recursion, so no proof here can show
that it keeps the members of the array. `RunVote.indexed` takes that fact as the hypothesis
`QsortMem` (`LatestMessages.lean`), as the fork-choice theorems do.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState pureState_inj runPure run_bind_eq_ok run_get_bind_eq_ok
  run_assert_bind_eq_ok run_bind_eq_ok_pure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Attestation AttestationData
  IndexedAttestation ValidatorIndex Validator SignedBeaconBlock)

section
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- Two registries with one list of public keys have one public key at each index. -/
theorem pubkey_getElem!_eq {va vb : Array Validator}
    (h : va.map (·.pubkey) = vb.map (·.pubkey)) (k : Nat) :
    (va[k]!).pubkey = (vb[k]!).pubkey := by
  have hs : va.size = vb.size := by simpa using congrArg Array.size h
  by_cases hk : k < va.size
  · rw [getElem!_pos va k hk, getElem!_pos vb k (hs ▸ hk)]
    have := congrArg (·[k]?) h
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem hk,
      Array.getElem?_eq_getElem (hs ▸ hk), Option.map_some, Option.some.injEq] at this
    exact this
  · rw [getElem!_neg va k hk, getElem!_neg vb k (hs ▸ hk)]

/-- Two states with one `keyView` give one answer of `isValidIndexedAttestation`. -/
theorem isValidIndexedAttestation_of_keyView [CryptoBackend] {a b : BeaconState}
    (h : keyView (pureState a) = keyView (pureState b)) (ia : IndexedAttestation) :
    EthCLSpecs.Heze.isValidIndexedAttestation (pureState a) ia =
      EthCLSpecs.Heze.isValidIndexedAttestation (pureState b) ia := by
  simp only [keyView, Prod.mk.injEq] at h
  obtain ⟨hk, hf, hg⟩ := h
  change a.validators.val.map (·.pubkey) = b.validators.val.map (·.pubkey) at hk
  have hs : a.validators.val.size = b.validators.val.size := by
    simpa using congrArg Array.size hk
  have hpk : ∀ k : Nat, (a.validators[k]!).pubkey = (b.validators[k]!).pubkey := fun k => by
    rw [progressiveList_getElem!_eq, progressiveList_getElem!_eq]
    exact pubkey_getElem!_eq hk k
  -- State the same reads in the form that the unfolded definition uses.
  have hsz : (pureState a).view.validators.size = (pureState b).view.validators.size := hs
  have hpk' : ∀ k : Nat, ((pureState a).view.validators[k]!).pubkey =
      ((pureState b).view.validators[k]!).pubkey := hpk
  unfold EthCLSpecs.Heze.isValidIndexedAttestation EthCLSpecs.Heze.getDomain
  simp only [hf, hg, hsz, hpk']

variable [Config] [CryptoBackend]

/-- A successful `processAttestation` validated an indexed attestation. The indexed
attestation has the data and the signature of the attestation, and the attesting indices in
sorted order. At v1.7.0-beta.4 the index list is progressive, so the run builds it whole. -/
theorem processAttestation_indexed (att : Attestation) (ps : EthCLSpecs.Heze.Slot)
    (st : BeaconState) {r : PUnit × State}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att ps).run
      (pureState st) = .ok r) :
    ∃ (idx : Array ValidatorIndex) (ia : IndexedAttestation),
      EthCLSpecs.Heze.getAttestingIndices (pureState st) att = .ok idx ∧ ia.data = att.data ∧
      ia.attestingIndices.val = idx.qsort (· < ·) ∧
      EthCLSpecs.Heze.isValidIndexedAttestation (pureState st) ia = .ok true := by
  unfold EthCLSpecs.Heze.processAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- Each shape check is an `assert`, a `checkedAdd`, or the `liftErr` of the committee
  -- offset. A successful run of each one returns its input state, as in
  -- `processAttestation_run_flags`, so the state stays `pureState st`.
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨incl, s1, hincl, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have e1 := (pureState_inj (checkedAdd_run_state hincl)).symm
  subst e1
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨off, s1', hoff, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have e2 := (pureState_inj (liftErr_run_ok_spec hoff).2).symm
  subst e2
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- Read the flag list, the attesting indices, and the validity answer.
  obtain ⟨f, s2, -, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨idx0, s4, hidx0, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨vb, s6, hvb, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  -- The validity read and its assert read the state that the run read first.
  obtain ⟨hv, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  let ia : IndexedAttestation :=
    { attestingIndices := ⟨idx0.qsort (fun a b => a < b)⟩, data := att.data,
      signature := att.signature }
  refine ⟨idx0, ia, (liftErr_run_ok_spec hidx0).1, rfl, rfl, ?_⟩
  rw [(liftErr_run_ok_spec hvb).1, hv]

/-- **A placed vote is a valid indexed attestation on the run.** The run of the prefix `s₁`
reaches `u`, and the next step is the block that includes the vote. The indexed attestation
of the vote has the data of the vote, holds the voter, and is valid on `u`. `QsortMem` puts
the voter in the sorted indices. -/
theorem RunVote.indexed (hq : QsortMem) {hi : Nat} {st₀ : BeaconState}
    {steps : List ChainStep} {i : ValidatorIndex} {d : AttestationData}
    (hv : RunVote hi st₀ steps i d) :
    ∃ (s₁ s₂ : List ChainStep) (sb : SignedBeaconBlock) (v : Bool) (u : BeaconState)
      (ia : IndexedAttestation),
      steps = s₁ ++ .block sb v :: s₂ ∧ ChainRun hi s₁ st₀ u ∧ ia.data = d ∧
      i ∈ ia.attestingIndices.toArray ∧
      EthCLSpecs.Heze.isValidIndexedAttestation (pureState u) ia = .ok true := by
  obtain ⟨s₁, s₂, sb, v, u, pre, post, att, hs, hr, -, hd, hvote, -, hkey, -⟩ := hv
  obtain ⟨⟨ps, hrun⟩, ⟨idx, hidx, hmem⟩, -, -⟩ := hvote
  obtain ⟨s, hs', -⟩ := runPure_ok_run hrun
  obtain ⟨idx', ia, hidx', hdat, hval, hok⟩ := processAttestation_indexed att ps pre hs'
  -- `getAttestingIndices` is a function of `pre`, so the two index arrays are one.
  have he : idx' = idx := by
    rw [hidx] at hidx'
    cases hidx'
    rfl
  subst he
  refine ⟨s₁, s₂, sb, v, u, ia, hs, hr, hdat.trans hd, ?_, ?_⟩
  · show i ∈ ia.attestingIndices.val
    rw [hval]
    exact (hq _ _).mpr hmem
  · rw [← isValidIndexedAttestation_of_keyView hkey]
    exact hok

end

end EthCLSpecs.Proofs.Heze
