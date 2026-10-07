import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.StorePure

/-!
# `EthCLSpecs.Proofs.Heze.LatestMessages`: where a latest message comes from

`get_attestation_score` reads `store.latest_messages`. This module traces each entry of
that map to the attestation event that wrote it.

## One handler

`on_attestation` (phase0 `fork-choice.md:952`) is the only handler that writes the map.
`onAttestation_run_ok` inverts a successful run. The run passed
`validate_on_attestation` (`gloas/fork-choice.md:846`) on the store it read. So the block of
the vote is in the store with a slot no greater than the vote slot (`:867`). The current slot
is past the vote slot (`:885`). The run computed the target state and the attesting indices
`A`. Then it wrote `update_latest_messages` (`:897`) over the sorted `A`. Under `StorePure`,
the target state is the uncached box of a plain value. `onAttestation_run_post` states the
written store alone, and it needs no such hypothesis.

`update_latest_messages` replaces the message of an index only for a greater slot. It skips
equivocators. `latestFold_mono`, `latestFold_source`, and `latestFold_delivered` state
the three facts of that loop. The five other handler events keep the map (`keeps_solve`).
`onInclusionList` writes only the IL store (`onInclusionList_run_eq`).

## The trace

`NodeTrace.latest_source`: an entry at the end of a trace was in the seed, or an
attestation event of the trace wrote it (`AttWrite`). `NodeTrace.latest_mono`: the slot of
an entry never decreases. `onAttestation_delivers`: take an event whose attesting indices
hold `i`, where `i` is not an equivocator. After the event, the entry of `i` has at least the
vote slot.

## The committees

`getAttestingIndices_mem`: an attesting index is in a committee of the vote slot, and the
committee bits name that committee (`get_attesting_indices`, `electra/beacon-chain.md:651`).
The successful run built that committee, so `getBeaconCommittee` returns it as `.ok`.
The handler writes the indices in sorted order. Core Lean states no lemma about
`Array.qsort`, and its recursion is private.
So the theorems that cross the sort take `QsortMem` as a hypothesis.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok run_bind_eq_ok
  run_pure_eq_ok run_get_bind_eq_ok run_assert_bind_eq_ok KeepsAt)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap pureState)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint Slot BeaconBlock
  ValidatorIndex LatestMessage
  Attestation AttesterSlashing SignedBeaconBlock PayloadAttestationMessage
  SignedExecutionPayloadEnvelope SignedInclusionList ExecutionPayload ExecutionRequests
  Transaction updateLatestMessages getCurrentSlot validateOnAttestation
  storeTargetCheckpointState getAttestingIndices getBeaconCommittee getCommitteeIndices
  getForkchoiceStore onTick
  onBlock onAttestation onAttesterSlashing onPayloadAttestationMessage
  onExecutionPayloadEnvelope)

/-- The sort of the handler keeps the members of the array. Core Lean states no lemma about
`Array.qsort`, so the theorems that need this fact take it as a hypothesis. -/
def QsortMem : Prop :=
  ∀ (A : Array ValidatorIndex) (i : ValidatorIndex), i ∈ A.qsort (· < ·) ↔ i ∈ A

section Loop
variable {map : MapKind} [Preset] [FcMap map]

/-- The message that `att` writes: its slot, its root, and the payload flag of
`data.index`. -/
def attMessage (att : Attestation) : LatestMessage :=
  { slot := att.data.slot, root := att.data.beaconBlockRoot, payloadPresent := att.data.index == 1 }

/-- One step of the loop of `updateLatestMessages`, for the equivocators `eq`. -/
def latestStep (eq : Array ValidatorIndex) (att : Attestation)
    (lm : map ValidatorIndex LatestMessage) (i : ValidatorIndex) : map ValidatorIndex LatestMessage :=
  if !eq.contains i then
    match FcMap.lookup lm i with
    | some prev => if att.data.slot > prev.slot then FcMap.insert lm i (attMessage att) else lm
    | none => FcMap.insert lm i (attMessage att)
  else lm

variable [LawfulFcMap map ValidatorIndex]

/-- One step of the loop at key `i`. The entry of `i` stays, or the step writes the message
of `att` at `i`. A write needs three conditions: `j = i`, `i` is not an equivocator, and the
old entry of `i` is absent or has a smaller slot. -/
theorem latestStep_lookup (eq : Array ValidatorIndex) (att : Attestation)
    (m : map ValidatorIndex LatestMessage) (j i : ValidatorIndex) :
    FcMap.lookup (latestStep eq att m j) i = FcMap.lookup m i ∨
      (j = i ∧ eq.contains i = false ∧
        (∀ p, FcMap.lookup m i = some p → p.slot < att.data.slot) ∧
        FcMap.lookup (latestStep eq att m j) i = some (attMessage att)) := by
  unfold latestStep
  by_cases hc : (!eq.contains j) = true
  · rw [if_pos hc]
    by_cases hji : j = i
    · subst hji
      have hc' : eq.contains j = false := by simpa using hc
      cases hl : FcMap.lookup m j with
      | none =>
        refine Or.inr ⟨?_, hc', ?_, ?_⟩
        · trivial
        · simp
        · simp
      | some prev =>
        by_cases hs : att.data.slot > prev.slot
        · simp only [hs, if_true]
          refine Or.inr ⟨trivial, hc', ?_, by simp⟩
          intro p hp
          cases hp
          exact hs
        · simp only [hs, if_false]
          exact Or.inl hl
    · left
      split
      · split
        · exact LawfulFcMap.lookup_insert_ne _ _ _ _ hji
        · rfl
      · exact LawfulFcMap.lookup_insert_ne _ _ _ _ hji
  · rw [if_neg hc]
    exact Or.inl rfl

/-- The slot of the entry of `i` never decreases along the loop. -/
theorem latestFold_mono (eq : Array ValidatorIndex) (att : Attestation) (i : ValidatorIndex) :
    ∀ (l : List ValidatorIndex) (m : map ValidatorIndex LatestMessage) (p : LatestMessage),
      FcMap.lookup m i = some p →
      ∃ q, FcMap.lookup (l.foldl (latestStep eq att) m) i = some q ∧ p.slot ≤ q.slot := by
  intro l
  induction l with
  | nil => intro m p hp; exact ⟨p, hp, UInt64.le_refl _⟩
  | cons j l ih =>
    intro m p hp
    rw [List.foldl_cons]
    rcases latestStep_lookup eq att m j i with h | ⟨-, -, hlt, h⟩
    · exact ih _ p (h.trans hp)
    · obtain ⟨q, hq, hle⟩ := ih _ _ h
      exact ⟨q, hq, UInt64.le_trans (UInt64.le_of_lt (hlt p hp)) hle⟩

/-- An entry of `i` after the loop was there before, or it is the message of `att`. In the
second case, `i` is in the list and is not an equivocator. -/
theorem latestFold_source (eq : Array ValidatorIndex) (att : Attestation) (i : ValidatorIndex) :
    ∀ (l : List ValidatorIndex) (m : map ValidatorIndex LatestMessage) (q : LatestMessage),
      FcMap.lookup (l.foldl (latestStep eq att) m) i = some q →
      FcMap.lookup m i = some q ∨
        (i ∈ l ∧ eq.contains i = false ∧ q = attMessage att) := by
  intro l
  induction l with
  | nil => intro m q hq; exact Or.inl hq
  | cons j l ih =>
    intro m q hq
    rw [List.foldl_cons] at hq
    rcases ih _ q hq with h | ⟨hi, hc, hqa⟩
    · rcases latestStep_lookup eq att m j i with h' | ⟨hji, hc, -, h'⟩
      · exact Or.inl (h'.symm.trans h)
      · rw [h'] at h
        cases h
        exact Or.inr ⟨hji ▸ List.mem_cons_self, hc, rfl⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ hi, hc, hqa⟩

/-- Take a member `i` of the list that is not an equivocator. After the loop, the entry of
`i` has a slot at least the slot of `att`. -/
theorem latestFold_delivered (eq : Array ValidatorIndex) (att : Attestation)
    (i : ValidatorIndex) (hc : eq.contains i = false) :
    ∀ (l : List ValidatorIndex) (m : map ValidatorIndex LatestMessage), i ∈ l →
      ∃ q, FcMap.lookup (l.foldl (latestStep eq att) m) i = some q ∧
        att.data.slot ≤ q.slot := by
  intro l
  induction l with
  | nil => intro m h; cases h
  | cons j l ih =>
    intro m hi
    rw [List.foldl_cons]
    by_cases hji : j = i
    · subst hji
      -- After the step, the entry of `j` has a slot at least the slot of `att`.
      have hstep : ∃ p, FcMap.lookup (latestStep eq att m j) j = some p ∧
          att.data.slot ≤ p.slot := by
        unfold latestStep
        have hc' : (!eq.contains j) = true := by rw [hc]; rfl
        rw [if_pos hc']
        cases hl : FcMap.lookup m j with
        | none => exact ⟨attMessage att, by simp, UInt64.le_refl _⟩
        | some prev =>
          by_cases hs : att.data.slot > prev.slot
          · simp only [hs, if_true]
            exact ⟨attMessage att, by simp, UInt64.le_refl _⟩
          · simp only [hs, if_false]
            exact ⟨prev, hl, UInt64.not_lt.mp hs⟩
      obtain ⟨p, hp, hle⟩ := hstep
      obtain ⟨q, hq, hle'⟩ := latestFold_mono eq att j l _ p hp
      exact ⟨q, hq, UInt64.le_trans hle hle'⟩
    · rcases List.mem_cons.mp hi with h | h
      · exact absurd h.symm hji
      · exact ih _ h

end Loop

section Handler
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- `updateLatestMessages` folds `latestStep` over the indices, with the equivocators of
its store. -/
theorem updateLatestMessages_eq (store : Store map) (idx : Array ValidatorIndex)
    (att : Attestation) :
    (updateLatestMessages store idx att).latestMessages
      = idx.toList.foldl (latestStep store.equivocatingIndices att) store.latestMessages := by
  simp only [updateLatestMessages, Id.run]
  rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList]
  generalize store.latestMessages = m0
  generalize idx.toList = l
  -- In `Id`, the loop of yields is a fold.
  show ForInStep.value (List.foldlM _ _ l : Id _) = _
  induction l generalizing m0 with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldlM_cons, List.foldl_cons]
    rw [← ih]
    unfold latestStep attMessage
    by_cases hc : (!store.equivocatingIndices.contains i) = true
    · rw [if_pos hc]
      simp only [hc, if_true]
      cases hl : FcMap.lookup m0 i with
      | none => rfl
      | some prev =>
        by_cases hs : att.data.slot > prev.slot
        · simp only [hs, if_true]
          rfl
        · simp only [hs, if_false]
          rfl
    · rw [if_neg hc]
      simp only [hc]
      rfl

variable [Config]

/-- A successful `validateOnAttestation` run on the store `st`. The block of the vote is in
`st` with a slot no greater than the vote slot. The current slot of `st` is past the vote
slot. -/
theorem validateOnAttestation_run_ok (st : Store map) (att : Attestation) (fb : Bool)
    (s s' : Store map)
    (h : (validateOnAttestation (StoreTransition := ForkChoiceStoreRun (Store map)) st att fb).run s
      = .ok ((), s')) :
    ∃ (b : BeaconBlock) (cs : Slot) (u u' : Store map),
      FcMap.lookup st.blocks att.data.beaconBlockRoot = some b ∧ b.slot ≤ att.data.slot ∧
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run u
        = .ok (cs, u') ∧
      att.data.slot.toNat + 1 ≤ cs.toNat := by
  unfold validateOnAttestation at h
  -- A vote that is not from a block first passes the epoch window test, which reads the
  -- store epoch. Both branches then run the join point `jp` of the other checks.
  extract_lets _ jp at h
  obtain ⟨_, _, h⟩ : ∃ (y : PUnit) (s1 : Store map), (jp y).run s1 = .ok ((), s') := by
    split at h
    · rename_i _ h
      obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      dsimp only at h
      obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      exact ⟨(), _, h⟩
    · rename_i _ h
      obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      exact ⟨(), _, h⟩
  simp only [jp] at h
  -- The three checks on the target and the two roots.
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨b, u1, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hlook : FcMap.lookup st.blocks att.data.beaconBlockRoot = some b := by
    unfold FcMap.getOrThrow FcMap.getOrThrowKey at hb
    split at hb
    · rename_i v hv
      rw [hv, run_pure_eq_ok _ _ _ _ hb]
    · cases hb
  -- The slot check, the three index checks, and the checkpoint check.
  obtain ⟨hslot, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The clock check, with the checked `data.slot + 1`.
  obtain ⟨cs, u2, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨d, u3, hd, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hge : cs ≥ d := by
    by_cases hc : cs ≥ d
    · exact hc
    · rw [if_neg hc] at h
      cases h
  refine ⟨b, cs, _, _, hlook, hslot, hcs, ?_⟩
  simp only [checkedAdd] at hd
  split at hd
  · simp [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at hd
  · rename_i hno
    have hd' := run_pure_eq_ok _ _ _ _ hd
    subst hd'
    have := EthCLLib.Proofs.toNat_add_of_not_lt _ _ hno
    rw [UInt64.toNat_one] at this
    have hge' := UInt64.le_iff_toNat_le.mp hge
    omega

variable [CryptoBackend]

/-- `storeTargetCheckpointState` returns its store with only the checkpoint states
changed. -/
theorem storeTargetCheckpointState_run_ok (st : Store map) (target : EthCLSpecs.Heze.Checkpoint)
    (s s' mid : Store map)
    (h : (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) st
      target).run s = .ok (mid, s')) :
    ∃ cps, mid = { st with checkpointStates := cps } := by
  unfold storeTargetCheckpointState at h
  split at h
  · exact ⟨st.checkpointStates, run_pure_eq_ok _ _ _ _ h⟩
  · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    dsimp only at h
    -- The checked start slot of the target epoch.
    obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    split at h
    · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      exact ⟨_, run_pure_eq_ok _ _ _ _ h⟩
    · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      exact ⟨_, run_pure_eq_ok _ _ _ _ h⟩

/-- The attesting indices of `att` at the store `pre`: the target-state step of the handler
returns the checkpoint states `cps`, the uncached box of the target state `ts` sits at the
target, and `getAttestingIndices` returns `A`. -/
def AttIndices (pre : Store map) (att : Attestation) (A : Array ValidatorIndex) : Prop :=
  ∃ (cps : map Checkpoint State) (s2 : Store map) (ts : BeaconState),
    (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) pre
      att.data.target).run pre = .ok ({ pre with checkpointStates := cps }, s2) ∧
    FcMap.lookup cps att.data.target = some (pureState ts) ∧
    getAttestingIndices (pureState ts) att = .ok A

/-- The store that a successful `on_attestation` run writes: the latest messages of the
sorted attesting indices `A`, over the store with the checkpoint states `cps` that the
target-state step returned. -/
theorem onAttestation_run_post (att : Attestation) (fb : Bool) (pre post : Store map)
    (h : (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
      fb).run pre = .ok ((), post)) :
    ∃ (cps : map Checkpoint State) (s2 : Store map) (A : Array ValidatorIndex),
      (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) pre
        att.data.target).run pre = .ok ({ pre with checkpointStates := cps }, s2) ∧
      post = updateLatestMessages { pre with checkpointStates := cps } (A.qsort (· < ·)) att := by
  unfold onAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, s1, hval, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The checks read the store and do not change the runner state.
  have hk : KeepsAt (fun st : Store map => st) pre
      (validateOnAttestation (StoreTransition := ForkChoiceStoreRun (Store map)) pre att fb) := by
    keeps_solve
  have hs1 : s1 = pre := hk pre () s1 rfl hval
  rw [hs1] at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨mid, s2, hmid, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨cps, hcps⟩ := storeTargetCheckpointState_run_ok _ _ _ _ _ hmid
  subst hcps
  -- The target read, the indices, the indexed attestation and its signature check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨A, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The validity check is an `Except` read, then its gate.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact ⟨cps, s2, A, hmid, EthCLLib.Proofs.run_set_state_eq _ _ _ _ h⟩

variable [LawfulFcMap map Checkpoint]

/-- The part of the `on_attestation` contract that the latest messages need. The theorem
omits the target and index checks and the signature check. A successful run passed
`validateOnAttestation` on the store it read. It computed the attesting indices `A` from
the target state, the uncached box of `ts` under `StorePure`. It wrote the latest messages
of the sorted `A`. Only the checkpoint states and the latest messages change. -/
theorem onAttestation_run_ok (att : Attestation) (fb : Bool) (pre post : Store map)
    (hp : StorePure pre)
    (h : (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
      fb).run pre = .ok ((), post)) :
    ∃ (b : BeaconBlock) (cs : Slot) (u u' : Store map)
      (cps : map Checkpoint State) (s2 : Store map) (ts : BeaconState)
      (A : Array ValidatorIndex),
      FcMap.lookup pre.blocks att.data.beaconBlockRoot = some b ∧ b.slot ≤ att.data.slot ∧
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) pre).run u
        = .ok (cs, u') ∧
      att.data.slot.toNat + 1 ≤ cs.toNat ∧
      (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) pre
        att.data.target).run pre = .ok ({ pre with checkpointStates := cps }, s2) ∧
      FcMap.lookup cps att.data.target = some (pureState ts) ∧
      getAttestingIndices (pureState ts) att = .ok A ∧
      post = updateLatestMessages { pre with checkpointStates := cps } (A.qsort (· < ·)) att := by
  unfold onAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, s1, hval, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨b, cs, u, u', hb, hslot, hcs, hge⟩ := validateOnAttestation_run_ok _ _ _ _ _ hval
  -- The checks read the store and do not change the runner state.
  have hk : KeepsAt (fun st : Store map => st) pre
      (validateOnAttestation (StoreTransition := ForkChoiceStoreRun (Store map)) pre att fb) := by
    keeps_solve
  have hs1 : s1 = pre := hk pre () s1 rfl hval
  rw [hs1] at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨mid, s2, hmid, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨cps, hcps⟩ := storeTargetCheckpointState_run_ok _ _ _ _ _ hmid
  subst hcps
  obtain ⟨_, s3, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨ts, s4, hts, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hts' : FcMap.lookup cps att.data.target = some ts := by
    unfold FcMap.getOrThrowKey at hts
    split at hts
    · rename_i v hv
      rw [hv, run_pure_eq_ok _ _ _ _ hts]
    · cases hts
  -- The target state is the uncached box of a value: the target step keeps `StorePure`.
  have hpmid : StorePure { pre with checkpointStates := cps } :=
    hp.storeTargetCheckpointState att.data.target _ _ _ hmid
  obtain ⟨tv, htv⟩ := hpmid.checkpointStates_some att.data.target
    (show (FcMap.lookup cps att.data.target).isSome = true by rw [hts']; rfl)
  change FcMap.lookup cps att.data.target = some (pureState tv) at htv
  rw [htv] at hts'
  injection hts' with hts'
  subst hts'
  obtain ⟨A, s5, hA, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hA' : getAttestingIndices (pureState tv) att = .ok A := by
    unfold liftErr at hA
    cases hx : getAttestingIndices (pureState tv) att with
    | error e =>
      rw [hx] at hA
      cases hA
    | ok a =>
      rw [hx] at hA
      rw [run_pure_eq_ok _ _ _ _ hA]
  dsimp only at h
  -- The indexed attestation and its signature check, an `Except` read and its gate, then
  -- the write.
  obtain ⟨_, s6, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact ⟨b, cs, u, u', cps, s2, tv, A, hb, hslot, hcs, hge, hmid, htv, hA',
    EthCLLib.Proofs.run_set_state_eq _ _ _ _ h⟩

end Handler

/-- An invariant of a `for` loop over a list in `Except`. Each successful body run keeps
`P`, so a successful loop keeps it. -/
theorem except_forIn_list_inv {α β ε : Type} (P : β → Prop)
    (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ (b : β) (r : ForInStep β), P b → f a b = .ok r → P r.value) →
      ∀ (init r : β), P init → forIn l init f = .ok r → P r := by
  intro l
  induction l with
  | nil =>
    intro _ init r hinit h
    cases h
    exact hinit
  | cons a l ih =>
    intro hf init r hinit h
    rw [List.forIn_cons] at h
    cases hfa : f a init with
    | error e =>
      rw [hfa] at h
      cases h
    | ok st =>
      rw [hfa] at h
      have hst := hf a List.mem_cons_self init st hinit hfa
      cases st with
      | done b =>
        cases h
        exact hst
      | yield b =>
        exact ih (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) b r hst h

section Committees
variable [Preset] [HasherTag]

/-- An attesting index is a member of a committee of the vote slot, and the committee bits
name that committee. `get_attesting_indices` reads the committees of `data.slot` that the
committee bits name, and collects the members whose aggregation bit is set. A successful run
built each committee it read, so the committee of the index exists (`.ok c`). -/
theorem getAttestingIndices_mem (st : BeaconState) (att : Attestation)
    (A : Array ValidatorIndex) (h : getAttestingIndices (pureState st) att = .ok A)
    (i : ValidatorIndex) (hi : i ∈ A) :
    ∃ ci c, ci ∈ getCommitteeIndices att.committeeBits ∧
      getBeaconCommittee (pureState st) att.data.slot ci = .ok c ∧ i ∈ c := by
  -- The proof does not read the flavour of the box, so it names the box once.
  generalize pureState st = st at h ⊢
  unfold getAttestingIndices at h
  dsimp only at h
  -- The invariant: every collected index is in a named committee of the vote slot.
  let Q : Array ValidatorIndex → Prop := fun out =>
    ∀ x ∈ out, ∃ ci c, ci ∈ getCommitteeIndices att.committeeBits ∧
      getBeaconCommittee st att.data.slot ci = .ok c ∧ x ∈ c
  obtain ⟨r, hloop, hfin⟩ := except_bind_eq_ok h
  have hA : A = r.snd := by
    obtain ⟨o, out⟩ := r
    cases hfin
    rfl
  subst hA
  rw [← Array.forIn_toList] at hloop
  refine except_forIn_list_inv (fun r : MProd Nat (Array ValidatorIndex) => Q r.snd) _ _ ?_
    _ _ (by intro x hx; simp at hx) hloop i hi
  -- One committee: the run built it as `c`, and the inner loop over its positions keeps `Q`.
  intro ci hci b st' hb hrun
  obtain ⟨c, hc, hrun⟩ := except_bind_eq_ok hrun
  obtain ⟨out, hinner, hrun⟩ := except_bind_eq_ok hrun
  have hst' : st'.value.snd = out := by
    cases hrun
    rfl
  rw [hst']
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hinner
  refine except_forIn_list_inv Q _ _ ?_ _ _ hb hinner
  intro k hk o st'' ho hbody
  have hklt : k < c.size := (Std.Legacy.Range.mem_of_mem_range' hk).2.1
  obtain ⟨bit, -, hbody⟩ := except_bind_eq_ok hbody
  split at hbody
  · cases hbody
    intro x hx
    rcases Array.mem_push.mp hx with hx | hx
    · exact ho x hx
    · refine ⟨ci, c, Array.mem_def.mpr hci, hc, ?_⟩
      rw [hx, getElem!_pos c k hklt]
      exact Array.getElem_mem hklt
  · cases hbody
    exact ho

end Committees

section Frames
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

omit [CryptoBackend] in
/-- `onTick` keeps the latest messages. -/
theorem onTick_keeps_latest (v : map ValidatorIndex LatestMessage) (time : UInt64) :
    KeepsAt (fun st : Store map => st.latestMessages) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the latest messages. The handler does not run the attestations of the
block. -/
theorem onBlock_keeps_latest (v : map ValidatorIndex LatestMessage)
    (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.latestMessages) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the latest messages. -/
theorem onAttesterSlashing_keeps_latest (v : map ValidatorIndex LatestMessage)
    (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => st.latestMessages) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the latest messages. -/
theorem onPayloadAttestationMessage_keeps_latest (v : map ValidatorIndex LatestMessage)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.latestMessages) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the latest messages. -/
theorem onExecutionPayloadEnvelope_keeps_latest (v : map ValidatorIndex LatestMessage)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.latestMessages) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

end Frames

section Trace
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The attestation event `att`, run on the store `pre`, writes the message of `i`. The run
passed its checks on `pre`: the block of the vote, and the clock. `i` is one of the sorted
attesting indices and not an equivocator in `pre`. -/
structure AttWrite (pre : Store map) (att : Attestation) (i : ValidatorIndex) : Prop where
  /-- The block of the vote is in `pre`, with a slot no greater than the vote slot. -/
  block : ∃ b : BeaconBlock, FcMap.lookup pre.blocks att.data.beaconBlockRoot = some b ∧
    b.slot ≤ att.data.slot
  /-- The current slot of `pre` is past the vote slot. -/
  clock : ∃ (cs : Slot) (u u' : Store map),
    (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) pre).run u
      = .ok (cs, u') ∧ att.data.slot.toNat + 1 ≤ cs.toNat
  /-- `i` is one of the sorted attesting indices. -/
  indices : ∃ A, AttIndices pre att A ∧ i ∈ A.qsort (· < ·)
  /-- `i` is not an equivocator in `pre`. -/
  notEq : pre.equivocatingIndices.contains i = false

/-- A handler event other than an attestation keeps the latest messages. -/
theorem HandlerEvent.run_keeps_latest (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s'))
    (he : ∀ att fb, e ≠ .attestation att fb) :
    s'.latestMessages = s.latestMessages := by
  have keep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      KeepsAt (fun st : Store map => st.latestMessages) s.latestMessages x →
      x.run s = .ok ((), s') → s'.latestMessages = s.latestMessages := fun x hk hx =>
    hk s () s' rfl hx
  cases e with
  | tick time => exact keep _ (onTick_keeps_latest _ time) h
  | block signedBlock => exact keep _ (onBlock_keeps_latest _ signedBlock) h
  | attestation att isFromBlock => exact absurd rfl (he att isFromBlock)
  | attesterSlashing asl => exact keep _ (onAttesterSlashing_keeps_latest _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact keep _ (onPayloadAttestationMessage_keeps_latest _ msg isFromBlock) h
  | envelope signedEnv => exact keep _ (onExecutionPayloadEnvelope_keeps_latest _ signedEnv) h

variable [LawfulFcMap map ValidatorIndex]

/-- The slot of an entry never decreases over one handler event. -/
theorem HandlerEvent.run_latest_mono (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) (i : ValidatorIndex)
    (p : LatestMessage) (hp : FcMap.lookup s.latestMessages i = some p) :
    ∃ q, FcMap.lookup s'.latestMessages i = some q ∧ p.slot ≤ q.slot := by
  by_cases he : ∃ att fb, e = .attestation att fb
  · obtain ⟨att, fb, rfl⟩ := he
    obtain ⟨cps, -, A, -, rfl⟩ := onAttestation_run_post att fb s s' h
    rw [updateLatestMessages_eq]
    exact latestFold_mono _ att i _ _ p hp
  · have hne : ∀ att fb, e ≠ .attestation att fb := fun att fb h' => he ⟨att, fb, h'⟩
    rw [HandlerEvent.run_keeps_latest e s s' h hne]
    exact ⟨p, hp, UInt64.le_refl _⟩

/-- The slot of an entry never decreases along a trace. -/
theorem NodeTrace.latest_mono {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (i : ValidatorIndex) (p : LatestMessage) (hp : FcMap.lookup s0.latestMessages i = some p) :
    ∃ q, FcMap.lookup s.latestMessages i = some q ∧ p.slot ≤ q.slot := by
  induction h with
  | nil => exact ⟨p, hp, UInt64.le_refl _⟩
  | handler e _ hrun ih =>
    obtain ⟨q, hq, hle⟩ := ih
    obtain ⟨q', hq', hle'⟩ := HandlerEvent.run_latest_mono e _ _ hrun i q hq
    exact ⟨q', hq', UInt64.le_trans hle hle'⟩
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

variable [LawfulFcMap map Root] [LawfulFcMap map Checkpoint]

omit [LawfulFcMap map Root] in
/-- An entry after one handler event was there before, or the event is an attestation that
wrote it (`AttWrite`). The store before the event meets `StorePure`. -/
theorem HandlerEvent.run_latest_source (e : HandlerEvent) (s s' : Store map)
    (hsp : StorePure s)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) (i : ValidatorIndex)
    (q : LatestMessage) (hq : FcMap.lookup s'.latestMessages i = some q) :
    FcMap.lookup s.latestMessages i = some q ∨
      ∃ att fb, e = .attestation att fb ∧ AttWrite s att i ∧ q = attMessage att := by
  by_cases he : ∃ att fb, e = .attestation att fb
  · obtain ⟨att, fb, rfl⟩ := he
    obtain ⟨b, cs, u, u', cps, s2, ts, A, hb, hslot, hcs, hge, hmid, hts, hA, rfl⟩ :=
      onAttestation_run_ok att fb s s' hsp h
    rw [updateLatestMessages_eq] at hq
    rcases latestFold_source _ att i _ _ q hq with h0 | ⟨hi, hc, hqa⟩
    · exact Or.inl h0
    · exact Or.inr ⟨att, fb, rfl,
        ⟨⟨b, hb, hslot⟩, ⟨cs, u, u', hcs, hge⟩, ⟨A, ⟨cps, s2, ts, hmid, hts, hA⟩,
          Array.mem_toList_iff.mp hi⟩, hc⟩, hqa⟩
  · have hne : ∀ att fb, e ≠ .attestation att fb := fun att fb h' => he ⟨att, fb, h'⟩
    rw [HandlerEvent.run_keeps_latest e s s' h hne] at hq
    exact Or.inl hq

omit [LawfulFcMap map Root]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- An attestation event delivers the vote of `i`. `i` is an attesting index at `pre`, and
not an equivocator in `pre`. Then the entry of `i` after the event has at least the vote
slot. The store `pre` meets `StorePure`. -/
theorem onAttestation_delivers (hsort : QsortMem) (att : Attestation) (fb : Bool)
    (pre post : Store map) (hsp : StorePure pre)
    (h : (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
      fb).run pre = .ok ((), post))
    (i : ValidatorIndex) (hatt : ∀ A, AttIndices pre att A → i ∈ A)
    (hne : pre.equivocatingIndices.contains i = false) :
    ∃ q, FcMap.lookup post.latestMessages i = some q ∧ att.data.slot ≤ q.slot := by
  obtain ⟨-, -, -, -, cps, s2, ts, A, -, -, -, -, hmid, hts, hA, rfl⟩ :=
    onAttestation_run_ok att fb pre post hsp h
  have hi : i ∈ A := hatt A ⟨cps, s2, ts, hmid, hts, hA⟩
  rw [updateLatestMessages_eq]
  exact latestFold_delivered _ att i hne _ _ (Array.mem_toList_iff.mpr ((hsort A i).mpr hi))

/-- Where an entry at the end of a trace comes from: the seed, or an attestation event of
the trace that wrote it in the store before that event. The seed meets `StorePure`. -/
theorem NodeTrace.latest_source {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (h0 : StorePure s0)
    (i : ValidatorIndex) (q : LatestMessage) (hq : FcMap.lookup s.latestMessages i = some q) :
    FcMap.lookup s0.latestMessages i = some q ∨
      ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool) (pre : Store map)
        (arr arr2 : List (SignedInclusionList × UInt64)),
        events = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
        NodeTrace s0 es1 arr pre ∧
        NodeTrace pre (TraceEvent.handler (.attestation att fb) :: es2) arr2 s ∧
        AttWrite pre att i ∧ q = attMessage att := by
  revert hq
  induction h with
  | nil => exact .inl
  | @handler events arrs mid post e htrace hrun ih =>
    intro hq
    rcases HandlerEvent.run_latest_source e _ _ (htrace.storePure h0) hrun i q hq with
      hprev | ⟨att, fb, rfl, hw, hqa⟩
    · rcases ih hprev with h0 | ⟨es1, es2, att, fb, pre, arr, arr2, hev, htr, hsuf, hw, hqa⟩
      · exact .inl h0
      · refine .inr ⟨es1, es2 ++ [.handler e], att, fb, pre, arr, arr2, by simp [hev], htr, ?_,
          hw, hqa⟩
        have := NodeTrace.handler e hsuf hrun
        simpa using this
    · refine .inr ⟨_, [], att, fb, _, _, [], rfl, htrace, ?_, hw, hqa⟩
      simpa using NodeTrace.handler (s0 := mid) (.attestation att fb) NodeTrace.nil hrun
  | inclusionList signed t _ hclock hrun ih =>
    intro hq
    have hrun' := hrun
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun')] at hrun'
    injection hrun' with hrun'
    injection hrun' with _ hrun'
    rw [← hrun'] at hq
    rcases ih hq with h0 | ⟨es1, es2, att, fb, pre, arr, arr2, hev, htr, hsuf, hw, hqa⟩
    · exact .inl h0
    · refine .inr ⟨es1, es2 ++ [.inclusionList signed], att, fb, pre, arr, arr2 ++ [(signed, t)],
        by simp [hev], htr, ?_, hw, hqa⟩
      have := NodeTrace.inclusionList signed t hsuf hclock hrun
      simpa using this

end Trace

section Seed
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] [LawfulFcMap map ValidatorIndex]

/-- The seed of `getForkchoiceStore` has no latest message. -/
theorem getForkchoiceStore_latest (anchorState : BeaconState) (anchorBlock : BeaconBlock)
    (s0 : Store map) (h : getForkchoiceStore (pureState anchorState) anchorBlock = .ok s0)
    (i : ValidatorIndex) : FcMap.lookup s0.latestMessages i = none := by
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  exact LawfulFcMap.lookup_empty i

end Seed

end EthCLSpecs.Proofs.Heze
