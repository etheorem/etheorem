import EthCLSpecs.Proofs.Heze.StorePure.Basic
import EthCLSpecs.Proofs.Heze.CheckpointOrd
import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.KeepsUncached.Slots

/-!
# `EthCLSpecs.Proofs.Heze.StorePure`: every handler keeps the store pure

`StorePure s` (`StorePure/Basic.lean`) says that every state in `blockStates` and
`checkpointStates` is `pureState` of a plain value. This module proves that the anchor
store of `getForkchoiceStore (pureState v)` meets it, that every handler keeps it, and so
that every store along a `NodeTrace` from that anchor meets it (`NodeTrace.storePure`).

Four code sites write a state into the store:

* `getForkchoiceStore` stores the anchor box in both maps (`StorePure.anchor`).
* `onBlock` stores the post-box of `stateTransition`, run from the parent state that it
  read from `blockStates`. `keepsUncached_stateTransition` says that the run keeps the
  uncached box (`onBlock_run_ok`).
* `onExecutionPayloadEnvelope` stores the box that `verifyExecutionPayloadEnvelope`
  returns. That box is the second component of `stateRoot` of the state it read, and on
  an uncached box `stateRoot` returns the same box (`onExecutionPayloadEnvelope_run_ok`).
* `onAttestation` stores, through `storeTargetCheckpointState`, the state that it read
  from `blockStates`, or the post-box of `processSlots` from it
  (`StorePure.storeTargetCheckpointState`).

The other handlers keep both maps, and the frame tactic proves it.

The `onBlock` and envelope inversions need only the `blockStates` half,
`BlockStatesPure`. They take it as a hypothesis and return the stored states as plain
values. `SlotInv` (`SlotsIncrease.lean`) carries that half, so it uses them without the
checkpoint half.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt KeepsUncached LawfulFcMap pureState
  run_bind_eq_ok run_get_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint BeaconBlock
  SignedBeaconBlock Attestation AttesterSlashing PayloadAttestationMessage
  SignedExecutionPayloadEnvelope getForkchoiceStore onBlock onAttestation onAttesterSlashing
  onPayloadAttestationMessage onExecutionPayloadEnvelope onTick storeTargetCheckpointState
  verifyExecutionPayloadEnvelope stateTransition)

section Inserts
variable [Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- A step that keeps both state maps keeps the invariant. -/
theorem StorePure.of_maps_eq {pre post : Store map} (hp : StorePure pre)
    (hb : post.blockStates = pre.blockStates)
    (hc : post.checkpointStates = pre.checkpointStates) : StorePure post :=
  ⟨fun k => hb ▸ hp.blockStates k, fun c => hc ▸ hp.checkpointStates c⟩

variable [LawfulFcMap map Root]

/-- An insert of the uncached box of `v` into `blockStates` keeps `BlockStatesPure`. -/
theorem BlockStatesPure.insert {pre post : Store map} (hp : BlockStatesPure pre) (k : Root)
    (v : BeaconState) (hb : post.blockStates = FcMap.insert pre.blockStates k (pureState v)) :
    BlockStatesPure post := by
  intro k'
  rw [hb]
  by_cases hk : k = k'
  · subst hk
    exact ⟨some v, by rw [EthCLLib.Proofs.FcMap.lookup_insert_self]; rfl⟩
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk]
    exact hp k'

/-- The anchor store of `getForkchoiceStore` from the uncached box of `v` meets
`BlockStatesPure`: `blockStates` holds `pureState v` at one key and nothing else. -/
theorem BlockStatesPure.anchor [Config] (v : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : getForkchoiceStore (pureState v) a = .ok s0) : BlockStatesPure s0 := by
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  intro k
  by_cases hk : htr a = k
  · subst hk
    exact ⟨some v, by rw [EthCLLib.Proofs.FcMap.lookup_insert_self]; rfl⟩
  · exact ⟨none, by rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk, LawfulFcMap.lookup_empty]; rfl⟩

variable [LawfulFcMap map Checkpoint]

omit [LawfulFcMap map Checkpoint] in
/-- A step that inserts the uncached box of `v` into `blockStates`, and keeps
`checkpointStates`, keeps the invariant. -/
theorem StorePure.insert_blockState {pre post : Store map} (hp : StorePure pre) (k : Root)
    (v : BeaconState) (hb : post.blockStates = FcMap.insert pre.blockStates k (pureState v))
    (hc : post.checkpointStates = pre.checkpointStates) : StorePure post :=
  ⟨hp.blockStates.insert k v hb, fun c => hc ▸ hp.checkpointStates c⟩

omit [LawfulFcMap map Root] in
/-- A step that keeps `blockStates`, and inserts the uncached box of `v` into
`checkpointStates`, keeps the invariant. -/
theorem StorePure.insert_checkpointState {pre post : Store map} (hp : StorePure pre)
    (c : Checkpoint) (v : BeaconState) (hb : post.blockStates = pre.blockStates)
    (hc : post.checkpointStates = FcMap.insert pre.checkpointStates c (pureState v)) :
    StorePure post := by
  refine ⟨fun k => hb ▸ hp.blockStates k, fun c' => ?_⟩
  rw [hc]
  by_cases h : c = c'
  · subst h
    exact ⟨some v, by rw [EthCLLib.Proofs.FcMap.lookup_insert_self]; rfl⟩
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ h]
    exact hp.checkpointStates c'

/-- The anchor store of `getForkchoiceStore` from the uncached box of `v` meets the
invariant: each map holds `pureState v` at one key and nothing else. -/
theorem StorePure.anchor [Config] (v : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : getForkchoiceStore (pureState v) a = .ok s0) : StorePure s0 := by
  refine ⟨BlockStatesPure.anchor v a s0 h, ?_⟩
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  intro c
  by_cases hc : ({ epoch := EthCLSpecs.Heze.currentEpochOf (pureState v), root := htr a } :
      Checkpoint) = c
  · subst hc
    exact ⟨some v, by rw [EthCLLib.Proofs.FcMap.lookup_insert_self]; rfl⟩
  · exact ⟨none, by rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hc, LawfulFcMap.lookup_empty]; rfl⟩

end Inserts

section Runs
variable [Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- A successful `getOrAssert` read found its value at the key, and kept the store. -/
theorem getOrAssert_run_eq_ok {K V : Type} [Ord K] [BEq K] [Hashable K] (mp : map K V)
    (k : K) (d : String) (s : Store map) (v : V) (s' : Store map)
    (h : (FcMap.getOrAssert mp k d : ForkChoiceStoreRun (Store map) V).run s = .ok (v, s')) :
    FcMap.lookup mp k = some v ∧ s' = s := by
  unfold FcMap.getOrAssert at h
  split at h
  · rename_i v' hv
    injection h with h
    injection h with hv' hs
    exact ⟨hv'.symm ▸ hv, hs.symm⟩
  · cases h

omit [FcMap map] in
/-- A successful nested state transition from the uncached box of `pre`, followed by `f`.
The transition ran from `pureState pre` to the uncached box of some `w`, when it keeps the
uncached box. Then `f` ran on that box, from the same store. -/
theorem runNestedStateTransition_bind_eq_ok {α : Type} (pre : BeaconState)
    (act : HezeRun Unit) (hk : KeepsUncached act)
    (f : State → ForkChoiceStoreRun (Store map) α) (s : Store map) (r : α × Store map)
    (h : (runNestedStateTransition (m := ForkChoiceStoreRun (Store map)) (pureState pre) act
      >>= f).run s = .ok r) :
    ∃ w : BeaconState, act.run (pureState pre) = .ok ((), pureState w) ∧
      (f (pureState w)).run s = .ok r := by
  obtain ⟨v, s1, hn, hf⟩ := run_bind_eq_ok _ _ _ _ h
  cases hact : act.run (pureState pre) with
  | error e =>
    rw [runNestedStateTransition_of_error hact] at hn
    cases hn
  | ok p =>
    obtain ⟨⟨⟩, post⟩ := p
    rw [runNestedStateTransition_of_ok hact] at hn
    injection hn with hn
    injection hn with hv hs
    subst hv hs
    have hpost := hk pre () post hact
    rw [hpost] at hf
    exact ⟨post.view, hpost ▸ rfl, hf⟩

variable [Config] [CryptoBackend]

/-- A successful `onBlock` run read the parent state of the block, ran the state transition
from it, and inserted the block and the post-state at the block root. Under
`BlockStatesPure`, the parent state is the uncached box of `pv`, and the post-state is the
uncached box of `w`. The handler writes neither map again after that insert. -/
theorem onBlock_run_ok (sb : SignedBeaconBlock) (pre post : Store map)
    (hp : BlockStatesPure pre)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    ∃ pv w : BeaconState,
      FcMap.lookup pre.blockStates sb.message.parentRoot = some (pureState pv) ∧
      (stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
        = .ok ((), pureState w) ∧
      post.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message ∧
      post.blockStates = FcMap.insert pre.blockStates (htr sb.message) (pureState w) := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The parent state, read with `getOrAssert`. It is the uncached box of `pv`.
  obtain ⟨parentState, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, -⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  obtain ⟨pv, hpv⟩ := hp.lookup _ (by rw [hlookup]; rfl)
  rw [hpv] at hlookup
  injection hlookup with hlookup
  subst hlookup
  -- The parent-payload check, the clock check, the checked finalized slot, and the finality
  -- checks.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The state transition.
  obtain ⟨w, htrans, h⟩ :=
    runNestedStateTransition_bind_eq_ok pv _ (keepsUncached_stateTransition sb true) _ _ _ h
  -- The head, then the insert.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, t, hset, hcont⟩ := run_bind_eq_ok _ _ _ _ h
  have ht := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
  -- The rest of the handler keeps both maps.
  have hframe : (post.blocks, post.blockStates) = (t.blocks, t.blockStates) := by
    refine (?_ : KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
      (t.blocks, t.blockStates) _) t () post rfl hcont
    keeps_solve
  subst ht
  injection hframe with hblocks hstates
  exact ⟨pv, w, hpv, htrans, hblocks, hstates⟩

/-- A successful `onBlock` run inserted the block at its root, and it added to
`blockStates` no key other than that root. The form for a caller that needs the block map
and the keys of `blockStates` only. -/
theorem onBlock_run_maps [LawfulFcMap map Root] (sb : SignedBeaconBlock) (pre post : Store map)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    post.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message ∧
      ∀ k, (FcMap.lookup post.blockStates k).isSome →
        k = htr sb.message ∨ (FcMap.lookup pre.blockStates k).isSome := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The parent read, the checks, and the checked finalized slot.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The state transition, the head, then the insert.
  obtain ⟨postState, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, t, hset, hcont⟩ := run_bind_eq_ok _ _ _ _ h
  have ht := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
  -- The rest of the handler keeps both maps.
  have hframe : (post.blocks, post.blockStates) = (t.blocks, t.blockStates) := by
    refine (?_ : KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
      (t.blocks, t.blockStates) _) t () post rfl hcont
    keeps_solve
  subst ht
  injection hframe with hblocks hstates
  refine ⟨hblocks, fun k hk => ?_⟩
  rw [hstates] at hk
  by_cases hkr : k = htr sb.message
  · exact Or.inl hkr
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ (fun h => hkr h.symm)] at hk
    exact Or.inr hk

section EngineSeam
variable [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

omit [DataAvailability] in
/-- `verifyExecutionPayloadEnvelope` on the uncached box of `v` returns that box, when it
succeeds. The box it returns is the second component of `stateRoot` of its input, and on an
uncached box `stateRoot` returns the same box. The statement names the box as the image of
the result, so it binds no box. -/
theorem verifyExecutionPayloadEnvelope_pure (v : BeaconState)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    (verifyExecutionPayloadEnvelope (pureState v) signedEnv).map (fun _ => pureState v)
      = verifyExecutionPayloadEnvelope (pureState v) signedEnv := by
  cases hx : verifyExecutionPayloadEnvelope (pureState v) signedEnv with
  | error e => rfl
  | ok w =>
    show Except.ok (pureState v) = Except.ok w
    unfold verifyExecutionPayloadEnvelope at hx
    -- Peel the binds and the asserts of the `Except` block up to its `return`.
    repeat (first | (obtain ⟨_, -, hx⟩ := except_bind_eq_ok hx) | split at hx)
    -- The `return` hands back the second component of `stateRoot (pureState v)`, which is
    -- `pureState v` by `hashTreeRoot_uncachedBox`.
    exact hx

/-- A successful envelope run keeps the block map. It read the uncached box of `v` at the
envelope root, under `BlockStatesPure`, and stored that box back at the same key
(`verifyExecutionPayloadEnvelope_pure`). -/
theorem onExecutionPayloadEnvelope_run_ok (signedEnv : SignedExecutionPayloadEnvelope)
    (pre post : Store map) (hp : BlockStatesPure pre)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    post.blocks = pre.blocks ∧
      ∃ v : BeaconState,
        FcMap.lookup pre.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) ∧
        post.blockStates
          = FcMap.insert pre.blockStates signedEnv.message.beaconBlockRoot (pureState v) := by
  have hblocks : post.blocks = pre.blocks := by
    refine (?_ : KeepsAt (fun st : Store map => st.blocks) pre.blocks _) pre () post rfl h
    unfold onExecutionPayloadEnvelope
    keeps_solve
  refine ⟨hblocks, ?_⟩
  unfold onExecutionPayloadEnvelope at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨state, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, -⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  obtain ⟨v, hv⟩ := hp.lookup _ (by rw [hlookup]; rfl)
  rw [hv] at hlookup
  injection hlookup with hlookup
  subst hlookup
  -- The availability check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · rename_i warm hverify
    -- The box that the check returns is the box that it read.
    have hw : warm = pureState v := by
      have hm := verifyExecutionPayloadEnvelope_pure v signedEnv
      rw [hverify] at hm
      injection hm with hm
      exact hm.symm
    -- The answer record returns the store it read, with the answer map written.
    obtain ⟨store', _, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    have hstore' : store'.blockStates = pre.blockStates :=
      (?_ : EthCLLib.Proofs.Returns (fun st : Store map => st.blockStates) pre.blockStates _)
        _ _ _ hrec
    · have ht := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
      refine ⟨v, hv, ?_⟩
      rw [ht]
      show FcMap.insert store'.blockStates _ warm = _
      rw [hstore', hw]
    · keeps_solve

/-- A successful envelope run keeps the block map, and adds no key to `blockStates`. It
writes `blockStates` only at the envelope root, where it read a state. The form for a
caller that needs the keys only. -/
theorem onExecutionPayloadEnvelope_run_keys [LawfulFcMap map Root]
    (signedEnv : SignedExecutionPayloadEnvelope) (pre post : Store map)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    post.blocks = pre.blocks ∧
      ∀ k, (FcMap.lookup post.blockStates k).isSome →
        (FcMap.lookup pre.blockStates k).isSome := by
  have hblocks : post.blocks = pre.blocks := by
    refine (?_ : KeepsAt (fun st : Store map => st.blocks) pre.blocks _) pre () post rfl h
    unfold onExecutionPayloadEnvelope
    keeps_solve
  refine ⟨hblocks, fun k hk => ?_⟩
  unfold onExecutionPayloadEnvelope at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, _, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, -⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  -- The availability check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · rename_i warm _
    -- The answer record returns the store it read, with the answer map written.
    obtain ⟨store', _, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    have hstore' : store'.blockStates = pre.blockStates :=
      (?_ : EthCLLib.Proofs.Returns (fun st : Store map => st.blockStates) pre.blockStates _)
        _ _ _ hrec
    · have ht := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
      rw [ht] at hk
      change (FcMap.lookup (FcMap.insert store'.blockStates _ warm) k).isSome = true at hk
      rw [hstore'] at hk
      by_cases hkr : signedEnv.message.beaconBlockRoot = k
      · subst hkr
        rw [hlookup]
        rfl
      · rwa [LawfulFcMap.lookup_insert_ne _ _ _ _ hkr] at hk
    · keeps_solve

end EngineSeam

end Runs

section Frames
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

omit [CryptoBackend] in
/-- `onTick` keeps `blocks` and `blockStates`. -/
theorem onTick_keeps_blockMaps (v : _) (time : UInt64) :
    KeepsAt (fun st : Store map => (st.blocks, st.blockStates)) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onAttestation` keeps `blocks` and `blockStates`. -/
theorem onAttestation_keeps_blockMaps (v : _) (att : Attestation) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => (st.blocks, st.blockStates)) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps `blocks` and `blockStates`. -/
theorem onAttesterSlashing_keeps_blockMaps (v : _) (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => (st.blocks, st.blockStates)) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps `blocks` and `blockStates`. -/
theorem onPayloadAttestationMessage_keeps_blockMaps (v : _) (msg : PayloadAttestationMessage)
    (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => (st.blocks, st.blockStates)) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

omit [CryptoBackend] in
/-- `onTick` keeps the checkpoint states. -/
theorem onTick_keeps_checkpointStates (v : map Checkpoint State) (time : UInt64) :
    KeepsAt (fun st : Store map => st.checkpointStates) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the checkpoint states. -/
theorem onBlock_keeps_checkpointStates (v : map Checkpoint State)
    (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.checkpointStates) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        signedBlock) := by
  unfold onBlock
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the checkpoint states. -/
theorem onAttesterSlashing_keeps_checkpointStates (v : map Checkpoint State)
    (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => st.checkpointStates) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the checkpoint states. -/
theorem onPayloadAttestationMessage_keeps_checkpointStates (v : map Checkpoint State)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.checkpointStates) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

section EngineSeam
variable [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the checkpoint states. -/
theorem onExecutionPayloadEnvelope_keeps_checkpointStates (v : map Checkpoint State)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.checkpointStates) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

end EngineSeam

end Frames

section Handlers
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map Checkpoint]

omit [LawfulFcMap map Checkpoint] in
/-- `onBlock` keeps the invariant. It inserts the uncached post-box of `stateTransition`
into `blockStates` (`onBlock_run_ok`), and it keeps `checkpointStates`. -/
theorem StorePure.onBlock {pre post : Store map} (hp : StorePure pre) (sb : SignedBeaconBlock)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) : StorePure post := by
  obtain ⟨_, w, -, -, -, hstates⟩ := onBlock_run_ok sb pre post hp.blockStates h
  exact hp.insert_blockState _ w hstates
    (onBlock_keeps_checkpointStates _ sb pre () post rfl h)

omit [LawfulFcMap map Root] in
/-- `storeTargetCheckpointState` returns a store that meets the invariant, when its input
store does. The returned store keeps `checkpointStates`, or inserts the target state. That
state is the block state that it read, which is `pureState bv` by the invariant, or the
post-box of `processSlots` from it, which is uncached by `keepsUncached_processSlots`. -/
theorem StorePure.storeTargetCheckpointState {st : Store map} (hp : StorePure st)
    (target : Checkpoint) (s s' mid : Store map)
    (h : (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) st
      target).run s = .ok (mid, s')) : StorePure mid := by
  unfold EthCLSpecs.Heze.storeTargetCheckpointState at h
  split at h
  · -- The target state is already cached: the step returns its store.
    rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h]
    exact hp
  · obtain ⟨base, s3, hbase, h⟩ := run_bind_eq_ok _ _ _ _ h
    have hlookup : FcMap.lookup st.blockStates target.root = some base := by
      unfold FcMap.getOrThrow FcMap.getOrThrowKey at hbase
      split at hbase
      · rename_i b hb'
        rw [hb', EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbase]
      · cases hbase
    obtain ⟨bv, hbv⟩ := hp.blockStates_some _ (by rw [hlookup]; rfl)
    rw [hbv] at hlookup
    injection hlookup with hlookup
    subst hlookup
    dsimp only at h
    -- The checked start slot of the target epoch.
    obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    -- The advanced state is the uncached post-box of `processSlots`, or `pureState bv`.
    split at h
    · obtain ⟨adv, -, h⟩ :=
        runNestedStateTransition_bind_eq_ok bv _ (keepsUncached_processSlots _) _ _ _ h
      rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h]
      exact hp.insert_checkpointState target adv rfl rfl
    · obtain ⟨adv, s4, hadv, h⟩ := run_bind_eq_ok _ _ _ _ h
      have hadv' := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hadv
      subst hadv'
      rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h]
      exact hp.insert_checkpointState target bv rfl rfl

omit [LawfulFcMap map Root] in
/-- `onAttestation` keeps the invariant. Its target step, `storeTargetCheckpointState`,
returns a store that meets it. The rest of the handler writes only the latest messages
of that store. -/
theorem StorePure.onAttestation {pre post : Store map} (hp : StorePure pre) (att : Attestation)
    (isFromBlock : Bool)
    (h : (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
      isFromBlock).run pre = .ok ((), post)) : StorePure post := by
  unfold EthCLSpecs.Heze.onAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, s1, hval, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The checks read the store and do not change the runner state.
  have hk : KeepsAt (fun st : Store map => st) pre
      (EthCLSpecs.Heze.validateOnAttestation (StoreTransition := ForkChoiceStoreRun (Store map))
        pre att isFromBlock) := by
    keeps_solve
  have hs1 : s1 = pre := hk pre () s1 rfl hval
  rw [hs1] at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨mid, s2, hmid, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hpmid := hp.storeTargetCheckpointState att.data.target _ _ _ hmid
  -- The target read, the indices, the indexed attestation and its signature check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The validity check is an `Except` read, then its gate.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  -- The write: the latest messages of `mid`, with both state maps of `mid`.
  rw [EthCLLib.Proofs.run_set_state_eq _ _ _ _ h]
  exact hpmid.of_maps_eq rfl rfl

section EngineSeam
variable [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

omit [LawfulFcMap map Checkpoint] in
/-- `onExecutionPayloadEnvelope` keeps the invariant. It stores back the uncached box that
it read (`onExecutionPayloadEnvelope_run_ok`), and it keeps `checkpointStates`. -/
theorem StorePure.envelope {pre post : Store map} (hp : StorePure pre)
    (signedEnv : SignedExecutionPayloadEnvelope)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    StorePure post := by
  obtain ⟨-, v, -, hstates⟩ := onExecutionPayloadEnvelope_run_ok signedEnv pre post hp.blockStates h
  exact hp.insert_blockState _ v hstates
    (onExecutionPayloadEnvelope_keeps_checkpointStates _ signedEnv pre () post rfl h)

omit [LawfulFcMap map Checkpoint] in
/-- A handler event keeps `BlockStatesPure`. `onBlock` and the envelope handler insert an
uncached box, and the other handlers keep `blockStates`. -/
theorem BlockStatesPure.handler {pre post : Store map} (hp : BlockStatesPure pre)
    (e : HandlerEvent) (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) :
    BlockStatesPure post := by
  -- A handler that keeps `blockStates` keeps the predicate.
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      x.run pre = .ok ((), post) → BlockStatesPure post := by
    intro x hx hrun k
    have hm := hx pre () post rfl hrun
    injection hm with _ hb
    rw [hb]
    exact hp k
  cases e with
  | tick time => exact hkeep _ (onTick_keeps_blockMaps _ time) h
  | block sb =>
    obtain ⟨_, w, -, -, -, hstates⟩ := onBlock_run_ok sb pre post hp h
    exact hp.insert _ w hstates
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) h
  | attesterSlashing asl => exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) h
  | envelope signedEnv =>
    obtain ⟨-, v, -, hstates⟩ := onExecutionPayloadEnvelope_run_ok signedEnv pre post hp h
    exact hp.insert _ v hstates

omit [LawfulFcMap map Checkpoint] in
/-- `BlockStatesPure` along a trace. It needs only the law of the root map, so a caller
without the checkpoint half uses this form. -/
theorem NodeTrace.blockStatesPure {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (h0 : BlockStatesPure s0) : BlockStatesPure s := by
  induction h with
  | nil => exact h0
  | handler e _ hrun ih => exact ih.handler e hrun
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

/-- A handler event keeps the invariant. -/
theorem StorePure.handler {pre post : Store map} (hp : StorePure pre) (e : HandlerEvent)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) : StorePure post := by
  cases e with
  | tick time =>
    have hm := onTick_keeps_blockMaps _ time pre () post rfl h
    injection hm with _ hb
    exact hp.of_maps_eq hb (onTick_keeps_checkpointStates _ time pre () post rfl h)
  | block sb => exact hp.onBlock sb h
  | attestation att isFromBlock => exact hp.onAttestation att isFromBlock h
  | attesterSlashing asl =>
    have hm := onAttesterSlashing_keeps_blockMaps _ asl pre () post rfl h
    injection hm with _ hb
    exact hp.of_maps_eq hb (onAttesterSlashing_keeps_checkpointStates _ asl pre () post rfl h)
  | payloadAttestation msg isFromBlock =>
    have hm := onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock pre () post rfl h
    injection hm with _ hb
    exact hp.of_maps_eq hb
      (onPayloadAttestationMessage_keeps_checkpointStates _ msg isFromBlock pre () post rfl h)
  | envelope signedEnv => exact hp.envelope signedEnv h

/-- The invariant along a trace. A trace from a store that meets it ends in a store that
meets it. With `StorePure.anchor`, every store along a trace from the anchor store of
`getForkchoiceStore (pureState v)` meets it. -/
theorem NodeTrace.storePure {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (h0 : StorePure s0) : StorePure s := by
  induction h with
  | nil => exact h0
  | handler e _ hrun ih => exact ih.handler e hrun
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih.of_maps_eq rfl rfl

end EngineSeam

end Handlers

end EthCLSpecs.Proofs.Heze
