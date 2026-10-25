import EthCLSpecs.Proofs.Heze.HonestDuties
import EthCLSpecs.Proofs.Heze.Equivocators

/-!
# `EthCLSpecs.Proofs.Heze.TraceFacts`: blocks, clocks, and signers along a trace

`PayloadRaceExec.lean` follows a vote from the store that handled it to a later store of the
same node. This module holds the facts about traces that the argument needs.

- `NodeTrace.single_handler`: a trace of one handler event is one run of the handler.
- `NodeTrace.blocks_persist`: a key of the block map stays a key. Only `onBlock` writes the
  map. It only inserts.
- `HonestSigner.prefix`: an honest signer of a trace is an honest signer of each prefix.
- `ClockedTrace.attestation_slot_le`: the current slot when an attestation event ran is no
  greater than the current slot of a later query. The wall times of a clocked trace do not
  decrease. A non-tick event runs on a store whose time is its wall time
  (`ClockedTrace.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Config Store State Root Slot BeaconBlock ValidatorIndex Attestation
  SignedInclusionList ExecutionPayload ExecutionRequests Transaction getCurrentSlot)

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- A trace of one handler event is one successful run of the handler. -/
theorem NodeTrace.single_handler {s0 s : Store map} {e : HandlerEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 [.handler e] arrivals s) :
    (HandlerEvent.run (map := map) e).run s0 = .ok ((), s) := by
  generalize hes : [TraceEvent.handler e] = es at h
  cases h with
  | nil => simp at hes
  | @handler events arrs prev _ e' hprev hrun =>
    have hlast := congrArg List.getLast? hes
    have hlen := congrArg List.length hes
    simp only [List.getLast?_singleton, List.getLast?_append, Option.some_or,
      Option.some.injEq, TraceEvent.handler.injEq] at hlast
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have hnil : events = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hlast hnil
    obtain ⟨-, rfl⟩ := hprev.nil_inv
    exact hrun
  | inclusionList signed t _ _ _ =>
    have hlast := congrArg List.getLast? hes
    simp at hlast

/-- An honest signer of a trace is an honest signer of each prefix. -/
theorem HonestSigner.prefix {s0 : Store map} {es1 es2 : List TraceEvent} {i : ValidatorIndex}
    (h : HonestSigner s0 (es1 ++ es2) i) : HonestSigner s0 es1 i := by
  intro f1 f2 asl pre arr st hev htr hst
  exact h f1 (f2 ++ es2) asl pre arr st (by simp [hev]) htr hst

variable [LawfulFcMap map Root]

/-- A key of the block map stays a key along a trace. `onBlock` inserts. The other handlers
keep the map. -/
theorem NodeTrace.blocks_persist {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (k : Root) (b : BeaconBlock) (hb : FcMap.lookup s0.blocks k = some b) :
    ∃ b', FcMap.lookup s.blocks k = some b' := by
  induction h with
  | nil => exact ⟨b, hb⟩
  | @handler events arrs pre post e _ hrun ih =>
    obtain ⟨b1, hb1⟩ := ih
    have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
        KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
          (pre.blocks, pre.blockStates) x →
        x.run pre = .ok ((), post) → ∃ b', FcMap.lookup post.blocks k = some b' := by
      intro x hx hrunx
      have hmaps := hx pre () post rfl hrunx
      injection hmaps with hblocks _
      exact ⟨b1, hblocks ▸ hb1⟩
    cases e with
    | tick time => exact hkeep _ (onTick_keeps_blockMaps _ time) hrun
    | attestation att isFromBlock =>
      exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) hrun
    | attesterSlashing asl => exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) hrun
    | payloadAttestation msg isFromBlock =>
      exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) hrun
    | block sb =>
      obtain ⟨hblocks, -⟩ := onBlock_run_maps sb pre post hrun
      rw [hblocks]
      by_cases hk : htr sb.message = k
      · exact ⟨sb.message, hk ▸ LawfulFcMap.lookup_insert_self _ _ _⟩
      · exact ⟨b1, (LawfulFcMap.lookup_insert_ne _ _ _ _ hk).trans hb1⟩
    | envelope signedEnv =>
      obtain ⟨hblocks, -⟩ := onExecutionPayloadEnvelope_run_keys signedEnv pre post hrun
      exact ⟨b1, hblocks ▸ hb1⟩
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

end

section Clock
variable {map : MapKind} [Preset] [HasherTag] [Config]

/-- The current slot does not decrease with the store time, when the two stores have the same
genesis time. -/
theorem getCurrentSlot_le_of_time (st₁ st₂ : Store map) (hg : st₁.genesisTime = st₂.genesisTime)
    (ht : st₁.time.toNat ≤ st₂.time.toNat) {u₁ u₁' u₂ u₂' : Store map} {cs₁ cs₂ : Slot}
    (h₁ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st₁).run u₁
      = .ok (cs₁, u₁'))
    (h₂ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st₂).run u₂
      = .ok (cs₂, u₂')) :
    cs₁.toNat ≤ cs₂.toNat := by
  obtain ⟨hle₁, -, hcs₁⟩ := getCurrentSlot_run_ok st₁ u₁ u₁' cs₁ h₁
  obtain ⟨hle₂, -, hcs₂⟩ := getCurrentSlot_run_ok st₂ u₂ u₂' cs₂ h₂
  rw [hcs₁, hcs₂]
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  rw [UInt64.toNat_sub_of_le _ _ hle₁, UInt64.toNat_sub_of_le _ _ hle₂, hg]
  omega

variable [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- An attestation event of a clocked trace ran at a current slot no greater than the
current slot of a later query. The query store `σ` follows the prefix `P` of the trace. Its
time is the wall time `w` in whole seconds. Every event of `P` has a wall time no greater than
`w`. -/
theorem ClockedTrace.attestation_slot_le {s0 s σ : Store map} {tevs P rest : List (TraceEvent × Nat)}
    {arrivals arr : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    (hsplit : tevs = P ++ rest) (hσ : NodeTrace s0 (P.map Prod.fst) arr σ) {w : Nat}
    (hwall : ∀ y ∈ P, y.2 ≤ w) (htime : σ.time.toNat = w / 1000)
    {es1 es2 : List TraceEvent} {att : Attestation} {fb : Bool}
    (hes : P.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2)
    {arr1 : List (SignedInclusionList × UInt64)} {mid : Store map}
    (hmid : NodeTrace s0 es1 arr1 mid) {u₁ u₁' u₂ u₂' : Store map} {cs₁ cs₂ : Slot}
    (h₁ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) mid).run u₁
      = .ok (cs₁, u₁'))
    (h₂ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) σ).run u₂
      = .ok (cs₂, u₂')) :
    cs₁.toNat ≤ cs₂.toNat := by
  obtain ⟨P1, P2', hP, hP1, hP2'⟩ := List.map_eq_append_iff.mp hes
  obtain ⟨x, P2, rfl, hx, -⟩ := List.map_eq_cons_iff.mp hP2'
  have hclock := hct.clock P1 x (P2 ++ rest) (by rw [hsplit, hP]; simp) arr1 mid (hP1 ▸ hmid)
  have hmidTime : mid.time.toNat = x.2 / 1000 := by
    unfold ClockAt at hclock
    rw [hx] at hclock
    exact hclock
  have hxw : x.2 ≤ w := hwall x (by rw [hP]; simp)
  have hg : mid.genesisTime = σ.genesisTime := hmid.genesisTime.trans hσ.genesisTime.symm
  refine getCurrentSlot_le_of_time mid σ hg ?_ h₁ h₂
  rw [hmidTime, htime]
  exact Nat.div_le_div_right hxw

end Clock

end EthCLSpecs.Proofs.Heze
