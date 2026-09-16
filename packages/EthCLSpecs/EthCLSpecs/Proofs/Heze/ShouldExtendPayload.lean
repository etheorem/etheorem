import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's payload-extension decision

Heze's `shouldExtendPayload` follows the Gloas fork-choice decision flow and
inserts a FOCIL gate after payload verification, before the later timeliness,
data-availability, and proposer-boost logic.

This module states the complete `.run` equation at
`ForkChoiceStoreRun (Store map)`. The explicit argument `store` is the map
that is read. `runnerStore` is the runner state. Successful binds thread
intermediate states `s1`, `s2`, `s3`, and `s4`. A reject returns the error
alone and has no post-state.

`isPayloadInclusionListSatisfied` looks up the satisfaction record, then
reads `isPayloadVerified`. `shouldExtendPayload` tests `isPayloadVerified`
before it calls that helper. An unverified payload therefore returns `false`
without reading the satisfaction map. A missing satisfaction record remains
the helper's membership assert after verification has passed.

The existing corollary `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`
is the recorded-`false` FOCIL rejection specialized to `.run store`.

After a recorded `true` with a verified payload, the remaining arms are the
inherited Gloas tail: `payloadTimeliness`, `payloadDataAvailability`, the
proposer-boost block lookup, and `isParentNodeFull`.

The bind lemmas used here are `GloasRun.run_bind` and the `Except` facts in
`EthCLSpecs.Proofs.Gloas.Run`. They are stated at an arbitrary state type, so
they apply to `ForkChoiceStoreRun`.

Verdict production lives in `recordPayloadInclusionListSatisfaction`.
Pairing of `payloads[root]` with the satisfaction entry, and composition of
that write with this read, are later handler postconditions.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd throwArithmetic StoreTransitionError
  SpecReject)
open EthCLSpecs.Heze (Preset Config Store shouldExtendPayload isPayloadInclusionListSatisfied
  isPayloadVerified getCurrentSlot payloadTimeliness payloadDataAvailability isParentNodeFull
  fcZeroRoot Root Slot BeaconBlock)

/-- `.run` of `throwArithmetic` at `ForkChoiceStoreRun`. `GloasRun.run_throw`
does not apply: `throwArithmetic` is `liftErr` of a `StateTransitionError`,
and the store machine wraps that as `.transition`. -/
private theorem throwArithmetic_run :
    ∀ {σ α : Type} (descr : String) (s : σ),
      (throwArithmetic (m := ForkChoiceStoreRun σ) (E := StoreTransitionError) descr
          : ForkChoiceStoreRun σ α).run s
        = .error (.transition (.arithmetic descr)) := by
  intro σ α descr s
  rfl

/-! ## Complete `.run` equation -/

/-- Complete compositional `.run` equation of `shouldExtendPayload` at
`ForkChoiceStoreRun (Store map)`. The right-hand side is the evaluation
order: block lookup, `getCurrentSlot.run`, the `slot + 1` overflow check,
the slot assertion, `isPayloadVerified`, `isPayloadInclusionListSatisfied.run`,
then the inherited Gloas tail. Successful binds keep `s1` through `s4`.
A reject is the error unchanged. -/
@[characterizes EthCLSpecs.Heze.shouldExtendPayload]
theorem shouldExtendPayload_run
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
        match FcMap.lookup store.blocks root with
        | none => .error (.missingKey root)
        | some rootBlock =>
          match (getCurrentSlot
              (StoreTransition := ForkChoiceStoreRun (Store map))
              store).run runnerStore with
          | .error err => .error err
          | .ok (currentSlot, s1) =>
            if rootBlock.slot + 1 < rootBlock.slot then
              .error (.transition (.arithmetic
                "should_extend_payload: blocks[root].slot + 1"))
            else
              let nextSlot := rootBlock.slot + 1
              if nextSlot == currentSlot then
                if !isPayloadVerified store root then
                  .ok (false, s1)
                else
                  match (isPayloadInclusionListSatisfied
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store root).run s1 with
                  | .error err => .error err
                  | .ok (false, s2) => .ok (false, s2)
                  | .ok (true, s2) =>
                    match (payloadTimeliness
                        (StoreTransition := ForkChoiceStoreRun (Store map))
                        store root true).run s2 with
                    | .error err => .error err
                    | .ok (payloadIsTimely, s3) =>
                      match (payloadDataAvailability
                          (StoreTransition := ForkChoiceStoreRun (Store map))
                          store root true).run s3 with
                      | .error err => .error err
                      | .ok (payloadDataIsAvailable, s4) =>
                        if (payloadIsTimely && payloadDataIsAvailable)
                            || store.proposerBoostRoot == fcZeroRoot then
                          .ok (true, s4)
                        else
                          match FcMap.lookup store.blocks store.proposerBoostRoot with
                          | none => .error (.missingKey store.proposerBoostRoot)
                          | some pb =>
                            if pb.parentRoot != root then .ok (true, s4)
                            else
                              (isParentNodeFull
                                  (StoreTransition := ForkChoiceStoreRun (Store map))
                                  store pb).run s4
              else
                .error (.assert "(nextSlot == currentSlot)") := by
  intro store runnerStore root
  simp [shouldExtendPayload, FcMap.getOrThrow, FcMap.getOrThrowKey, checkedAdd]
  cases hblock : FcMap.lookup store.blocks root with
  | none =>
    simp [GloasRun.run_throw, GloasRun.except_bind_error]
  | some rootBlock =>
    cases hcur : (getCurrentSlot
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run runnerStore with
    | error err =>
      simp [hcur, GloasRun.except_bind_error]
    | ok p =>
      obtain ⟨currentSlot, s1⟩ := p
      simp [hcur, GloasRun.except_bind_ok]
      by_cases hover : rootBlock.slot + 1 < rootBlock.slot
      · simp [hover, throwArithmetic_run, GloasRun.except_bind_error]
      · simp [hover]
        by_cases hslot : rootBlock.slot + 1 = currentSlot
        · simp [hslot]
          cases hverified : isPayloadVerified store root
          · simp
            rfl
          · simp
            cases hfocil : (isPayloadInclusionListSatisfied
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root).run s1 with
            | error err =>
              simp [GloasRun.except_bind_error]
            | ok q =>
              obtain ⟨satisfied, s2⟩ := q
              simp [GloasRun.except_bind_ok]
              cases satisfied
              · rfl
              · simp
                cases htime : (payloadTimeliness
                    (StoreTransition := ForkChoiceStoreRun (Store map))
                    store root true).run s2 with
                | error err =>
                  simp [GloasRun.except_bind_error]
                | ok r =>
                  obtain ⟨payloadIsTimely, s3⟩ := r
                  simp [GloasRun.except_bind_ok]
                  cases hda : (payloadDataAvailability
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store root true).run s3 with
                  | error err =>
                    simp [GloasRun.except_bind_error]
                  | ok s =>
                    obtain ⟨payloadDataIsAvailable, s4⟩ := s
                    simp [GloasRun.except_bind_ok]
                    by_cases hacc :
                        payloadIsTimely = true ∧ payloadDataIsAvailable = true
                          ∨ store.proposerBoostRoot = fcZeroRoot
                    · simp [hacc]
                      rfl
                    · simp [hacc]
                      cases hpb : FcMap.lookup store.blocks store.proposerBoostRoot with
                      | none =>
                        simp [GloasRun.run_throw, GloasRun.except_bind_error]
                      | some pb =>
                        simp
                        by_cases hparent : pb.parentRoot = root
                        · simp [hparent]
                        · simp [hparent]
                          rfl
        · simp [hslot, GloasRun.run_throw, GloasRun.except_bind_error, SpecReject.assert]

/-! ## Prefix rejects -/

/-- A missing `store.blocks[root]` entry is `missingKey`. -/
theorem shouldExtendPayload_run_error_of_missing_block
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.blocks root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.missingKey root) := by
  intro store runnerStore root hblock
  rw [shouldExtendPayload_run]
  simp [hblock]

/-- A `getCurrentSlot` reject is propagated unchanged. -/
theorem shouldExtendPayload_run_error_of_getCurrentSlot
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root) (rootBlock : BeaconBlock)
      (err : StoreTransitionError),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .error err →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error err := by
  intro store runnerStore root rootBlock err hblock hcur
  rw [shouldExtendPayload_run]
  simp [hblock, hcur]

/-- Overflow of `blocks[root].slot + 1` is the arithmetic fault named by
`checkedAdd`. -/
theorem shouldExtendPayload_run_error_of_slot_overflow
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot + 1 < rootBlock.slot →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.transition (.arithmetic
            "should_extend_payload: blocks[root].slot + 1")) := by
  intro store runnerStore s1 root rootBlock currentSlot hblock hcur hover
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hover]

/-- A successful increment that fails `nextSlot == currentSlot` is the spec's
slot assertion. -/
theorem shouldExtendPayload_run_error_of_slot_assert
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 ≠ currentSlot →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "(nextSlot == currentSlot)") := by
  intro store runnerStore s1 root rootBlock currentSlot hblock hcur hnooverflow hslot
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hnooverflow, hslot]

/-! ## FOCIL gate -/

/-- An unverified payload returns `false` after the block and slot prefix.
The helper is not called. The runner state is `s1`. -/
theorem shouldExtendPayload_run_eq_false_of_unverified
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = false →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, s1) := by
  intro store runnerStore s1 root rootBlock currentSlot hblock hcur hnooverflow hslot hverified
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hnooverflow]
  simp [hslot, hverified]

/-- A missing satisfaction record, after verification, is the helper's
membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_focil_record
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_inclusion_list_satisfaction") := by
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hnooverflow hslot hverified hlookup
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hnooverflow]
  simp [hslot, hverified]
  rw [isPayloadInclusionListSatisfied_run_error_of_missing_record store s1 root hlookup]

/-- A verified payload with a recorded `false` inclusion-list satisfaction
verdict is rejected by the FOCIL gate. `hverified` selects that branch.
The converse is not claimed. -/
theorem shouldExtendPayload_run_eq_false_of_recorded_unsatisfied
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (shouldExtendPayload (StoreTransition := ForkChoiceStoreRun (Store map)) store root).run
          store
        = .ok (false, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied
  rw [shouldExtendPayload_run]
  simp [hblock, hcurrentslot, hnooverflow, hverified]
  rw [isPayloadInclusionListSatisfied_run]
  simp [hunsatisfied]

/-- A recorded `true` with a verified payload continues into the inherited
Gloas tail at `s1`. The helper leaves that runner state unchanged. -/
theorem shouldExtendPayload_run_eq_of_recorded_satisfied
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
        match (payloadTimeliness
            (StoreTransition := ForkChoiceStoreRun (Store map))
            store root true).run s1 with
        | .error err => .error err
        | .ok (payloadIsTimely, s3) =>
          match (payloadDataAvailability
              (StoreTransition := ForkChoiceStoreRun (Store map))
              store root true).run s3 with
          | .error err => .error err
          | .ok (payloadDataIsAvailable, s4) =>
            if (payloadIsTimely && payloadDataIsAvailable)
                || store.proposerBoostRoot == fcZeroRoot then
              .ok (true, s4)
            else
              match FcMap.lookup store.blocks store.proposerBoostRoot with
              | none => .error (.missingKey store.proposerBoostRoot)
              | some pb =>
                if pb.parentRoot != root then .ok (true, s4)
                else
                  (isParentNodeFull
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store pb).run s4 := by
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hnooverflow hslot hverified hlookup
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hnooverflow]
  simp [hslot, hverified]
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup, hverified]

/-! ## Inherited Gloas tail -/

/-- The inherited timeliness helper's membership assert on a missing vote
key. `GloasRun.run_throw` matches this `throw` of a store-machine `.assert`. -/
private theorem payloadTimeliness_run_error_of_missing_vote
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadTimelinessVote root = none →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run runnerStore
        = .error (.assert "root in store.payload_timeliness_vote") := by
  intro store runnerStore root hlookup
  simp [payloadTimeliness, FcMap.getOrAssert, hlookup, GloasRun.run_throw,
    GloasRun.except_bind_error]

/-- The inherited data-availability helper's membership assert on a missing
vote key. -/
private theorem payloadDataAvailability_run_error_of_missing_vote
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadDataAvailabilityVote root = none →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run runnerStore
        = .error (.assert "root in store.payload_data_availability_vote") := by
  intro store runnerStore root hlookup
  simp [payloadDataAvailability, FcMap.getOrAssert, hlookup, GloasRun.run_throw,
    GloasRun.except_bind_error]

/-- A missing timeliness-vote record is the spec's membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_timeliness_vote
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      FcMap.lookup store.payloadTimelinessVote root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_timeliness_vote") := by
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hnooverflow hslot hverified hsat htime
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  rw [payloadTimeliness_run_error_of_missing_vote store s1 root htime]

/-- A missing data-availability-vote record is the spec's membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_data_availability_vote
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      FcMap.lookup store.payloadDataAvailabilityVote root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_data_availability_vote") := by
  intro store runnerStore s1 s3 root rootBlock currentSlot payloadIsTimely
    hblock hcur hnooverflow hslot hverified hsat htime hda
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  simp [htime]
  rw [payloadDataAvailability_run_error_of_missing_vote store s3 root hda]

/-- The Gloas tail accepts when the payload is timely and available, or when
the proposer-boost root is unset. The runner state is `s4`. -/
theorem shouldExtendPayload_run_eq_true_of_timely_available_or_zero_boost
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s3
        = .ok (payloadDataIsAvailable, s4) →
      ((payloadIsTimely && payloadDataIsAvailable)
          || store.proposerBoostRoot == fcZeroRoot) = true →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (true, s4) := by
  intro store runnerStore s1 s3 s4 root rootBlock currentSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hnooverflow hslot hverified hsat htime hda hacc
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc]

/-- A missing proposer-boost block is `missingKey` of that boost root. -/
theorem shouldExtendPayload_run_error_of_missing_proposer_block
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s3
        = .ok (payloadDataIsAvailable, s4) →
      ((payloadIsTimely && payloadDataIsAvailable)
          || store.proposerBoostRoot == fcZeroRoot) = false →
      FcMap.lookup store.blocks store.proposerBoostRoot = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.missingKey store.proposerBoostRoot) := by
  intro store runnerStore s1 s3 s4 root rootBlock currentSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hnooverflow hslot hverified hsat htime hda hacc hpb
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb]

/-- When the boost block's parent is not `root`, the Gloas tail accepts.
The runner state is `s4`. -/
theorem shouldExtendPayload_run_eq_true_of_proposer_parent_ne
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s3
        = .ok (payloadDataIsAvailable, s4) →
      ((payloadIsTimely && payloadDataIsAvailable)
          || store.proposerBoostRoot == fcZeroRoot) = false →
      FcMap.lookup store.blocks store.proposerBoostRoot = some pb →
      pb.parentRoot ≠ root →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (true, s4) := by
  intro store runnerStore s1 s3 s4 root rootBlock pb currentSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hnooverflow hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- When the boost block's parent is `root`, the decision is
`isParentNodeFull.run s4`. -/
theorem shouldExtendPayload_run_eq_of_isParentNodeFull
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s3
        = .ok (payloadDataIsAvailable, s4) →
      ((payloadIsTimely && payloadDataIsAvailable)
          || store.proposerBoostRoot == fcZeroRoot) = false →
      FcMap.lookup store.blocks store.proposerBoostRoot = some pb →
      pb.parentRoot = root →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
        (isParentNodeFull
            (StoreTransition := ForkChoiceStoreRun (Store map))
            store pb).run s4 := by
  intro store runnerStore s1 s3 s4 root rootBlock pb currentSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hnooverflow hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hnooverflow hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- The inherited Gloas rejection: `isParentNodeFull` returns `false`.
The runner state is that helper's post-state `s5`. -/
theorem shouldExtendPayload_run_eq_false_of_parent_node_not_full
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store runnerStore s1 s3 s4 s5 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      rootBlock.slot + 1 = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s1
        = .ok (payloadIsTimely, s3) →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run s3
        = .ok (payloadDataIsAvailable, s4) →
      ((payloadIsTimely && payloadDataIsAvailable)
          || store.proposerBoostRoot == fcZeroRoot) = false →
      FcMap.lookup store.blocks store.proposerBoostRoot = some pb →
      pb.parentRoot = root →
      (isParentNodeFull
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store pb).run s4
        = .ok (false, s5) →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, s5) := by
  intro store runnerStore s1 s3 s4 s5 root rootBlock pb currentSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hnooverflow hslot hverified hsat htime hda hacc hpb hparent hfull
  have htail :=
    shouldExtendPayload_run_eq_of_isParentNodeFull
      store runnerStore s1 s3 s4 root rootBlock pb currentSlot
      payloadIsTimely payloadDataIsAvailable
      hblock hcur hnooverflow hslot hverified hsat htime hda hacc hpb hparent
  rw [htail, hfull]

end EthCLSpecs.Proofs.Heze
