import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's payload-extension decision

Heze's `shouldExtendPayload` inserts a FOCIL gate after payload verification
and before the timeliness, data-availability, and proposer-boost checks.

The complete `.run` equation evaluates in this order: block lookup,
`getCurrentSlot.run`, the checked `nextSlot ← blocks[root].slot + 1` bind, the
slot assertion, `isPayloadVerified`, `isPayloadInclusionListSatisfied.run`, then the
remaining post-FOCIL checks (`payloadTimeliness`, `payloadDataAvailability`,
proposer-boost block lookup, and `isParentNodeFull`).

The explicit argument `store` is the map that is read. `runnerStore` is
the runner state. Successful binds thread intermediate states `s1`, `s2`,
`s3`, and `s4`. A reject returns the error alone and has no post-state.
The increment is the checked `Slot` add: its fault surfaces as the
`.arithmetic` fault carrying the repr of the exact `ArithFault`, so the
corollaries state the add's `.ok` or `.error` equation.

Private bridges stage the equation so each corollary states only its own
case. `shouldExtendPayload_run_eq_of_slot_prefix` reduces the successful
block-and-slot prefix to the post-prefix form. The recorded-satisfied and
`isParentNodeFull` bridges continue the ladder into the inherited Gloas
tail.

`isPayloadInclusionListSatisfied` looks up the satisfaction record, then
reads `isPayloadVerified`. `shouldExtendPayload` tests `isPayloadVerified`
before it calls that helper. An unverified payload therefore returns `false`
without reading the satisfaction map. A missing satisfaction record remains
the helper's membership assert after verification has passed.

The characterization is this compositional equation. It does not cover
`recordPayloadInclusionListSatisfaction`, and it does not prove that every
`false` result comes from a recorded-unsatisfied FOCIL value.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure run_throw run_liftM_error
  run_liftM_ok except_bind_ok except_bind_error ite_bind)
open EthCLLib.Spec (HasherTag MapKind FcMap Checked ArithFault StoreTransitionError)
open EthCLSpecs.Heze (Preset Config Store shouldExtendPayload isPayloadInclusionListSatisfied
  isPayloadVerified getCurrentSlot payloadTimeliness payloadDataAvailability isParentNodeFull
  fcZeroRoot Root Slot BeaconBlock)

variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-! ## Complete `.run` equation -/

/-- Complete compositional `.run` equation of `shouldExtendPayload` at
`ForkChoiceStoreRun (Store map)`. The increment is the checked `Slot` add,
and its fault surfaces as the `.arithmetic` fault carrying the repr of the
exact `ArithFault`. -/
@[characterizes EthCLSpecs.Heze.shouldExtendPayload]
theorem shouldExtendPayload_run :
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
            match (rootBlock.slot + 1 : Checked Slot) with
            | .error f => .error (.transition (.arithmetic (reprStr f)))
            | .ok nextSlot =>
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
  simp only [shouldExtendPayload, FcMap.getOrThrow, FcMap.getOrThrowKey]
  cases hblock : FcMap.lookup store.blocks root with
  | none =>
    simp only []
    rw [run_bind, run_throw, except_bind_error]
  | some rootBlock =>
    simp only []
    rw [run_bind, run_pure, except_bind_ok]
    rw [run_bind]
    cases hcur : (getCurrentSlot
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run runnerStore with
    | error err => rw [except_bind_error]
    | ok p =>
      obtain ⟨currentSlot, s1⟩ := p
      rw [except_bind_ok]
      rw [run_bind]
      cases hadd : (rootBlock.slot + 1 : Checked Slot) with
      | error f => rw [run_liftM_error, except_bind_error]; rfl
      | ok nextSlot =>
        rw [run_liftM_ok, except_bind_ok]
        rw [ite_bind]
        split
        case isTrue hsucc =>
          simp only [run_bind, run_pure, except_bind_ok]
          rw [if_pos hsucc]
          cases hverified : isPayloadVerified store root with
          | false =>
            simp only [Bool.not_false, ite_true, run_pure]
          | true =>
            simp only [hverified, Bool.not_true, Bool.false_eq_true, if_false, run_bind]
            cases hfocil : (isPayloadInclusionListSatisfied
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root).run s1 with
            | error err => simp only [except_bind_error]
            | ok q =>
              simp only [except_bind_ok]
              cases q with
              | mk satisfied s2 =>
                cases satisfied with
                | false =>
                  simp only [Bool.not_false, Bool.false_eq_true, if_true, run_pure]
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false, run_bind]
                  cases htime : (payloadTimeliness
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store root true).run s2 with
                  | error err => simp only [except_bind_error]
                  | ok r =>
                    simp only [except_bind_ok]
                    cases r with
                    | mk payloadIsTimely s3 =>
                      cases hda : (payloadDataAvailability
                          (StoreTransition := ForkChoiceStoreRun (Store map))
                          store root true).run s3 with
                      | error err => simp only [except_bind_error]
                      | ok s =>
                        simp only [except_bind_ok]
                        cases s with
                        | mk payloadDataIsAvailable s4 =>
                          simp only []
                          split
                          case isTrue hacc => rfl
                          case isFalse hacc =>
                            simp only [run_bind]
                            cases hpb :
                                FcMap.lookup store.blocks store.proposerBoostRoot with
                            | none => simp only [run_throw, except_bind_error]
                            | some pb =>
                              simp only []
                              rw [run_pure, except_bind_ok]
                              split
                              case isTrue _ => simp only [run_pure]
                              case isFalse _ => rfl
        case isFalse hsucc =>
          simp only [run_bind, run_throw, except_bind_error, if_neg hsucc]
          rfl

/-! ## The successful prefix

The block lookup, `getCurrentSlot`, the checked increment, and the slot
assertion are the prefix every post-prefix corollary shares. One bridge
reduces that prefix once, and each corollary states only its own case.
-/

/-- Under the successful prefix (block lookup, `getCurrentSlot`, the bound
increment, the slot assertion) the run reduces to the post-prefix form: the
`isPayloadVerified` branch, the FOCIL read bound at `s1`, then the inherited
Gloas tail. The gate and tail corollaries below derive from this bridge, as
does later composition work on the write side. -/
private theorem shouldExtendPayload_run_eq_of_slot_prefix :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
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
                          store pb).run s4 := by
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hadd, hslot]

/-! ## Prefix rejects -/

/-- A missing `store.blocks[root]` entry is `missingKey`. -/
theorem shouldExtendPayload_run_error_of_missing_block :
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
theorem shouldExtendPayload_run_error_of_getCurrentSlot :
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

/-- Overflow of the checked increment is the `.arithmetic` fault carrying the
repr of the exact `ArithFault`. -/
theorem shouldExtendPayload_run_error_of_slot_overflow :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (f : ArithFault),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .error f →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.transition (.arithmetic (reprStr f))) := by
  intro store runnerStore s1 root rootBlock currentSlot f hblock hcur hadd
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hadd]

/-- A bound increment that fails `nextSlot == currentSlot` is the spec's
slot assertion. -/
theorem shouldExtendPayload_run_error_of_slot_assert :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot ≠ currentSlot →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "(nextSlot == currentSlot)") := by
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, hadd, hslot]

/-! ## FOCIL gate -/

/-- An unverified payload returns `false` after the block and slot prefix.
The helper is not called. The runner state is `s1`. -/
theorem shouldExtendPayload_run_eq_false_of_unverified :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
      isPayloadVerified store root = false →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, s1) := by
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot hverified
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot nextSlot hblock hcur hadd hslot]
  simp [hverified]

/-- A missing satisfaction record, after verification, is the helper's
membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_focil_record :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_inclusion_list_satisfaction") := by
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot hverified hlookup
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot nextSlot hblock hcur hadd hslot]
  simp [hverified]
  rw [isPayloadInclusionListSatisfied_run_error_of_missing_record store s1 root hlookup]

/-- A verified payload with a recorded `false` inclusion-list satisfaction
verdict is rejected by the FOCIL gate. `hverified` selects that branch.
The converse is not claimed. -/
theorem shouldExtendPayload_run_eq_false_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock) (nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (nextSlot, store) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (shouldExtendPayload (StoreTransition := ForkChoiceStoreRun (Store map)) store root).run
          store
        = .ok (false, store) := by
  intro store root rootBlock nextSlot hblock hcurrentslot hadd hverified hunsatisfied
  rw [shouldExtendPayload_run_eq_of_slot_prefix store store store root rootBlock
    nextSlot nextSlot hblock hcurrentslot hadd rfl]
  simp [hverified]
  rw [isPayloadInclusionListSatisfied_run]
  simp [hunsatisfied]

/-- A recorded `true` with a verified payload continues into the remaining
post-FOCIL checks at `s1`. The helper leaves that runner state unchanged. -/
private theorem shouldExtendPayload_run_eq_of_recorded_satisfied :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot hverified hlookup
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot nextSlot hblock hcur hadd hslot]
  simp [hverified]
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup, hverified]

/-! ## Remaining post-FOCIL checks -/

omit [Config] in
/-- `payloadTimeliness` throws its membership assertion when the vote key is
missing. `run_throw` exposes that store-machine `.assert` under `.run`. -/
private theorem payloadTimeliness_run_error_of_missing_vote :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadTimelinessVote root = none →
      (payloadTimeliness
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run runnerStore
        = .error (.assert "root in store.payload_timeliness_vote") := by
  intro store runnerStore root hlookup
  simp [payloadTimeliness, FcMap.getOrAssert, hlookup, run_throw,
    except_bind_error]

omit [Config] in
/-- `payloadDataAvailability` throws its membership assertion when the vote key
is missing. -/
private theorem payloadDataAvailability_run_error_of_missing_vote :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadDataAvailabilityVote root = none →
      (payloadDataAvailability
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root true).run runnerStore
        = .error (.assert "root in store.payload_data_availability_vote") := by
  intro store runnerStore root hlookup
  simp [payloadDataAvailability, FcMap.getOrAssert, hlookup, run_throw,
    except_bind_error]

/-- A missing timeliness-vote record is the spec's membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_timeliness_vote :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      FcMap.lookup store.payloadTimelinessVote root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_timeliness_vote") := by
  intro store runnerStore s1 root rootBlock currentSlot nextSlot
    hblock hcur hadd hslot hverified hsat htime
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  rw [payloadTimeliness_run_error_of_missing_vote store s1 root htime]

/-- A missing data-availability-vote record is the spec's membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_data_availability_vote :
    ∀ (store runnerStore s1 s3 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot) (payloadIsTimely : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 root rootBlock currentSlot nextSlot payloadIsTimely
    hblock hcur hadd hslot hverified hsat htime hda
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  simp [htime]
  rw [payloadDataAvailability_run_error_of_missing_vote store s3 root hda]

/-- The remaining post-FOCIL checks accept when the payload is timely and
available, or when the proposer-boost root is unset. The runner state is
`s4`. -/
theorem shouldExtendPayload_run_eq_true_of_timely_available_or_zero_boost :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 s4 root rootBlock currentSlot nextSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hadd hslot hverified hsat htime hda hacc
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc]

/-- A missing proposer-boost block is `missingKey` of that boost root. -/
theorem shouldExtendPayload_run_error_of_missing_proposer_block :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot nextSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 s4 root rootBlock currentSlot nextSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hadd hslot hverified hsat htime hda hacc hpb
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb]

/-- When the boost block's parent is not `root`, the remaining post-FOCIL
checks accept. The runner state is `s4`. -/
theorem shouldExtendPayload_run_eq_true_of_proposer_parent_ne :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot nextSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 s4 root rootBlock pb currentSlot nextSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hadd hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- When the boost block's parent is `root`, the decision is
`isParentNodeFull.run s4`. -/
private theorem shouldExtendPayload_run_eq_of_isParentNodeFull :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot nextSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 s4 root rootBlock pb currentSlot nextSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hadd hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot nextSlot
      hblock hcur hadd hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- The remaining post-FOCIL checks reject when `isParentNodeFull` returns
`false`. The runner state is that helper's post-state `s5`. -/
theorem shouldExtendPayload_run_eq_false_of_parent_node_not_full :
    ∀ (store runnerStore s1 s3 s4 s5 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot nextSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      (rootBlock.slot + 1 : Checked Slot) = .ok nextSlot →
      nextSlot = currentSlot →
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
  intro store runnerStore s1 s3 s4 s5 root rootBlock pb currentSlot nextSlot
    payloadIsTimely payloadDataIsAvailable
    hblock hcur hadd hslot hverified hsat htime hda hacc hpb hparent hfull
  have htail :=
    shouldExtendPayload_run_eq_of_isParentNodeFull
      store runnerStore s1 s3 s4 root rootBlock pb currentSlot nextSlot
      payloadIsTimely payloadDataIsAvailable
      hblock hcur hadd hslot hverified hsat htime hda hacc hpb hparent
  rw [htail, hfull]

end EthCLSpecs.Proofs.Heze
