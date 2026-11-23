import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.CLUint

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's payload-extension decision

Heze's `shouldExtendPayload` inserts a FOCIL gate after payload verification
and before the timeliness, data-availability, and proposer-boost checks.

The complete `.run` equation evaluates in this order: block lookup,
the checked `slot + 1`, `getCurrentSlot.run`, the slot assertion,
`isPayloadVerified`, `isPayloadInclusionListSatisfied.run`, then the
remaining post-FOCIL checks (`payloadTimeliness`, `payloadDataAvailability`,
proposer-boost block lookup, and `isParentNodeFull`).

The checked `blocks[root].slot + 1` appears as a decision on the plain sum
`rootBlock.slot.toPlainNat + 1 < UInt64.size`: the value `CLUint64.ofNatLT` in range, and
the `.arithmetic "+"` reject past `2^64 - 1` (`EthCLLib.Proofs.hadd_un_eq`). The corollaries
take the plain equation `rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat`, which
holds exactly when the add succeeds with `currentSlot`. A `match` on the checked add itself
would make the kernel reduce `mixBin`'s `Int` range test on an open slot, which unfolds
`Nat.sub` against `2^64` and exceeds the kernel's recursion depth.

The explicit argument `store` is the map that is read. `runnerStore` is
the runner state. Successful binds thread intermediate states `s1`, `s2`,
`s3`, and `s4`. A reject returns the error alone and has no post-state.

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

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure run_throw except_bind_ok
  except_bind_error hadd_un_eq)
open EthCLLib.Spec (MapKind FcMap CLUint64 StoreTransitionError SpecReject)
open EthCLSpecs.Heze (Preset Config Store shouldExtendPayload isPayloadInclusionListSatisfied
  isPayloadVerified getCurrentSlot payloadTimeliness payloadDataAvailability isParentNodeFull
  fcZeroRoot Root Slot BeaconBlock)

variable {map : MapKind} [Preset] [Config] [FcMap map]

/-! ## Complete `.run` equation -/

/-- Complete compositional `.run` equation of `shouldExtendPayload` at
`ForkChoiceStoreRun (Store map)`. -/
@[characterizes EthCLSpecs.Heze.shouldExtendPayload]
theorem shouldExtendPayload_run :
    ∀ (store runnerStore : Store map) (root : Root),
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
        match FcMap.lookup store.blocks root with
        | none => .error (.missingKey root)
        | some rootBlock =>
          if hnext : rootBlock.slot.toPlainNat + 1 < UInt64.size then
            match (getCurrentSlot
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store).run runnerStore with
            | .error err => .error err
            | .ok (currentSlot, s1) =>
              if CLUint64.ofNatLT _ hnext == currentSlot then
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
                .error (.assert "(nextSlot == currentSlot)")
          else
            .error (.transition (.arithmetic "+")) := by
  intro store runnerStore root
  simp only [shouldExtendPayload, FcMap.getOrThrow, FcMap.getOrThrowKey, run_bind]
  cases hblock : FcMap.lookup store.blocks root with
  | none => rfl
  | some rootBlock =>
    rw [run_pure, except_bind_ok]
    -- Reduce the statement's outer match, then state the checked add as its plain range
    -- decision on both sides (`hadd_un_eq`).
    dsimp only
    rw [hadd_un_eq]
    by_cases hnext : rootBlock.slot.toPlainNat + 1 < UInt64.size
    · rw [dite_eq_left hnext, dite_eq_left hnext, ForkChoiceStoreRun.liftChecked_ok_run,
        except_bind_ok]
      cases hcur : (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore with
      | error err => rfl
      | ok p =>
        obtain ⟨currentSlot, s1⟩ := p
        rw [except_bind_ok]
        by_cases hslot : (CLUint64.ofNatLT _ hnext == currentSlot) = true
        · simp [hslot]
          cases hverified : isPayloadVerified store root
          · simp
            rfl
          · simp
            cases hfocil : (isPayloadInclusionListSatisfied
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root).run s1 with
            | error err =>
              simp [except_bind_error]
            | ok q =>
              obtain ⟨satisfied, s2⟩ := q
              simp [except_bind_ok]
              cases satisfied
              · rfl
              · simp
                cases htime : (payloadTimeliness
                    (StoreTransition := ForkChoiceStoreRun (Store map))
                    store root true).run s2 with
                | error err =>
                  simp [except_bind_error]
                | ok r =>
                  obtain ⟨payloadIsTimely, s3⟩ := r
                  simp [except_bind_ok]
                  cases hda : (payloadDataAvailability
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store root true).run s3 with
                  | error err =>
                    simp [except_bind_error]
                  | ok s =>
                    obtain ⟨payloadDataIsAvailable, s4⟩ := s
                    simp [except_bind_ok]
                    by_cases hacc :
                        payloadIsTimely = true ∧ payloadDataIsAvailable = true
                          ∨ store.proposerBoostRoot = fcZeroRoot
                    · simp [hacc]
                      rfl
                    · simp [hacc]
                      cases hpb : FcMap.lookup store.blocks store.proposerBoostRoot with
                      | none =>
                        simp [run_throw, except_bind_error]
                      | some pb =>
                        simp
                        by_cases hparent : pb.parentRoot = root
                        · simp [hparent]
                        · simp [hparent]
                          rfl
        · simp [hslot, run_throw, except_bind_error, SpecReject.assert]
    · rw [dite_eq_right hnext, dite_eq_right hnext, ForkChoiceStoreRun.liftChecked_error_run,
        except_bind_error]
      rfl

/-! ## The successful prefix

The block lookup, the increment, `getCurrentSlot`, and the slot assertion
are the prefix every post-prefix corollary shares. One bridge reduces that
prefix once, and each corollary states only its own case.
-/

omit [Preset] [Config] in
/-- A block one slot before `currentSlot` passes the checked add's range test: the sum
equals a value already below `2^64`. -/
private theorem next_slot_lt {a c : Slot} (h : a.toPlainNat + 1 = c.toPlainNat) :
    a.toPlainNat + 1 < UInt64.size := by
  rw [h]
  exact UInt64.toNat_lt_size c.val

omit [Preset] [Config] in
/-- The checked add's value is then `currentSlot`, so the slot assertion holds. -/
private theorem next_slot_beq {a c : Slot} (h : a.toPlainNat + 1 = c.toPlainNat) :
    (CLUint64.ofNatLT _ (next_slot_lt h) == c) = true := by
  rw [beq_iff_eq]
  apply CLUint64.val_inj
  apply UInt64.toNat_inj.1
  show (CLUint64.ofNatLT _ (next_slot_lt h)).toPlainNat = c.toPlainNat
  rw [CLUint64.ofNatLT_toPlainNat]
  exact h

/-- Under the successful prefix (block lookup, the non-overflowing increment,
`getCurrentSlot`, the slot assertion) the run reduces to the
post-prefix form: the `isPayloadVerified` branch, the FOCIL read bound at
`s1`, then the inherited Gloas tail. The gate and tail corollaries below
derive from this bridge, as does later composition work on the write
side. -/
private theorem shouldExtendPayload_run_eq_of_slot_prefix :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hslot
  rw [shouldExtendPayload_run]
  simp [hblock, hcur, next_slot_lt hslot, next_slot_beq hslot]

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

/-- After a successful increment, a `getCurrentSlot` reject is propagated unchanged. -/
theorem shouldExtendPayload_run_error_of_getCurrentSlot :
    ∀ (store runnerStore : Store map) (root : Root) (rootBlock : BeaconBlock)
      (err : StoreTransitionError),
      FcMap.lookup store.blocks root = some rootBlock →
      rootBlock.slot.toPlainNat + 1 < UInt64.size →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .error err →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error err := by
  intro store runnerStore root rootBlock err hblock hnooverflow hcur
  rw [shouldExtendPayload_run]
  simp [hblock, hnooverflow, hcur]

/-- Overflow of the checked `blocks[root].slot + 1` is the range fault, which lands as the
`.arithmetic` reject carrying the operator. The add binds before the clock read, as Python
evaluates the left operand of `==` first, so the clock's own rejects cannot preempt it. -/
theorem shouldExtendPayload_run_error_of_slot_overflow :
    ∀ (store runnerStore : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      UInt64.size ≤ rootBlock.slot.toPlainNat + 1 →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.transition (.arithmetic "+")) := by
  intro store runnerStore root rootBlock hblock hover
  rw [shouldExtendPayload_run]
  simp [hblock, Nat.not_lt.mpr hover]

/-- A successful increment that fails `nextSlot == currentSlot` is the spec's
slot assertion. -/
theorem shouldExtendPayload_run_error_of_slot_assert :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 < UInt64.size →
      rootBlock.slot.toPlainNat + 1 ≠ currentSlot.toPlainNat →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "(nextSlot == currentSlot)") := by
  intro store runnerStore s1 root rootBlock currentSlot hblock hcur hnooverflow hslot
  rw [shouldExtendPayload_run]
  have hne : (CLUint64.ofNatLT _ hnooverflow == currentSlot) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    apply hslot
    rw [← h, CLUint64.ofNatLT_toPlainNat]
  simp [hblock, hcur, hnooverflow, hne]

/-! ## FOCIL gate -/

/-- An unverified payload returns `false` after the block and slot prefix.
The helper is not called. The runner state is `s1`. -/
theorem shouldExtendPayload_run_eq_false_of_unverified :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
      isPayloadVerified store root = false →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, s1) := by
  intro store runnerStore s1 root rootBlock currentSlot hblock hcur hslot hverified
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot hblock hcur hslot]
  simp [hverified]

/-- A missing satisfaction record, after verification, is the helper's
membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_focil_record :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_inclusion_list_satisfaction") := by
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hslot hverified hlookup
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot hblock hcur hslot]
  simp [hverified]
  rw [isPayloadInclusionListSatisfied_run_error_of_missing_record store s1 root hlookup]

/-- The FOCIL gate rejects a verified payload with a recorded `false`
inclusion-list satisfaction value. `hverified` selects that branch.
The converse is not claimed. -/
theorem shouldExtendPayload_run_eq_false_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock) (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (currentSlot, store) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (shouldExtendPayload (StoreTransition := ForkChoiceStoreRun (Store map)) store root).run
          store
        = .ok (false, store) := by
  intro store root rootBlock currentSlot hblock hcurrentslot hslot hverified hunsatisfied
  rw [shouldExtendPayload_run_eq_of_slot_prefix store store store root rootBlock
    currentSlot hblock hcurrentslot hslot]
  simp [hverified]
  rw [isPayloadInclusionListSatisfied_run]
  simp [hunsatisfied]

/-- A recorded `true` with a verified payload continues into the remaining
post-FOCIL checks at `s1`. The helper leaves that runner state unchanged. -/
private theorem shouldExtendPayload_run_eq_of_recorded_satisfied :
    ∀ (store runnerStore s1 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hlookup
  rw [shouldExtendPayload_run_eq_of_slot_prefix store runnerStore s1 root rootBlock
    currentSlot hblock hcur hslot]
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
      (currentSlot : Slot),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      FcMap.lookup store.payloadTimelinessVote root = none →
      (shouldExtendPayload
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_timeliness_vote") := by
  intro store runnerStore s1 root rootBlock currentSlot
    hblock hcur hslot hverified hsat htime
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  rw [payloadTimeliness_run_error_of_missing_vote store s1 root htime]

/-- A missing data-availability-vote record is the spec's membership assert. -/
theorem shouldExtendPayload_run_error_of_missing_data_availability_vote :
    ∀ (store runnerStore s1 s3 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  simp [htime]
  rw [payloadDataAvailability_run_error_of_missing_vote store s3 root hda]

/-- The remaining post-FOCIL checks accept when the payload is timely and
available, or when the proposer-boost root is unset. The runner state is
`s4`. -/
theorem shouldExtendPayload_run_eq_true_of_timely_available_or_zero_boost :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda hacc
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc]

/-- A missing proposer-boost block is `missingKey` of that boost root. -/
theorem shouldExtendPayload_run_error_of_missing_proposer_block :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root) (rootBlock : BeaconBlock)
      (currentSlot : Slot) (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda hacc hpb
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb]

/-- When the boost block's parent is not `root`, the remaining post-FOCIL
checks accept. The runner state is `s4`. -/
theorem shouldExtendPayload_run_eq_true_of_proposer_parent_ne :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- When the boost block's parent is `root`, the decision is
`isParentNodeFull.run s4`. -/
private theorem shouldExtendPayload_run_eq_of_isParentNodeFull :
    ∀ (store runnerStore s1 s3 s4 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda hacc hpb hparent
  have htail :=
    shouldExtendPayload_run_eq_of_recorded_satisfied
      store runnerStore s1 root rootBlock currentSlot
      hblock hcur hslot hverified hsat
  rw [htail]
  simp [htime, hda, hacc, hpb, hparent]

/-- The remaining post-FOCIL checks reject when `isParentNodeFull` returns
`false`. The runner state is that helper's post-state `s5`. -/
theorem shouldExtendPayload_run_eq_false_of_parent_node_not_full :
    ∀ (store runnerStore s1 s3 s4 s5 : Store map) (root : Root)
      (rootBlock pb : BeaconBlock) (currentSlot : Slot)
      (payloadIsTimely payloadDataIsAvailable : Bool),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store).run runnerStore
        = .ok (currentSlot, s1) →
      rootBlock.slot.toPlainNat + 1 = currentSlot.toPlainNat →
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
    hblock hcur hslot hverified hsat htime hda hacc hpb hparent hfull
  have htail :=
    shouldExtendPayload_run_eq_of_isParentNodeFull
      store runnerStore s1 s3 s4 root rootBlock pb currentSlot
      payloadIsTimely payloadDataIsAvailable
      hblock hcur hslot hverified hsat htime hda hacc hpb hparent
  rw [htail, hfull]

end EthCLSpecs.Proofs.Heze
