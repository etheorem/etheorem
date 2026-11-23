import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.CommitteeCoverageOrderPins`: the attestation failure order

`process_attestation` mixes asserts, which the test helper catches, with checked
`uint64` arithmetic, which it does not (`expect_assertion_error` catches
`AssertionError` and `IndexError`, and the range fault is a `ValueError`). So the
order of an assert and an arithmetic step decides the class the runner observes. The
pins cover three sites in Fulu and in Gloas. The first two sit at a state slot near the
maximum.

1. The committee loop (`fulu/minimal.py:2051-2060`, `gloas/minimal.py:2614-2623`). A
   failed check aborts the loop at once. The pins use a preset with
   `SLOTS_PER_EPOCH = 1`, so the epoch equals the slot and `get_seed`'s
   `epoch + EPOCHS_PER_HISTORICAL_VECTOR` overflows near the maximum: every
   `get_beacon_committee` call at that slot raises the range fault. Committee indices
   `2` and `3` both fail the range assert (the count is `2`), so the attestation
   rejects with the caught assert, and the pin confirms that a committee call at
   index `3` would fault. Committee indices `0` and `3` reach the committee call at
   index `0`, which raises the uncaught range fault.
2. `get_attestation_participation_flag_indices` (`fulu/minimal.py:4414-4423`,
   `gloas/minimal.py:5123-5142`). The body reads the target root before
   `assert is_matching_source`. At state slot `2^64 - 1` with the minimal preset, the
   target epoch starts at slot `2^64 - 8`, and `get_block_root_at_slot`'s
   `slot + SLOTS_PER_HISTORICAL_ROOT` overflows. So an attestation with a mismatched
   source raises the uncaught range fault. At state slot `20` the reads succeed and the
   same mismatch rejects with the caught assert.

3. The fold's stop at the first failed check (`fulu/minimal.py:2051-2060`,
   `gloas/minimal.py:2614-2623`). With `SLOTS_PER_EPOCH = 1` and eight validators the
   slot has two committees of four. Committee indices `0` and `1` with four `false`
   aggregation bits fail the attester assert at index `0`, so the attestation rejects
   with the caught assert. A fold that ran on would read `aggregation_bits[4]` for
   index `1` and raise `IndexError`; the nearby pin with four `true` bits passes index
   `0` and shows that read raising.

The pinned pyspec gives the same class at every pin, with `SLOTS_PER_EPOCH` patched to
`1` for sites 1 and 3. Site 2's maximum-slot pins discriminate: a source check placed before
the reads rejects with `.assert` there. Site 3's pins discriminate the fold's stop: a
later committee's aggregation-bit read raises `IndexError` once the fold reaches it.
Site 1's pins record the class at a slot near the maximum. There the committee call's
fault is `get_seed`'s epoch chain, which depends on the slot alone. The call also raises
through `compute_committee`'s checked products, which depend on the committee index, but
those products pass `2^64 - 1` only for a registry far larger than a fixture can hold.
The pins hash through the FFI `Sha256` (`fastHasherTag`), so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.CommitteeCoverageOrderPins

/-- A capped array (an `SSZList` or a `Bitlist`) built from `a` when `a` fits the cap,
and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-! ## Fulu -/

section FuluPins

open EthCLSpecs.Fulu

/-- The minimal preset with `SLOTS_PER_EPOCH = 1`. The epoch equals the slot, so the
seed's checked `epoch + EPOCHS_PER_HISTORICAL_VECTOR` overflows for slots at or above
`2^64 - 64`, since `EPOCHS_PER_HISTORICAL_VECTOR` is `64` at the minimal preset. -/
@[reducible] private def oneSlotEpochs : Preset :=
  { minimal with slotsPerEpoch := 1, slotsPerEpochPos := by decide, slotsPerEpochLt := by decide }

/-- A Fulu state at slot `s` with eight active validators, so each committee at the
minimal preset has a member. The preset is a parameter, so the list caps are not known
here; `capped` checks them, and `pinFuluStatesHoldEight` confirms both presets fit. -/
private def fuluState (P : Preset) (s : Slot) : @BeaconState P :=
  letI : Preset := P
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @BeaconState P) with
    slot := s
    validators := capped (Array.replicate 8 v)
    balances := capped (Array.replicate 8 32000000000) }

/-- Both Fulu fixture presets hold all eight validators. -/
private def pinFuluStatesHoldEight : Bool :=
  (letI : Preset := minimal; (sszGet (fuluState minimal 0) validators).size == 8) &&
    (letI : Preset := oneSlotEpochs; (sszGet (fuluState oneSlotEpochs 0) validators).size == 8)
example : pinFuluStatesHoldEight = true := by native_decide

/-- An attestation at `slot` for `targetEpoch`, with the source checkpoint at
`sourceEpoch`, the given committee bits set, and one set aggregation bit. -/
private def fuluAtt (P : Preset) (slot : Slot) (targetEpoch sourceEpoch : Epoch)
    (committees : List Nat) : @Attestation P :=
  letI : Preset := P
  { (default : Attestation) with
    aggregationBits := capped #[true]
    data := { (default : AttestationData) with
      slot, source := { (default : Checkpoint) with epoch := sourceEpoch },
      target := { (default : Checkpoint) with epoch := targetEpoch } }
    committeeBits := committees.foldl (fun bits ci => bitSet bits ci true) default }

/-- Runs Fulu `process_attestation` over a state and an attestation. -/
private def fuluRun (P : Preset) (s : Slot) (att : @Attestation P) :
    EStateM.Result StateTransitionError (@BeaconState P) Unit :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  (processAttestation att : EStateM StateTransitionError
    (@BeaconState P) Unit).run (fuluState P s)

/-! ### 1. The committee loop -/

/-- Committee indices `2` and `3` at slot `2^64 - 2` (`SLOTS_PER_EPOCH = 1`): the
count is `2`, so the first index fails the range assert and the attestation rejects
with the caught assert. A committee call at index `3` and that slot faults. -/
private def pinFuluOutOfRangeIndexRejectsAssert : Bool :=
  letI : Preset := oneSlotEpochs
  letI : HasherTag := fastHasherTag
  let s : Slot := 18446744073709551614
  let laterCallFaults :=
    match (getBeaconCommittee (fuluState oneSlotEpochs 18446744073709551615) s 3 :
        Except StateTransitionError (Array ValidatorIndex)) with
    | .error (.arithmetic _) => true
    | _ => false
  let rejects :=
    match fuluRun oneSlotEpochs 18446744073709551615 (fuluAtt oneSlotEpochs s s 0 [2, 3]) with
    | .error (.assert _) _ => true
    | _ => false
  laterCallFaults && rejects
example : pinFuluOutOfRangeIndexRejectsAssert = true := by native_decide

/-- Committee indices `0` and `3` at the same slot: the first index is in range, so
the committee call runs and raises the uncaught range fault. -/
private def pinFuluInRangeIndexFaults : Bool :=
  letI : Preset := oneSlotEpochs
  let s : Slot := 18446744073709551614
  match fuluRun oneSlotEpochs 18446744073709551615 (fuluAtt oneSlotEpochs s s 0 [0, 3]) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinFuluInRangeIndexFaults = true := by native_decide

/-! ### 2. The participation-flag reads -/

/-- State slot `2^64 - 1`, attestation slot `2^64 - 8`, source epoch `1` (the state's
justified checkpoint is at epoch `0`). The target-root read overflows before the
source check, so the uncaught range fault is raised first. -/
private def pinFuluMismatchedSourceAtMaxFaults : Bool :=
  letI : Preset := minimal
  match fuluRun minimal 18446744073709551615
      (fuluAtt minimal 18446744073709551608 2305843009213693951 1 [0]) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinFuluMismatchedSourceAtMaxFaults = true := by native_decide

/-- State slot `20`, attestation slot `17`: every read succeeds, and the mismatched
source rejects with the caught assert. -/
private def pinFuluMismatchedSourceRejectsAssert : Bool :=
  letI : Preset := minimal
  match fuluRun minimal 20 (fuluAtt minimal 17 2 1 [0]) with
  | .error (.assert _) _ => true
  | _ => false
example : pinFuluMismatchedSourceRejectsAssert = true := by native_decide

/-! ### 3. The fold's stop at the first failed check -/

/-- `fuluAtt` with the given aggregation bits in place of the single set bit. -/
private def fuluAttBits (P : Preset) (slot : Slot) (targetEpoch : Epoch)
    (committees : List Nat) (bits : Array Bool) : @Attestation P :=
  letI : Preset := P
  { fuluAtt P slot targetEpoch 0 committees with aggregationBits := capped bits }

/-- `SLOTS_PER_EPOCH = 1`, state slot `3`, attestation slot `2`: two committees of four.
Committee indices `0` and `1` with four `false` bits fail the attester assert at index
`0`, so the fold stops there and the attestation rejects with the caught assert. A fold
that ran on would read `aggregation_bits[4]` for index `1` and reject `outOfBounds`. -/
private def pinFuluFirstFailureStopsFold : Bool :=
  match fuluRun oneSlotEpochs 3 (fuluAttBits oneSlotEpochs 2 2 [0, 1] #[false, false, false, false]) with
  | .error (.assert _) _ => true
  | _ => false
example : pinFuluFirstFailureStopsFold = true := by native_decide

/-- The same attestation with four `true` bits: index `0` passes, and index `1` reads
`aggregation_bits[4]`, which raises `IndexError`. -/
private def pinFuluLaterCommitteeReadRaises : Bool :=
  match fuluRun oneSlotEpochs 3 (fuluAttBits oneSlotEpochs 2 2 [0, 1] #[true, true, true, true]) with
  | .error (.outOfBounds 4 4) _ => true
  | _ => false
example : pinFuluLaterCommitteeReadRaises = true := by native_decide

end FuluPins

/-! ## Gloas -/

section GloasPins

open EthCLSpecs.Gloas

/-- The Gloas minimal preset with `SLOTS_PER_EPOCH = 1`. -/
@[reducible] private def oneSlotEpochsG : Preset :=
  { minimal with slotsPerEpoch := 1, slotsPerEpochPos := by decide, slotsPerEpochLt := by decide }

/-- A Gloas state at slot `s` with eight active validators. -/
private def gloasState (P : Preset) (s : Slot) : @State P fastHasherTag :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Gloas.BeaconState P) with
    slot := s
    validators := ⟨Array.replicate 8 v⟩
    balances := ⟨Array.replicate 8 32000000000⟩ }

/-- A Gloas attestation, shaped as `fuluAtt`. Gloas `aggregation_bits` is an uncapped
`ProgressiveBitlist` (EIP-7688). -/
private def gloasAtt (P : Preset) (slot : Slot) (targetEpoch sourceEpoch : Epoch)
    (committees : List Nat) : @Attestation P :=
  letI : Preset := P
  { (default : Attestation) with
    aggregationBits := ⟨#[true]⟩
    data := { (default : AttestationData) with
      slot, source := { (default : Checkpoint) with epoch := sourceEpoch },
      target := { (default : Checkpoint) with epoch := targetEpoch } }
    committeeBits := committees.foldl (fun bits ci => bitSet bits ci true) default }

/-- Runs Gloas `process_attestation` with `parent_slot = 0`. -/
private def gloasRun (P : Preset) (s : Slot) (att : @Attestation P) :
    EStateM.Result StateTransitionError (@State P fastHasherTag) Unit :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  (processAttestation att 0 : EStateM StateTransitionError (@State P fastHasherTag) Unit).run
    (gloasState P s)

/-! ### 1. The committee loop -/

/-- Gloas twin of `pinFuluOutOfRangeIndexRejectsAssert`. -/
private def pinGloasOutOfRangeIndexRejectsAssert : Bool :=
  letI : Preset := oneSlotEpochsG
  letI : HasherTag := fastHasherTag
  let s : Slot := 18446744073709551614
  let laterCallFaults :=
    match (getBeaconCommittee (gloasState oneSlotEpochsG 18446744073709551615) s 3 :
        Except StateTransitionError (Array ValidatorIndex)) with
    | .error (.arithmetic _) => true
    | _ => false
  let rejects :=
    match gloasRun oneSlotEpochsG 18446744073709551615 (gloasAtt oneSlotEpochsG s s 0 [2, 3]) with
    | .error (.assert _) _ => true
    | _ => false
  laterCallFaults && rejects
example : pinGloasOutOfRangeIndexRejectsAssert = true := by native_decide

/-- Gloas twin of `pinFuluInRangeIndexFaults`. -/
private def pinGloasInRangeIndexFaults : Bool :=
  letI : Preset := oneSlotEpochsG
  let s : Slot := 18446744073709551614
  match gloasRun oneSlotEpochsG 18446744073709551615 (gloasAtt oneSlotEpochsG s s 0 [0, 3]) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinGloasInRangeIndexFaults = true := by native_decide

/-! ### 2. The participation-flag reads -/

/-- Gloas twin of `pinFuluMismatchedSourceAtMaxFaults`. The same-slot check and the
head-root read also come before the source check; the target-root read faults first. -/
private def pinGloasMismatchedSourceAtMaxFaults : Bool :=
  letI : Preset := minimal
  match gloasRun minimal 18446744073709551615
      (gloasAtt minimal 18446744073709551608 2305843009213693951 1 [0]) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinGloasMismatchedSourceAtMaxFaults = true := by native_decide

/-- Gloas twin of `pinFuluMismatchedSourceRejectsAssert`. -/
private def pinGloasMismatchedSourceRejectsAssert : Bool :=
  letI : Preset := minimal
  match gloasRun minimal 20 (gloasAtt minimal 17 2 1 [0]) with
  | .error (.assert _) _ => true
  | _ => false
example : pinGloasMismatchedSourceRejectsAssert = true := by native_decide

/-! ### 3. The fold's stop at the first failed check -/

/-- `gloasAtt` with the given aggregation bits in place of the single set bit. -/
private def gloasAttBits (P : Preset) (slot : Slot) (targetEpoch : Epoch)
    (committees : List Nat) (bits : Array Bool) : @Attestation P :=
  letI : Preset := P
  { gloasAtt P slot targetEpoch 0 committees with aggregationBits := ⟨bits⟩ }

/-- Gloas twin of `pinFuluFirstFailureStopsFold`. -/
private def pinGloasFirstFailureStopsFold : Bool :=
  match gloasRun oneSlotEpochsG 3 (gloasAttBits oneSlotEpochsG 2 2 [0, 1] #[false, false, false, false]) with
  | .error (.assert _) _ => true
  | _ => false
example : pinGloasFirstFailureStopsFold = true := by native_decide

/-- Gloas twin of `pinFuluLaterCommitteeReadRaises`. -/
private def pinGloasLaterCommitteeReadRaises : Bool :=
  match gloasRun oneSlotEpochsG 3 (gloasAttBits oneSlotEpochsG 2 2 [0, 1] #[true, true, true, true]) with
  | .error (.outOfBounds 4 4) _ => true
  | _ => false
example : pinGloasLaterCommitteeReadRaises = true := by native_decide

end GloasPins

end EthCLSpecs.Tests.CommitteeCoverageOrderPins
