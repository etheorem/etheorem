import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.ParticipationFlagsMigrationPins`: the checked-8 flag pins

Behavior pins for `ParticipationFlags` on the checked-8
surface (`CLUint8`): the mask boundary of `has_flag` / `add_flag`, add-flag
idempotence at `255`, and the short-circuit call placement of
`process_attestation`'s flag walk. Each failure pin names the pre-change form
it fails under. The pinned pyspec gives the same class or value at every pin
(`add_flag(255, 0) == 255`; `has_flag(_, 8)` raises
`SSZValueError: 256 is out of range for ParticipationFlags [0, 255]`).

1. Mask boundary (`fulu/minimal.py:4301-4314`, the `add_flag` / `has_flag`
   bodies): the mask `ParticipationFlags(2**flag_index)` range-tests against
   `[0, 255]`, so flag index 7 succeeds and flag index 8 raises the typed range
   fault. The pre-change raw helpers shifted by the index mod 8, so index 8
   read or wrote bit 0 and never raised.
2. Add-flag idempotence at `255`: `add_flag(255, i) == 255` and
   `has_flag(255, i)` for every in-range flag; at the body level, processing
   the same attestation twice changes nothing the second time, because the
   `not has_flag(...)` gate skips the reward accrual. A dropped gate re-accrues
   the proposer reward, which the balance read-back catches; a wrapping
   `flags + mask` combine would leave `3` where the pin reads `255`.
3. Short-circuit placement (`fulu/minimal.py:2081-2084`,
   `gloas/minimal.py:2653-2657`): `flag_index in participation_flag_indices and
   not has_flag(...)` evaluates the `in` first, so the flag read forms only for
   a flag the attestation earns. A Fulu attestation that earns no flag never
   reads the participation list: on a state whose participation lists are empty
   it still processes, where the paired attestation that earns
   `TIMELY_SOURCE_FLAG_INDEX` rejects with the read's `outOfBounds`. A read
   hoisted out of the guard inverts the pair. Gloas reads
   `epoch_participation[index]` for `had_no_participation` once per attesting
   index before the inner loop (`gloas/minimal.py:2650`), so its empty-list
   twin rejects on that read even for a no-flags attestation — the pinned
   order.

The signature gate is forced off (`CryptoBackend.verifyOff`, the `bls_setting:
2` seam): the pins drive the flag walk, which the fabricated zero-signature
attestations never reach otherwise. The pins hash through the FFI `Sha256`
(`fastHasherTag`), so `native_decide` on the harness pins.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ParticipationFlagsMigrationPins

/-! ## The checked-8 value rows behind the fork alias -/

/-- Flag index 7 tests bit 7: the boundary index that still succeeds. -/
example : (CLUint8.hasFlag (0 : EthCLSpecs.Fulu.ParticipationFlags) 7) = .ok false := by
  decide
/-- Flag index 7 sets bit 7: `0 | 128`. -/
example : (CLUint8.addFlag (0 : EthCLSpecs.Fulu.ParticipationFlags) 7) = .ok 128 := by
  decide
/-- Idempotence at `255`: every bit already set, `255 | mask = 255`. A wrapping
combine leaves `3` here (`255 + 4` mod 256). -/
example : (CLUint8.addFlag (255 : EthCLSpecs.Fulu.ParticipationFlags) 2) = .ok 255 := by
  decide
example : (CLUint8.hasFlag (255 : EthCLSpecs.Fulu.ParticipationFlags) 2) = .ok true := by
  decide
/-- Flag index 8: the mask `ParticipationFlags(2**8)` raises the typed range
fault, the pin's own range test. The pre-change raw helper computed
`1 <<< UInt8.ofNat 8`, which wraps to bit 0 and returned a value. -/
example : (CLUint8.addFlag (0 : EthCLSpecs.Fulu.ParticipationFlags) 8) =
    .error (.range "Uint8()" 8 256 0) := by
  decide
example : (CLUint8.hasFlag (0 : EthCLSpecs.Fulu.ParticipationFlags) 8) =
    .error (.range "Uint8()" 8 256 0) := by
  decide

/-! ## Fulu -/

section FuluPins

open EthCLSpecs.Fulu

/-- A capped array (an `SSZList` or a `Bitlist`) built from `a` when `a` fits the cap,
and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- A Fulu state at slot `s` with eight active validators; `part = none` leaves
the participation lists empty (the default), `some a` fills the current-epoch
list. -/
private def attState (P : Preset) (s : Slot) (part : Option (Array ParticipationFlags)) :
    @EthCLSpecs.Fulu.BeaconState P :=
  letI : Preset := P
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Fulu.BeaconState P) with
    slot := s
    validators := capped (Array.replicate 8 v)
    balances := capped (Array.replicate 8 32000000000)
    currentEpochParticipation := capped (part.getD #[]) }

/-- An attestation at `slot` for `targetEpoch` whose target root mismatches the
state's zero block roots, so `is_matching_target` (and with it
`is_matching_head`) is false and only the inclusion delay can earn a flag —
`TIMELY_SOURCE_FLAG_INDEX` iff `delay ≤ isqrt(SLOTS_PER_EPOCH)` (= 2 at
minimal). One set aggregation bit: the slot's single committee holds one validator (eight validators over eight slots at the minimal preset), so exactly one attester. -/
private def noTargetAtt (P : Preset) (slot : Slot) (targetEpoch : Epoch) : @Attestation P :=
  letI : Preset := P
  { (default : Attestation) with
    aggregationBits := capped #[true]
    data := { (default : AttestationData) with
      slot,
      target := { (default : Checkpoint) with
        epoch := targetEpoch, root := Vector.ofFn (fun _ => (1 : UInt8)) } }
    committeeBits := bitSet default 0 true }

/-- Runs Fulu `process_attestation` from an explicit state. -/
private def attRunFrom (P : Preset) (st : @EthCLSpecs.Fulu.BeaconState P)
    (att : @Attestation P) :
    EStateM.Result StateTransitionError (@EthCLSpecs.Fulu.BeaconState P) Unit :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  (processAttestation att : EStateM StateTransitionError
    (@EthCLSpecs.Fulu.BeaconState P) Unit).run st

/-- Runs Fulu `process_attestation` over the fixture state. -/
private def attRun (P : Preset) (s : Slot) (part : Option (Array ParticipationFlags))
    (att : @Attestation P) :
    EStateM.Result StateTransitionError (@EthCLSpecs.Fulu.BeaconState P) Unit :=
  attRunFrom P (attState P s part) att

/-! ### 1. The mask boundary on the accessor -/

/-- `get_unslashed_participating_indices` at flag index 7: every validator's
flag byte is `0x80`, bit 7 is set, all eight participate. -/
private def pinFlag7Participates : Bool :=
  letI : Preset := minimal
  match getUnslashedParticipatingIndices (attState minimal 20 (some (Array.replicate 8 0x80)))
      7 2 with
  | .ok idx => idx.size == 8
  | .error _ => false
example : pinFlag7Participates = true := by native_decide

/-- The same read at flag index 8: the mask `ParticipationFlags(2**8)` raises
the typed range fault (the pin's `256 is out of range for ParticipationFlags
[0, 255]`). The pre-change raw helper shifted by 8 mod 8 = 0, tested bit 0, and
answered `false` without raising. -/
private def pinFlag8Raises : Bool :=
  letI : Preset := minimal
  match getUnslashedParticipatingIndices (attState minimal 20 (some (Array.replicate 8 0x80)))
      8 2 with
  | .error (.arithmetic _) => true
  | _ => false
example : pinFlag8Raises = true := by native_decide

/-! ### 3. The short-circuit placement (Fulu) -/

/-- State slot `20`, attestation slot `17`: delay `3 > isqrt(8) = 2`, so no flag
is earned and the `in` test short-circuits before the flag read — the empty
participation lists are never read and the attestation processes. A read hoisted
out of the guard rejects `outOfBounds` here. -/
private def pinFuluNoFlagsSkipsRead : Bool :=
  match attRun minimal 20 none (noTargetAtt minimal 17 2) with
  | .ok _ _ => true
  | _ => false
example : pinFuluNoFlagsSkipsRead = true := by native_decide

/-- The paired read that does fire: state slot `19`, attestation slot `17`
(delay `2 ≤ isqrt(8)`), so `TIMELY_SOURCE_FLAG_INDEX` is earned and the guarded
read rejects `outOfBounds` on the empty list (the attester's index against the
empty bound). -/
private def pinFuluEarnedFlagReads : Bool :=
  match attRun minimal 19 none (noTargetAtt minimal 17 2) with
  | .error (.outOfBounds _ 0) _ => true
  | _ => false
example : pinFuluEarnedFlagReads = true := by native_decide

/-! ### 2. Add-flag idempotence at the body (Fulu) -/

/-- Processing the same attestation twice: the first run sets the source flag
on the one attester and pays the proposer; the second run's `not has_flag`
gate skips both, so the participation list and the balances are unchanged. A
dropped gate re-accrues the reward, which the balance read-back catches. -/
private def pinFuluSecondRunChangesNothing : Bool :=
  letI : Preset := minimal
  let att := noTargetAtt minimal 17 2
  match attRun minimal 19 (some (Array.replicate 8 0)) att with
  | .error _ _ => false
  | .ok _ st1 =>
    let part1 := (sszGet st1 currentEpochParticipation).val.map CLUint8.toPlainNat
    let bal1 := (sszGet st1 balances).val.map CLUint64.toPlainNat
    part1.contains 1 &&
    match attRunFrom minimal st1 att with
    | .error _ _ => false
    | .ok _ st2 =>
      part1 == (sszGet st2 currentEpochParticipation).val.map CLUint8.toPlainNat
        && bal1 == (sszGet st2 balances).val.map CLUint64.toPlainNat
example : pinFuluSecondRunChangesNothing = true := by native_decide

end FuluPins

/-! ## Gloas -/

section GloasPins

open EthCLSpecs.Gloas

/-- A Gloas state at slot `s` with eight active validators; `part = none`
leaves the participation lists empty, `some a` fills the current-epoch list. -/
private def gAttState (P : Preset) (s : Slot) (part : Option (Array ParticipationFlags)) :
    @EthCLSpecs.Gloas.BeaconState P :=
  letI : Preset := P
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Gloas.BeaconState P) with
    slot := s
    validators := ⟨Array.replicate 8 v⟩
    balances := ⟨Array.replicate 8 32000000000⟩
    currentEpochParticipation := ⟨part.getD #[]⟩ }

/-- The Gloas twin of `noTargetAtt`. Gloas `aggregation_bits` is an uncapped
`ProgressiveBitlist` (EIP-7688). -/
private def gNoTargetAtt (P : Preset) (slot : Slot) (targetEpoch : Epoch) : @Attestation P :=
  letI : Preset := P
  { (default : Attestation) with
    aggregationBits := ⟨#[true]⟩
    data := { (default : AttestationData) with
      slot,
      target := { (default : Checkpoint) with
        epoch := targetEpoch, root := Vector.ofFn (fun _ => (1 : UInt8)) } }
    committeeBits := bitSet default 0 true }

/-- Runs Gloas `process_attestation` with `parent_slot = 0` from an explicit state. -/
private def gAttRunFrom (P : Preset) (st : @EthCLSpecs.Gloas.BeaconState P)
    (att : @Attestation P) :
    EStateM.Result StateTransitionError (@EthCLSpecs.Gloas.BeaconState P) Unit :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  (processAttestation att 0 : EStateM StateTransitionError
    (@EthCLSpecs.Gloas.BeaconState P) Unit).run st

/-- Runs Gloas `process_attestation` over the fixture state. -/
private def gAttRun (P : Preset) (s : Slot) (part : Option (Array ParticipationFlags))
    (att : @Attestation P) :
    EStateM.Result StateTransitionError (@EthCLSpecs.Gloas.BeaconState P) Unit :=
  gAttRunFrom P (gAttState P s part) att

/-! ### 3. The short-circuit placement (Gloas) -/

/-- State slot `20`, attestation slot `17`: no flag earned, but Gloas reads
`epoch_participation[index]` for `had_no_participation` once per attesting
index before the inner loop (`gloas/minimal.py:2650`), so the empty list
rejects on that read — the pinned order, unlike Fulu's guarded read. -/
private def pinGloasFlags0ReadRaises : Bool :=
  match gAttRun minimal 20 none (gNoTargetAtt minimal 17 2) with
  | .error (.outOfBounds _ 0) _ => true
  | _ => false
example : pinGloasFlags0ReadRaises = true := by native_decide

/-- The nearby success: the same no-flags attestation with the participation
lists present processes (nothing is earned, the inner loop skips, the flags0
read of the one attester succeeds). -/
private def pinGloasNoFlagsProcesses : Bool :=
  match gAttRun minimal 20 (some (Array.replicate 8 0)) (gNoTargetAtt minimal 17 2) with
  | .ok _ _ => true
  | _ => false
example : pinGloasNoFlagsProcesses = true := by native_decide

/-- The paired read that does fire: delay `2 ≤ isqrt(8)`, so
`TIMELY_SOURCE_FLAG_INDEX` is earned and the inner guarded read rejects
`outOfBounds` on the empty list (the attester's index against the empty
bound). -/
private def pinGloasEarnedFlagReads : Bool :=
  match gAttRun minimal 19 none (gNoTargetAtt minimal 17 2) with
  | .error (.outOfBounds _ 0) _ => true
  | _ => false
example : pinGloasEarnedFlagReads = true := by native_decide

/-! ### 2. Add-flag idempotence at the body (Gloas) -/

/-- The Gloas twin of the twice-processed attestation: the second run's
`not has_flag` gate leaves both the participation list and the balances
unchanged. -/
private def pinGloasSecondRunChangesNothing : Bool :=
  letI : Preset := minimal
  let att := gNoTargetAtt minimal 17 2
  match gAttRun minimal 19 (some (Array.replicate 8 0)) att with
  | .error _ _ => false
  | .ok _ st1 =>
    let part1 := (sszGet st1 currentEpochParticipation).val.map CLUint8.toPlainNat
    let bal1 := (sszGet st1 balances).val.map CLUint64.toPlainNat
    part1.contains 1 &&
    match gAttRunFrom minimal st1 att with
    | .error _ _ => false
    | .ok _ st2 =>
      part1 == (sszGet st2 currentEpochParticipation).val.map CLUint8.toPlainNat
        && bal1 == (sszGet st2 balances).val.map CLUint64.toPlainNat
example : pinGloasSecondRunChangesNothing = true := by native_decide

end GloasPins

end EthCLSpecs.Tests.ParticipationFlagsMigrationPins
