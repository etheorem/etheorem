import EthCLSpecs.Fulu.State
import EthCLSpecs.Fulu.Blocks
import SizzLean.Repr.Class

/-!
# `EthCLSpecs.Proofs.Fulu.Codec`: roundtrip and non-malleability on the Fulu wire types

`SizzLean` proves its two serialization theorems once, over the whole `SSZType` universe.
`SSZ.roundtrip` says that decoding an encoding returns the value. `SSZ.serialize_injective`
says that two values with the same encoding are equal, the non-malleability property. Both
take the gate `SSZType.BasicSupported r.shape` and the size bound
`(SSZ.serialize x).size < MAX_LENGTH`. This module discharges the gate for the Fulu
`BeaconState`, `BeaconBlockBody`, `BeaconBlock`, and `SignedBeaconBlock`. The two theorems then
hold on these types with the size bound as the only hypothesis.

The size bound stays a hypothesis because it is a fact about one value. The SSZ offset table
stores every offset in a `uint32`, so an encoding of `2 ^ 32` bytes or more has no valid
offsets. A `BeaconState` with a large enough validator registry reaches that size in
principle, and the protocol never produces one.

The gate is a fact about the schema, and kernel `decide` proves it through the decision
procedure in `SizzLean.Spec.BasicSupportedDecide`. The kernel unfolds the `SSZRepr` instance the
`forkcontainer` form derives to the container's `SSZType`, then runs the check over it. No
compiler trust enters, so every theorem here carries the three standard axioms alone.

## Why the theorems range over the shipped presets

Every container here takes the fork's `[Preset]`, which sizes its vectors. `BasicSupported`
requires every vector length to be positive, because the decoder rejects a zero-length vector.
The `Preset` class carries positivity proofs for `slotsPerEpoch`, `slotsPerHistoricalRoot`,
and `epochsPerHistoricalVector` only. `BeaconState.slashings` has length
`epochsPerSlashingsVector`, which carries no such proof. For a preset that sets it to zero,
the gate fails and the roundtrip is false. So each theorem takes `P = mainnet ∨ P = minimal`
and case-splits on it, and `decide` checks each shipped preset.

`rcases hP with rfl | rfl` substitutes the concrete preset for the instance variable `P`.
After that step, every vector length in the shape is a closed term, and `decide` can reduce it.

Gloas and Heze re-elaborate these containers at their own `Preset`, so these theorems say
nothing about `EthCLSpecs.Gloas.BeaconState` or `EthCLSpecs.Heze.BeaconState`. Each fork's
`Proofs/<Fork>/Codec.lean` states its own.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open SizzLean
open SizzLean.Spec (SSZType MAX_LENGTH)
open EthCLSpecs.Fulu (Preset mainnet minimal BeaconState BeaconBlockBody BeaconBlock
  SignedBeaconBlock)

/-! ## The gate, per container -/

/-- The Fulu `BeaconState` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconState_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconState)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Fulu `BeaconBlockBody` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem beaconBlockBody_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlockBody)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Fulu `BeaconBlock` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Fulu `SignedBeaconBlock` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem signedBeaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := SignedBeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-! ## Roundtrip

Decoding the encoding of a value returns the value. -/

/-- A Fulu `BeaconState` decodes from its own encoding. -/
theorem beaconState_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (s : BeaconState)
    (h_fits : (SSZ.serialize s).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize s) = .ok s :=
  SSZ.roundtrip s (beaconState_basicSupported hP) h_fits

/-- A Fulu `BeaconBlockBody` decodes from its own encoding. -/
theorem beaconBlockBody_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : BeaconBlockBody) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlockBody_basicSupported hP) h_fits

/-- A Fulu `BeaconBlock` decodes from its own encoding. -/
theorem beaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (b : BeaconBlock)
    (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlock_basicSupported hP) h_fits

/-- A Fulu `SignedBeaconBlock` decodes from its own encoding. -/
theorem signedBeaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : SignedBeaconBlock) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (signedBeaconBlock_basicSupported hP) h_fits

/-! ## Non-malleability

Two values with the same encoding are equal. The bound on `x` is enough, because the equal
encoding gives `y` the same size. -/

/-- Two Fulu `BeaconState`s with the same encoding are equal. -/
theorem beaconState_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconState} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconState_basicSupported hP) h_fits h_eq

/-- Two Fulu `BeaconBlockBody`s with the same encoding are equal. -/
theorem beaconBlockBody_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlockBody} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlockBody_basicSupported hP) h_fits h_eq

/-- Two Fulu `BeaconBlock`s with the same encoding are equal. -/
theorem beaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlock_basicSupported hP) h_fits h_eq

/-- Two Fulu `SignedBeaconBlock`s with the same encoding are equal. -/
theorem signedBeaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : SignedBeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (signedBeaconBlock_basicSupported hP) h_fits h_eq

end EthCLSpecs.Proofs.Fulu
