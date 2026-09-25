import EthCLSpecs.Gloas.State
import EthCLSpecs.Gloas.Block
import SizzLean.Repr.Class

/-!
# `EthCLSpecs.Proofs.Gloas.Codec`: roundtrip and non-malleability on the Gloas wire types

The Gloas counterpart of `EthCLSpecs.Proofs.Fulu.Codec`, whose module docstring gives the full
argument. Kernel `decide` discharges the `SSZType.BasicSupported` gate for the Gloas
`BeaconState`, `BeaconBlockBody`, `BeaconBlock`, and `SignedBeaconBlock`. `SSZ.roundtrip` and
`SSZ.serialize_injective` then hold on each with the value-level size bound as the only
hypothesis.

Gloas re-elaborates every container at its own `Preset`, so these are separate constants from
the Fulu ones, and the Fulu theorems say nothing about them. The Gloas schemas differ as well:
the state carries the builder registry and the payment window, and the block body carries the
signed execution-payload bid and the payload attestations.

Each theorem takes `P = mainnet ∨ P = minimal`, for the reason the Fulu module records. The
`Preset` class carries no positivity proof for `epochsPerSlashingsVector` or `ptcSize`, and a
zero value for either breaks the gate. The three standard axioms are the whole trust base.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open SizzLean
open SizzLean.Spec (SSZType MAX_LENGTH)
open EthCLSpecs.Gloas (Preset mainnet minimal BeaconState BeaconBlockBody BeaconBlock
  SignedBeaconBlock)

/-! ## The gate, per container -/

/-- The Gloas `BeaconState` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconState_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconState)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Gloas `BeaconBlockBody` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem beaconBlockBody_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlockBody)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Gloas `BeaconBlock` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Gloas `SignedBeaconBlock` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem signedBeaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := SignedBeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-! ## Roundtrip -/

/-- A Gloas `BeaconState` decodes from its own encoding. -/
theorem beaconState_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (s : BeaconState)
    (h_fits : (SSZ.serialize s).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize s) = .ok s :=
  SSZ.roundtrip s (beaconState_basicSupported hP) h_fits

/-- A Gloas `BeaconBlockBody` decodes from its own encoding. -/
theorem beaconBlockBody_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : BeaconBlockBody) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlockBody_basicSupported hP) h_fits

/-- A Gloas `BeaconBlock` decodes from its own encoding. -/
theorem beaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (b : BeaconBlock)
    (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlock_basicSupported hP) h_fits

/-- A Gloas `SignedBeaconBlock` decodes from its own encoding. -/
theorem signedBeaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : SignedBeaconBlock) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (signedBeaconBlock_basicSupported hP) h_fits

/-! ## Non-malleability -/

/-- Two Gloas `BeaconState`s with the same encoding are equal. -/
theorem beaconState_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconState} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconState_basicSupported hP) h_fits h_eq

/-- Two Gloas `BeaconBlockBody`s with the same encoding are equal. -/
theorem beaconBlockBody_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlockBody} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlockBody_basicSupported hP) h_fits h_eq

/-- Two Gloas `BeaconBlock`s with the same encoding are equal. -/
theorem beaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlock_basicSupported hP) h_fits h_eq

/-- Two Gloas `SignedBeaconBlock`s with the same encoding are equal. -/
theorem signedBeaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : SignedBeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (signedBeaconBlock_basicSupported hP) h_fits h_eq

end EthCLSpecs.Proofs.Gloas
