import EthCLSpecs.Heze.State
import EthCLSpecs.Heze.Block
import SizzLean.Repr.Class

/-!
# `EthCLSpecs.Proofs.Heze.Codec`: roundtrip and non-malleability on the Heze wire types

The Heze counterpart of `EthCLSpecs.Proofs.Fulu.Codec`, whose module docstring gives the full
argument. Kernel `decide` discharges the `SSZType.BasicSupported` gate for the Heze
`BeaconState`, `BeaconBlockBody`, `BeaconBlock`, and `SignedBeaconBlock`. `SSZ.roundtrip` and
`SSZ.serialize_injective` then hold on each with the value-level size bound as the only
hypothesis.

Heze declares these four containers with `inherit`, so their fields are the Gloas fields. Each
`inherit` still elaborates a new constant at the Heze `Preset`, so the Gloas theorems say
nothing about these. Each theorem takes `P = mainnet ∨ P = minimal`, for the reason the Fulu
module records.

Heze adds the FOCIL inclusion list (EIP-7805), gossiped as `SignedInclusionList`. Its schema
holds no preset-sized vector, only a list capped by `maxTransactionsPerPayload`. The gate
never reads a list cap, so its theorems hold at every preset. `decide` refuses a goal with a
free variable such as `P`, so the proof calls the soundness lemma
`SSZType.basicSupported_of_checkBasicSupported` and closes the check by `rfl`. The elaborator
reduces the check with the cap left symbolic.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open SizzLean
open SizzLean.Spec (SSZType MAX_LENGTH)
open EthCLSpecs.Heze (Preset mainnet minimal BeaconState BeaconBlockBody BeaconBlock
  SignedBeaconBlock SignedInclusionList)

/-! ## The gate, per container -/

/-- The Heze `BeaconState` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconState_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconState)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Heze `BeaconBlockBody` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem beaconBlockBody_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlockBody)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Heze `BeaconBlock` schema passes the `BasicSupported` gate at both shipped presets. -/
theorem beaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := BeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Heze `SignedBeaconBlock` schema passes the `BasicSupported` gate at both shipped
presets. -/
theorem signedBeaconBlock_basicSupported [P : Preset] (hP : P = mainnet ∨ P = minimal) :
    SSZType.BasicSupported (SSZRepr.shape (T := SignedBeaconBlock)) := by
  rcases hP with rfl | rfl <;> decide

/-- The Heze `SignedInclusionList` schema passes the `BasicSupported` gate at every preset. -/
theorem signedInclusionList_basicSupported [Preset] :
    SSZType.BasicSupported (SSZRepr.shape (T := SignedInclusionList)) :=
  SSZType.basicSupported_of_checkBasicSupported _ rfl

/-! ## Roundtrip -/

/-- A Heze `BeaconState` decodes from its own encoding. -/
theorem beaconState_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (s : BeaconState)
    (h_fits : (SSZ.serialize s).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize s) = .ok s :=
  SSZ.roundtrip s (beaconState_basicSupported hP) h_fits

/-- A Heze `BeaconBlockBody` decodes from its own encoding. -/
theorem beaconBlockBody_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : BeaconBlockBody) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlockBody_basicSupported hP) h_fits

/-- A Heze `BeaconBlock` decodes from its own encoding. -/
theorem beaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal) (b : BeaconBlock)
    (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (beaconBlock_basicSupported hP) h_fits

/-- A Heze `SignedBeaconBlock` decodes from its own encoding. -/
theorem signedBeaconBlock_roundtrip [P : Preset] (hP : P = mainnet ∨ P = minimal)
    (b : SignedBeaconBlock) (h_fits : (SSZ.serialize b).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize b) = .ok b :=
  SSZ.roundtrip b (signedBeaconBlock_basicSupported hP) h_fits

/-- A Heze `SignedInclusionList` decodes from its own encoding, at every preset. -/
theorem signedInclusionList_roundtrip [Preset] (l : SignedInclusionList)
    (h_fits : (SSZ.serialize l).size < MAX_LENGTH) :
    SSZ.deserialize (SSZ.serialize l) = .ok l :=
  SSZ.roundtrip l signedInclusionList_basicSupported h_fits

/-! ## Non-malleability -/

/-- Two Heze `BeaconState`s with the same encoding are equal. -/
theorem beaconState_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconState} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconState_basicSupported hP) h_fits h_eq

/-- Two Heze `BeaconBlockBody`s with the same encoding are equal. -/
theorem beaconBlockBody_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlockBody} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlockBody_basicSupported hP) h_fits h_eq

/-- Two Heze `BeaconBlock`s with the same encoding are equal. -/
theorem beaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : BeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (beaconBlock_basicSupported hP) h_fits h_eq

/-- Two Heze `SignedBeaconBlock`s with the same encoding are equal. -/
theorem signedBeaconBlock_serialize_injective [P : Preset] (hP : P = mainnet ∨ P = minimal)
    {x y : SignedBeaconBlock} (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective (signedBeaconBlock_basicSupported hP) h_fits h_eq

/-- Two Heze `SignedInclusionList`s with the same encoding are equal, at every preset. -/
theorem signedInclusionList_serialize_injective [Preset] {x y : SignedInclusionList}
    (h_fits : (SSZ.serialize x).size < MAX_LENGTH)
    (h_eq : SSZ.serialize x = SSZ.serialize y) : x = y :=
  SSZ.serialize_injective signedInclusionList_basicSupported h_fits h_eq

end EthCLSpecs.Proofs.Heze
