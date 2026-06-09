import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Phase0.BeaconBlockHeader`

Smallest non-trivial Phase 0 composite, five fixed-size primitive
fields. A useful first reading of the `deriving SSZRepr` handler
against a real consensus-spec type.

Per `consensus-specs/specs/phase0/beacon-chain.md`:

```
class BeaconBlockHeader(Container):
    slot: Slot
    proposer_index: ValidatorIndex
    parent_root: Root
    state_root: Root
    body_root: Root
```

The SSZ shape is `.container [.uintN 64, .uintN 64,
.vector (.uintN 8) 32, .vector (.uintN 8) 32, .vector (.uintN 8) 32]`.
All fixed-size, total wire length is `8 + 8 + 32 + 32 + 32 = 112` bytes.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Phase0

open SizzLean

open LeanEthCS

/-- Phase 0 beacon-block header, five fixed-size fields. -/
structure BeaconBlockHeader where
  slot           : Slot
  proposerIndex  : ValidatorIndex
  parentRoot     : Root
  stateRoot      : Root
  bodyRoot       : Root
  deriving SSZRepr

/-- Smoke-test: a default-valued header round-trips via the
`SSZRepr`-driven encode/decode pair. Closed by `native_decide`, the
verified `SSZ.roundtrip` corollary is gated on `BasicSupported` and
this concrete check sits outside that surface. -/
private def roundTripBBH (h : BeaconBlockHeader) : Bool :=
  match SSZ.deserialize (T := BeaconBlockHeader) (SSZ.serialize h) with
  | .ok h' => decide (h'.slot = h.slot) &&
              decide (h'.proposerIndex = h.proposerIndex) &&
              decide (h'.parentRoot = h.parentRoot) &&
              decide (h'.stateRoot = h.stateRoot) &&
              decide (h'.bodyRoot = h.bodyRoot)
  | .error _ => false

/-- Zero-valued header for the smoke test. -/
private def zeroBBH : BeaconBlockHeader :=
  { slot := 0, proposerIndex := 0,
    parentRoot     := Vector.replicate 32 0,
    stateRoot      := Vector.replicate 32 0,
    bodyRoot       := Vector.replicate 32 0 }

example : roundTripBBH zeroBBH = true := by native_decide

end LeanEthCS.Forks.Phase0
