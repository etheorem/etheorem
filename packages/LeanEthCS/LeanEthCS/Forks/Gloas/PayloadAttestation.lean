import LeanEthCS.Primitives
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.PayloadAttestation`: ePBS payload attestations

EIP-7732 introduces a Payload-Timeliness Committee (PTC) that votes
on whether the proposed `ExecutionPayload` was made available on
time. The committee size `PTC_SIZE` is preset-sensitive
(16 minimal, 512 mainnet); the per-block cap
`MAX_PAYLOAD_ATTESTATIONS = 4` is preset-invariant.

The four containers:

* `PayloadAttestationData`: what's being voted on (block root,
  slot, presence flags). Preset-invariant.
* `PayloadAttestation`: aggregated PTC vote (uses
  `Bitvector[PTC_SIZE]`, preset-sensitive).
* `PayloadAttestationMessage`: single-validator unaggregated vote.
  Preset-invariant.
* `IndexedPayloadAttestation`: expanded form used by slashing
  predicates; the `attesting_indices` list cap is `PTC_SIZE`
  (preset-sensitive).
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Macros

/-- What the PTC votes on: the block root, slot, and presence
flags for the execution payload and its blob sidecar. -/
structure PayloadAttestationData where
  beaconBlockRoot    : Root
  slot               : Slot
  payloadPresent     : Bool
  blobDataAvailable  : Bool
  deriving SSZRepr

ssz_struct_for_presets PayloadAttestation in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  aggregationBits : Bitvector @@PTC_SIZE,
  data            : PayloadAttestationData,
  signature       : BLSSignature

/-- A single unaggregated PTC vote, preset-invariant. -/
structure PayloadAttestationMessage where
  validatorIndex : ValidatorIndex
  data           : PayloadAttestationData
  signature      : BLSSignature
  deriving SSZRepr

ssz_struct_for_presets IndexedPayloadAttestation in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  attestingIndices : SSZList ValidatorIndex @@PTC_SIZE,
  data             : PayloadAttestationData,
  signature        : BLSSignature

end LeanEthCS.Forks.Gloas
