import EthCLSpecs.Gloas.Containers.ExecutionRequests

/-!
# `EthCLSpecs.Gloas.Containers.PayloadAttestation`: the payload-attestation family (EIP-7732)

What the PTC votes on (`PayloadAttestationData`) and the three shapes that carry
it: the aggregated `PayloadAttestation`, its resolved-set
`IndexedPayloadAttestation`, and a single member's `PayloadAttestationMessage`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- The data a payload attestation votes on. -/
forkcontainer PayloadAttestationData where
  beaconBlockRoot   : Root
  slot              : Slot
  payloadPresent    : Bool
  blobDataAvailable : Bool

/-- A PTC payload attestation (aggregated over the PTC). -/
forkcontainer PayloadAttestation where
  aggregationBits : Bitvector Const.ptcSize
  data            : PayloadAttestationData
  signature       : BLSSignature

/-- The resolved attesting set of a payload attestation. -/
forkcontainer IndexedPayloadAttestation where
  attestingIndices : SSZList ValidatorIndex Const.ptcSize
  data             : PayloadAttestationData
  signature        : BLSSignature

/-- A single PTC member's payload-attestation message. -/
forkcontainer PayloadAttestationMessage where
  validatorIndex : ValidatorIndex
  data           : PayloadAttestationData
  signature      : BLSSignature

end EthCLSpecs.Gloas
