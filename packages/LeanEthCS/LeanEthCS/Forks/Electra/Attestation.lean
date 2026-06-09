import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.Attestation`: Electra attestation containers

EIP-7549 changes Phase 0's `Attestation` and `IndexedAttestation`:

* `Attestation` adds `committee_bits : Bitvector[MAX_COMMITTEES_PER_SLOT]`
  so a single attestation can cover multiple committees per slot.
* Both `aggregation_bits` (on `Attestation`) and `attesting_indices`
  (on `IndexedAttestation`) are widened to
  `MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT`.

`AttesterSlashing` is re-declared because it embeds Electra's
`IndexedAttestation`. `SingleAttestation` is new in Electra
(preset-invariant).

## Caps

* `MAX_COMMITTEES_PER_SLOT`: 4 (minimal) / 64 (mainnet)
* `MAX_VALIDATORS_PER_COMMITTEE = 2048` (preset-invariant)
* Combined cap `MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT`:
  8192 (minimal) / 131072 (mainnet)
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0 (AttestationData)
open LeanEthCS.Macros

ssz_struct_for_presets Attestation in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  aggregationBits : Bitlist (2048 * @@MAX_COMMITTEES_PER_SLOT),
  data            : AttestationData,
  signature       : BLSSignature,
  committeeBits   : Bitvector @@MAX_COMMITTEES_PER_SLOT

ssz_struct_for_presets IndexedAttestation in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  attestingIndices : SSZList ValidatorIndex (2048 * @@MAX_COMMITTEES_PER_SLOT),
  data             : AttestationData,
  signature        : BLSSignature

ssz_struct_for_presets AttesterSlashing in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  attestation1 : @%IndexedAttestation,
  attestation2 : @%IndexedAttestation

/-- `SingleAttestation`: an attestation from one validator, no
aggregation. Preset-invariant. -/
structure SingleAttestation where
  committeeIndex : CommitteeIndex
  attesterIndex  : ValidatorIndex
  data           : AttestationData
  signature      : BLSSignature
  deriving SSZRepr

ssz_struct_for_presets AggregateAndProof in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  aggregatorIndex : ValidatorIndex,
  aggregate       : @%Attestation,
  selectionProof  : BLSSignature

ssz_struct_for_presets SignedAggregateAndProof in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  message   : @%AggregateAndProof,
  signature : BLSSignature

end LeanEthCS.Forks.Electra
