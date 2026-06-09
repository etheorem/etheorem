import LeanEthCS.Primitives
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Altair.Sync`: Altair sync-committee containers

Altair extends Phase 0 with the *sync-committee* subprotocol used by
light clients. Seven containers carry the sync-committee membership,
aggregated participation, and signing scaffolding.

Five of them embed the preset-sensitive `SYNC_COMMITTEE_SIZE` (32
minimal / 512 mainnet) directly in their SSZ shape, *or* reference a
type that does. Those are declared with `ssz_struct_for_presets`, which
emits one structure per preset (`X.Minimal` / `X.Mainnet`). The two
preset-invariant containers (`SyncCommitteeMessage`,
`SyncAggregatorSelectionData`) stay as ordinary `structure ... deriving
SSZRepr` declarations.

`SYNC_SUBCOMMITTEE_SIZE` is computed in the field type via the macro's
literal-Nat substitution as `SYNC_COMMITTEE_SIZE / 4`. At expansion
the division reduces to `8` (minimal) or `128` (mainnet).
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Altair

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Macros

-- `SyncAggregate`: bitvector of who signed + the aggregated signature.
ssz_struct_for_presets SyncAggregate in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  syncCommitteeBits      : Bitvector @@SYNC_COMMITTEE_SIZE,
  syncCommitteeSignature : BLSSignature

-- `SyncCommittee`: pubkey registry for one sync-committee period.
ssz_struct_for_presets SyncCommittee in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  pubkeys         : Vector BLSPubkey @@SYNC_COMMITTEE_SIZE,
  aggregatePubkey : BLSPubkey

/-- `SyncCommitteeMessage`: a single sync-committee member's
attestation for one slot. Fixed-size, no aggregation. Preset-invariant. -/
structure SyncCommitteeMessage where
  slot            : Slot
  beaconBlockRoot : Root
  validatorIndex  : ValidatorIndex
  signature       : BLSSignature
  deriving SSZRepr

-- `SyncCommitteeContribution`: partial aggregation across one subnet.
-- `aggregationBits` length is `SYNC_SUBCOMMITTEE_SIZE = SYNC_COMMITTEE_SIZE / 4`.
ssz_struct_for_presets SyncCommitteeContribution in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  slot              : Slot,
  beaconBlockRoot   : Root,
  subcommitteeIndex : UInt64,
  aggregationBits   : Bitvector (@@SYNC_COMMITTEE_SIZE / 4),
  signature         : BLSSignature

-- `ContributionAndProof`: contribution + aggregator's selection proof.
-- Preset-variant via its `contribution` field.
ssz_struct_for_presets ContributionAndProof in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  aggregatorIndex : ValidatorIndex,
  contribution    : @%SyncCommitteeContribution,
  selectionProof  : BLSSignature

-- Signed wrapper around `ContributionAndProof`.
ssz_struct_for_presets SignedContributionAndProof in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  message   : @%ContributionAndProof,
  signature : BLSSignature

/-- `SyncAggregatorSelectionData`: message a sync-committee aggregator
signs to prove eligibility for a (slot, subcommittee). Preset-invariant. -/
structure SyncAggregatorSelectionData where
  slot              : Slot
  subcommitteeIndex : UInt64
  deriving SSZRepr

end LeanEthCS.Forks.Altair
