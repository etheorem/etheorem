import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Phase0.Attestations`: attestation + slashing types

The Phase 0 types that use `Bitlist`, `SSZList`, and nested
variable-size containers. These exercise the variable-field offset
table and Merkleization paths that bitlist and list-of-composites
require.

## Spec constants (consensus-spec-tests phase0, mainnet *and*
minimal agree on these)

* `MAX_VALIDATORS_PER_COMMITTEE = 2048`: cap for both the
  attestation bitlist and the `IndexedAttestation` index list.
* `DEPOSIT_CONTRACT_TREE_DEPTH = 32` (so proof depth = 33).

Other consensus constants used downstream (`MAX_PROPOSER_SLASHINGS`,
`MAX_ATTESTATIONS`, etc.) live in `Eth/Phase0/Block.lean` where
`BeaconBlockBody` consumes them.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Phase0

open SizzLean

open SizzLean.Repr

open LeanEthCS

/-- `IndexedAttestation`: attesting validator indices listed
explicitly (used in slashing). The index list is a variable-size
collection of fixed-size `uint64` elements. -/
structure IndexedAttestation where
  attestingIndices : SSZList ValidatorIndex 2048
  data             : AttestationData
  signature        : BLSSignature
  deriving SSZRepr

/-- `PendingAttestation`: attestation in flight inside the
beacon state. Variable-size container with a `Bitlist` field
(aggregation bits) plus three fixed-size fields. -/
structure PendingAttestation where
  aggregationBits : Bitlist 2048
  data            : AttestationData
  inclusionDelay  : Slot
  proposerIndex   : ValidatorIndex
  deriving SSZRepr

/-- `Attestation`: aggregated attestation broadcast on the wire. -/
structure Attestation where
  aggregationBits : Bitlist 2048
  data            : AttestationData
  signature       : BLSSignature
  deriving SSZRepr

/-- `AttesterSlashing`: two conflicting indexed attestations from
the same validator set. Variable-size container of variable-size
elements. -/
structure AttesterSlashing where
  attestation1 : IndexedAttestation
  attestation2 : IndexedAttestation
  deriving SSZRepr

/-- `Deposit`: Merkle inclusion proof + the deposit data being
attested. The proof is a fixed-length vector of 33
`Bytes32`s (the contract-tree depth plus one for the deposit-count
sibling). -/
structure Deposit where
  proof : Vector Bytes32 33
  data  : DepositData
  deriving SSZRepr

/-- `AggregateAndProof`: aggregator's contribution plus selection
proof. -/
structure AggregateAndProof where
  aggregatorIndex : ValidatorIndex
  aggregate       : Attestation
  selectionProof  : BLSSignature
  deriving SSZRepr

/-- Signed wrapper around `AggregateAndProof`. -/
structure SignedAggregateAndProof where
  message   : AggregateAndProof
  signature : BLSSignature
  deriving SSZRepr

end LeanEthCS.Forks.Phase0
