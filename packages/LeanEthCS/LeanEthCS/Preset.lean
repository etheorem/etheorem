/-!
# `LeanEthCS.Preset`: minimal / mainnet preset constants

Ethereum consensus has two "presets" that scale the protocol for
mainnet (`mainnet`) and tests (`minimal`). The presets only change
*numeric constants*, never the *shape* of the SSZ types, so a single
container declaration can target both presets if we can substitute the
right `Nat` literal at each instantiation site.

The macro in `LeanEthCS.PresetStruct` does that substitution by
looking up `Preset.<name>.<CONSTANT>` and reducing it to a literal at
expansion time. This module defines:

* `Preset`: a record carrying every preset-sensitive numeric used
  inside an SSZ field type across phase0 → fulu.
* `Preset.minimal`, `Preset.mainnet`: the two values.

Values transcribed from
[ethereum/consensus-specs](https://github.com/ethereum/consensus-specs)
`presets/{minimal,mainnet}/<fork>.yaml` at the tag pinned in
`scripts/run_conformance.py`'s `DEFAULT_TAG`.

## Scope

This record holds **only preset-sensitive caps that appear inside an
SSZ field type**. Spec constants that are identical on both presets
(e.g. `HISTORICAL_ROOTS_LIMIT = 2^24`, `VALIDATOR_REGISTRY_LIMIT =
2^40`, `MAX_PROPOSER_SLASHINGS = 16`, the `BLSSignature` width, etc.)
stay as literal `Nat`s in the container declarations, no preset
indirection needed for them. Constants that affect *behavior* but not
SSZ shape (e.g. `MAX_EFFECTIVE_BALANCE`, `SHUFFLE_ROUND_COUNT`) are
out of scope here entirely; they're spec-text values, not types.

Add a new field if-and-only-if a container declaration needs to embed
a preset-sensitive `Nat` in a `Vector` / `SSZList` / `Bitvector` /
`Bitlist` argument and the value differs between minimal and mainnet.
-/

set_option autoImplicit false

namespace LeanEthCS



/-- Preset-sensitive numeric constants used inside SSZ field types. -/
structure Preset where
  -- Phase 0
  SLOTS_PER_EPOCH                   : Nat
  MAX_COMMITTEES_PER_SLOT           : Nat
  EPOCHS_PER_ETH1_VOTING_PERIOD     : Nat
  SLOTS_PER_HISTORICAL_ROOT         : Nat
  EPOCHS_PER_HISTORICAL_VECTOR      : Nat
  EPOCHS_PER_SLASHINGS_VECTOR       : Nat
  -- Altair
  SYNC_COMMITTEE_SIZE               : Nat
  -- Capella
  MAX_WITHDRAWALS_PER_PAYLOAD       : Nat
  -- Deneb. Both presets agree on these today, but they're kept as
  -- preset-record fields rather than literals so the macro surface
  -- stays uniform across forks and a future preset divergence
  -- doesn't need a structural change. `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH`
  -- is derived from `BeaconBlockBody`'s gindex via
  -- `ceillog2(MAX_BLOB_COMMITMENTS_PER_BLOCK) + 5`.
  MAX_BLOB_COMMITMENTS_PER_BLOCK       : Nat
  KZG_COMMITMENT_INCLUSION_PROOF_DEPTH : Nat
  -- Electra
  PENDING_PARTIAL_WITHDRAWALS_LIMIT : Nat
  PENDING_CONSOLIDATIONS_LIMIT      : Nat
  -- Gloas (EIP-7732 ePBS), from `presets/{minimal,mainnet}/gloas.yaml`.
  -- `PTC_SIZE` (16 / 512) and `MAX_BUILDERS_PER_WITHDRAWALS_SWEEP`
  -- (16 / 16384) are preset-sensitive; `MAX_PAYLOAD_ATTESTATIONS`,
  -- `BUILDER_REGISTRY_LIMIT`, and `BUILDER_PENDING_WITHDRAWALS_LIMIT`
  -- agree across presets but stay as preset-record fields for macro
  -- uniformity. `PTC_SIZE` is the one that lands inside an SSZ field
  -- type (`ptc_window`'s inner `Vector`, `PayloadAttestation`'s
  -- `Bitvector`), so it must track the spec exactly.
  PTC_SIZE                            : Nat
  MAX_PAYLOAD_ATTESTATIONS            : Nat
  BUILDER_REGISTRY_LIMIT              : Nat
  BUILDER_PENDING_WITHDRAWALS_LIMIT   : Nat
  MAX_BUILDERS_PER_WITHDRAWALS_SWEEP  : Nat
  deriving Repr, DecidableEq

namespace Preset

/-- Minimal preset, used by the upstream `tests/minimal/...` test
vectors. Scaled-down constants so the protocol fits in a test runner. -/
def minimal : Preset :=
  { SLOTS_PER_EPOCH                      := 8
    MAX_COMMITTEES_PER_SLOT              := 4
    EPOCHS_PER_ETH1_VOTING_PERIOD        := 4
    SLOTS_PER_HISTORICAL_ROOT            := 64
    EPOCHS_PER_HISTORICAL_VECTOR         := 64
    EPOCHS_PER_SLASHINGS_VECTOR          := 64
    SYNC_COMMITTEE_SIZE                  := 32
    MAX_WITHDRAWALS_PER_PAYLOAD          := 4
    MAX_BLOB_COMMITMENTS_PER_BLOCK       := 4096
    KZG_COMMITMENT_INCLUSION_PROOF_DEPTH := 17
    PENDING_PARTIAL_WITHDRAWALS_LIMIT    := 64
    PENDING_CONSOLIDATIONS_LIMIT         := 64
    PTC_SIZE                             := 16
    MAX_PAYLOAD_ATTESTATIONS             := 4
    BUILDER_REGISTRY_LIMIT               := 1099511627776
    BUILDER_PENDING_WITHDRAWALS_LIMIT    := 1048576
    MAX_BUILDERS_PER_WITHDRAWALS_SWEEP   := 16 }

/-- Mainnet preset, the production protocol parameters. -/
def mainnet : Preset :=
  { SLOTS_PER_EPOCH                      := 32
    MAX_COMMITTEES_PER_SLOT              := 64
    EPOCHS_PER_ETH1_VOTING_PERIOD        := 64
    SLOTS_PER_HISTORICAL_ROOT            := 8192
    EPOCHS_PER_HISTORICAL_VECTOR         := 65536
    EPOCHS_PER_SLASHINGS_VECTOR          := 8192
    SYNC_COMMITTEE_SIZE                  := 512
    MAX_WITHDRAWALS_PER_PAYLOAD          := 16
    MAX_BLOB_COMMITMENTS_PER_BLOCK       := 4096
    KZG_COMMITMENT_INCLUSION_PROOF_DEPTH := 17
    PENDING_PARTIAL_WITHDRAWALS_LIMIT    := 134217728
    PENDING_CONSOLIDATIONS_LIMIT         := 262144
    PTC_SIZE                             := 512
    MAX_PAYLOAD_ATTESTATIONS             := 4
    BUILDER_REGISTRY_LIMIT               := 1099511627776
    BUILDER_PENDING_WITHDRAWALS_LIMIT    := 1048576
    MAX_BUILDERS_PER_WITHDRAWALS_SWEEP   := 16384 }

end Preset

end LeanEthCS
