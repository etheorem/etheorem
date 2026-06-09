import SizzLean.Repr.Class
import SizzLean.Repr.Instances

/-!
# `LeanEthCS.Primitives`: consensus-specs primitive types

Each definition here is a faithful Lean transcription of a
consensus-specs *primitive*, the named types (`Slot`, `Epoch`,
`BLSPubkey`, …) used throughout the beacon-chain specification.
Composite types under `LeanEthCS/Forks/Phase0/`, `Altair/`, etc.
build on these via `deriving SSZRepr`.

## Naming convention

`abbrev` (not `structure`) is used for every primitive, they're
transparent aliases over the underlying SSZ representation, matching
consensus-specs's `NewType(...)` pattern. The benefit: `SSZRepr`
instances resolve automatically (via the underlying `UInt64` /
`Vector UInt8 N` instances) without needing to derive or hand-write
new instances per primitive. The cost: no nominal type-safety
between, say, `Slot` and `Epoch`, both are `UInt64` to the
typechecker. We accept this trade-off because (a) consensus-specs
itself doesn't enforce nominal safety, (b) deriving the alternative
(structures + manual `SSZRepr` instances) would add ~80 lines of
boilerplate per type for negligible value, and (c) the SSZ wire
format is identical either way.

## Spec reference

These map line-for-line to consensus-specs/specs/phase0/beacon-chain.md
*§Custom types* and the subsequent fork-deltas. Widths and lengths
are inlined at each `abbrev` rather than pulled from named
constants. The spec text uses the literal numbers in the same
places, and a named-constant indirection would obscure the mapping.
-/

set_option autoImplicit false

namespace LeanEthCS

open SizzLean

/-! ### `uint64`-shaped primitives -/

/-- Beacon-chain slot index. `uint64` per spec; values increment
once per `SECONDS_PER_SLOT` interval. -/
abbrev Slot := UInt64

/-- Epoch index, a group of `SLOTS_PER_EPOCH` slots. `uint64`. -/
abbrev Epoch := UInt64

/-- Index into the active validator registry. `uint64`. -/
abbrev ValidatorIndex := UInt64

/-- Index into a committee. `uint64`. -/
abbrev CommitteeIndex := UInt64

/-- Index of a withdrawal in the queue (Capella+). `uint64`. -/
abbrev WithdrawalIndex := UInt64

/-- Amount denominated in gwei (`10⁻⁹` ether). `uint64`. -/
abbrev Gwei := UInt64

/-! ### Byte-array primitives

All are `Vector UInt8 N` for a fixed `N`. The `SSZRepr (Vector α n)`
instance resolves these to `.vector (.uintN 8) n` shapes. -/

/-- 32-byte hash output (typically SHA-256 over a Merkleized SSZ
value). `Vector[byte, 32]` per spec, i.e. `.vector (.uintN 8) 32`. -/
abbrev Bytes32 := Vector UInt8 32

/-- Alias for `Bytes32`, used in spec for Merkle roots of containers. -/
abbrev Root := Vector UInt8 32

/-- Alias for `Bytes32`, used in spec for execution-layer block
hashes (post-Bellatrix). -/
abbrev Hash32 := Vector UInt8 32

/-- 20-byte Ethereum address (post-Bellatrix). -/
abbrev ExecutionAddress := Vector UInt8 20

/-- 48-byte BLS12-381 public key. -/
abbrev BLSPubkey := Vector UInt8 48

/-- 96-byte BLS12-381 signature. -/
abbrev BLSSignature := Vector UInt8 96

/-- 4-byte fork version (e.g. `0x00000000` for genesis). -/
abbrev Version := Vector UInt8 4

/-- 4-byte domain type tag (used in BLS domain construction). -/
abbrev DomainType := Vector UInt8 4

/-- 32-byte domain (4-byte type + 28-byte fork-version digest). -/
abbrev Domain := Vector UInt8 32

/-! ### `uint8`-shaped primitives -/

/-- 8-bit packed attestation participation flags (Altair+). -/
abbrev ParticipationFlags := UInt8

end LeanEthCS
