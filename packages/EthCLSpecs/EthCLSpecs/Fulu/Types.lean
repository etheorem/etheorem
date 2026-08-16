import EthCLSpecs.Fulu.Fork

/-!
# `EthCLSpecs.Fulu.Types`: consensus type aliases (load order row 1)

The fork's primitive vocabulary as aliases over SizzLean's SSZ basic types and
the crypto-backend byte buffers (`SPECS_ARCHITECTURE.md` §3.1 row 1). Each is a
`forkabbrev`: reducible, so SSZRepr instance synthesis sees straight through
`Root` to the underlying `Vector UInt8 32` instance, and captured, so a child
fork replays the whole vocabulary into its own namespace with `inherit` rather
than reaching into this one.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- A slot number. -/
forkabbrev Slot := UInt64
/-- An epoch number. -/
forkabbrev Epoch := UInt64
/-- An index into the validator registry. -/
forkabbrev ValidatorIndex := UInt64
/-- An index into the builder registry (Gloas/EIP-7732). SSZ `uint64`. -/
forkabbrev BuilderIndex := UInt64
/-- An index into a committee. -/
forkabbrev CommitteeIndex := UInt64
/-- An index into the withdrawal queue. -/
forkabbrev WithdrawalIndex := UInt64
/-- A balance, in gwei. SSZ `uint64`. -/
forkabbrev Gwei := UInt64
/-- A 32-byte SSZ Merkle root. -/
forkabbrev Root := Vector UInt8 32
/-- A generic 32-byte value. -/
forkabbrev Bytes32 := Vector UInt8 32
/-- An execution-layer block hash (32 bytes). -/
forkabbrev Hash32 := Vector UInt8 32
/-- A 4-byte fork version. -/
forkabbrev Version := Vector UInt8 4
/-- A 4-byte domain-separation tag. -/
forkabbrev DomainType := Vector UInt8 4
/-- A 32-byte signature domain. -/
forkabbrev Domain := Vector UInt8 32
/-- A 48-byte BLS public key. -/
forkabbrev BLSPubkey := Vector UInt8 48
/-- A 96-byte BLS signature. -/
forkabbrev BLSSignature := Vector UInt8 96
/-- A 20-byte execution-layer address. -/
forkabbrev ExecutionAddress := Vector UInt8 20
/-- Per-validator participation flag bits (Altair onward). SSZ `uint8`. -/
forkabbrev ParticipationFlags := UInt8
/-- A blob-commitment KZG point (48 bytes). -/
forkabbrev KZGCommitment := Vector UInt8 48
/-- A KZG opening proof (48 bytes), same width as a commitment. -/
forkabbrev KZGProof := Vector UInt8 48
/-- A PeerDAS extended-blob cell: `BYTES_PER_FIELD_ELEMENT * FIELD_ELEMENTS_PER_CELL`
= `32 * 64` = 2048 bytes. -/
forkabbrev Cell := Vector UInt8 2048
/-- A PeerDAS data-column index (`= CellIndex`; one of `NUMBER_OF_COLUMNS`). -/
forkabbrev ColumnIndex := UInt64
/-- A PeerDAS cell index into an extended blob. -/
forkabbrev CellIndex := UInt64
/-- An RLP-encoded execution transaction: an SSZ `ByteList[MAX_BYTES_PER_TRANSACTION]`. -/
forkabbrev Transaction := SizzLean.Repr.SSZList UInt8 (2 ^ 30)

end EthCLSpecs.Fulu
