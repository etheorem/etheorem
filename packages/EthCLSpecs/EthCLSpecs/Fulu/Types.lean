import SizzLean

/-!
# `EthCLSpecs.Fulu.Types`: consensus type aliases (load order row 1)

The fork's primitive vocabulary as aliases over SizzLean's SSZ basic types and
the crypto-backend byte buffers (`SPECS_ARCHITECTURE.md` §3.1 row 1). Aliases are
`@[reducible]` (`abbrev`), so SSZRepr instance synthesis sees straight through
them to the underlying `UInt64` / `Vector` instance.
-/

set_option autoImplicit false


namespace EthCLSpecs.Fulu

/-- A slot number. -/
abbrev Slot := UInt64
/-- An epoch number. -/
abbrev Epoch := UInt64
/-- An index into the validator registry. -/
abbrev ValidatorIndex := UInt64
/-- An index into the builder registry (Gloas/EIP-7732). SSZ `uint64`. -/
abbrev BuilderIndex := UInt64
/-- An index into a committee. -/
abbrev CommitteeIndex := UInt64
/-- An index into the withdrawal queue. -/
abbrev WithdrawalIndex := UInt64
/-- A balance, in gwei. SSZ `uint64`. -/
abbrev Gwei := UInt64
/-- A 32-byte SSZ Merkle root. -/
abbrev Root := Vector UInt8 32
/-- A generic 32-byte value. -/
abbrev Bytes32 := Vector UInt8 32
/-- An execution-layer block hash (32 bytes). -/
abbrev Hash32 := Vector UInt8 32
/-- A 4-byte fork version. -/
abbrev Version := Vector UInt8 4
/-- A 4-byte domain-separation tag. -/
abbrev DomainType := Vector UInt8 4
/-- A 32-byte signature domain. -/
abbrev Domain := Vector UInt8 32
/-- A 48-byte BLS public key. -/
abbrev BLSPubkey := Vector UInt8 48
/-- A 96-byte BLS signature. -/
abbrev BLSSignature := Vector UInt8 96
/-- A 20-byte execution-layer address. -/
abbrev ExecutionAddress := Vector UInt8 20
/-- Per-validator participation flag bits (Altair onward). SSZ `uint8`. -/
abbrev ParticipationFlags := UInt8
/-- A blob-commitment KZG point (48 bytes). -/
abbrev KZGCommitment := Vector UInt8 48
/-- A KZG opening proof (48 bytes), same width as a commitment. -/
abbrev KZGProof := Vector UInt8 48
/-- A PeerDAS extended-blob cell: `BYTES_PER_FIELD_ELEMENT * FIELD_ELEMENTS_PER_CELL`
= `32 * 64` = 2048 bytes. -/
abbrev Cell := Vector UInt8 2048
/-- A PeerDAS data-column index (`= CellIndex`; one of `NUMBER_OF_COLUMNS`). -/
abbrev ColumnIndex := UInt64
/-- A PeerDAS cell index into an extended blob. -/
abbrev CellIndex := UInt64
/-- An RLP-encoded execution transaction: an SSZ `ByteList[MAX_BYTES_PER_TRANSACTION]`. -/
abbrev Transaction := SizzLean.Repr.SSZList UInt8 (2 ^ 30)

end EthCLSpecs.Fulu
