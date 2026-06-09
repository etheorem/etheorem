import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.Primitives`: Deneb KZG / blob primitives

Deneb (EIP-4844, "proto-danksharding") introduces blob-carrying
transactions and the KZG commitment scheme. The four primitives here
are byte-array aliases.

## Constants (preset-invariant)

* `BYTES_PER_FIELD_ELEMENT = 32`
* `FIELD_ELEMENTS_PER_BLOB = 4096`
* `BYTES_PER_BLOB = FIELD_ELEMENTS_PER_BLOB * BYTES_PER_FIELD_ELEMENT = 131_072`
* `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH = 17`
* `MAX_BLOB_COMMITMENTS_PER_BLOCK = 4096`
-/

set_option autoImplicit false

namespace LeanEthCS

open SizzLean

/-- 48-byte KZG commitment. -/
abbrev KZGCommitment := Vector UInt8 48

/-- 48-byte KZG proof. -/
abbrev KZGProof := Vector UInt8 48

/-- Blob index inside a block. -/
abbrev BlobIndex := UInt64

/-- One blob, a fixed-size byte array of `BYTES_PER_BLOB = 131072`
bytes (= `FIELD_ELEMENTS_PER_BLOB * BYTES_PER_FIELD_ELEMENT`). -/
abbrev Blob := Vector UInt8 131072

end LeanEthCS
