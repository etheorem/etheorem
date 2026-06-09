# LeanHazmatKzg

Lean 4 FFI bindings for Ethereum KZG / polynomial commitments, EIP-4844
blobs and EIP-7594 (Fulu / PeerDAS) cells, wrapping
[ethereum/c-kzg-4844](https://github.com/ethereum/c-kzg-4844). Part of the
[LeanHazmat](../../hazmat-docs/ARCHITECTURE.md) FFI crypto family.

## Setup

This package `require`s `LeanHazmatBls` (it reuses Bls's vendored
**blst**). Fetch both vendored sources once, then build:

```bash
just vendor-bls    # blst v0.3.16 (the rev c-kzg v2.1.7 expects)
just vendor-kzg    # c-kzg-4844 v2.1.7
lake build LeanHazmatKzg
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatKzg"
path = "…/packages/LeanHazmatKzg"     # or a git source
```

The KZG trusted setup is embedded in the build, with no runtime file to ship
or locate.

## Usage

The EIP-4844 blob flow, commit to a blob, produce a proof, verify it:

```lean
import LeanHazmatKzg
open LeanHazmat.Kzg

-- A blob is 4096 field elements = 131072 bytes (here, an all-zero blob).
def blob : ByteArray := ByteArray.mk (Array.replicate bytesPerBlob 0)

def commitment : ByteArray := blobToKzgCommitment blob            -- 48 bytes
def proof      : ByteArray := computeBlobKzgProof blob commitment -- 48 bytes

/-- Verify a blob sidecar you received (the common consensus-client path). -/
def checkBlobSidecar (blob commitment proof : ByteArray) : Bool :=
  verifyBlobKzgProof blob commitment proof

/-- Run it in a compiled program. -/
def main : IO Unit := do
  IO.println s!"sidecar valid: {checkBlobSidecar blob commitment proof}"   -- true
  IO.println s!"batch valid:   {verifyBlobKzgProofBatch #[blob] #[commitment] #[proof]}"
```

Point-evaluation proof (the EIP-4844 `0x0a` precompile primitive), open
the committed polynomial at a point `z`, get the value `y`, then verify:

```lean
def z : ByteArray := ByteArray.mk ((Array.replicate 31 0).push 2)  -- field element 2

def evalOk : Bool :=
  let (proof, y) := computeKzgProof blob z
  verifyKzgProof commitment z y proof
```

Fulu / PeerDAS cells, extend a blob to 128 cells with proofs, batch-verify
them, and recover the full set from any ≥ 50 % subset:

```lean
def cellsAndProofs := computeCellsAndKzgProofs blob   -- (Array 128 cells, Array 128 proofs)
def cells  := cellsAndProofs.1
def proofs := cellsAndProofs.2
def idx : Array UInt64 := (Array.range cellsPerExtBlob).map (·.toUInt64)

def cellsOk : Bool :=
  verifyCellKzgProofBatch (Array.replicate cellsPerExtBlob commitment) idx cells proofs

-- recover all 128 cells from the first 64:
def recovered : Array ByteArray :=
  (recoverCellsAndKzgProofs ((Array.range 64).map (·.toUInt64)) (cells.extract 0 64)).1
```

### Running and checking

These are `@[extern]` native primitives, so they run as **compiled** code.
Call them from an executable (`lake exe …`) or a `def`/`IO` action your app
compiles. To assert results at build time, use `native_decide` (this is how
the test suite runs them):

```lean
example : verifyBlobKzgProof blob commitment proof = true := by native_decide
```

Plain `#eval` in the interpreter cannot execute opaque `@[extern]` functions.

### Error handling

Point/byte results use the **empty `ByteArray`** as the error sentinel (bad
input length, malformed point, internal failure), with no exception.
Verification returns `Bool`, where `false` covers both "does not verify" and
invalid input:

```lean
example : (blobToKzgCommitment (ByteArray.mk #[0x00])).isEmpty = true := by native_decide
```

## API (namespace `LeanHazmat.Kzg`)

```lean
-- EIP-4844
blobToKzgCommitment    : ByteArray → ByteArray                        -- blob → commitment(48)
computeKzgProof        : ByteArray → ByteArray → ByteArray × ByteArray -- blob, z → (proof(48), y(32))
computeBlobKzgProof    : ByteArray → ByteArray → ByteArray            -- blob, commitment → proof(48)
verifyKzgProof         : ByteArray → ByteArray → ByteArray → ByteArray → Bool
verifyBlobKzgProof     : ByteArray → ByteArray → ByteArray → Bool
verifyBlobKzgProofBatch : Array ByteArray → Array ByteArray → Array ByteArray → Bool

-- EIP-7594 / Fulu
computeCellsAndKzgProofs : ByteArray → Array ByteArray × Array ByteArray
verifyCellKzgProofBatch  : Array ByteArray → Array UInt64 → Array ByteArray → Array ByteArray → Bool
recoverCellsAndKzgProofs : Array UInt64 → Array ByteArray → Array ByteArray × Array ByteArray
```

Size constants (`Nat`): `bytesPerBlob` 131072, `bytesPerCommitment` 48,
`bytesPerFieldElement` 32, `bytesPerCell` 2048, `cellsPerExtBlob` 128.

## Trust boundary

Each binding is an opaque `@[extern]` over c-kzg-4844, with no pure-Lean
reference, validated only against round-trips / spec vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatKzgTests     # EIP-4844 + Fulu round-trips
```

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../LICENSE).
