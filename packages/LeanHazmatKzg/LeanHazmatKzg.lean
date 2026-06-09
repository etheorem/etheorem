import LeanHazmatKzg.Ffi

/-!
# `LeanHazmatKzg`: library root

FFI bindings for **Ethereum consensus-layer KZG / polynomial
commitments**, EIP-4844 blobs and EIP-7594 / Fulu PeerDAS cells,
wrapping ethereum/c-kzg-4844 behind `@[extern]` under the `LeanHazmat.Kzg`
brand namespace. Part of the [LeanHazmat](../../hazmat-docs/ARCHITECTURE.md)
crypto family.

`import LeanHazmatKzg` brings the public surface into scope (namespace
`LeanHazmat.Kzg`):

* EIP-4844: `blobToKzgCommitment`, `computeKzgProof`,
  `computeBlobKzgProof`, `verifyKzgProof`, `verifyBlobKzgProof`,
  `verifyBlobKzgProofBatch`.
* Fulu PeerDAS: `computeCellsAndKzgProofs`, `verifyCellKzgProofBatch`,
  `recoverCellsAndKzgProofs`.
* Size constants: `bytesPerBlob`, `bytesPerCommitment`, …

See [`LeanHazmatKzg/Ffi.lean`](LeanHazmatKzg/Ffi.lean) for the bindings
and trust assumptions, and [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
for the family trust boundary.

## Dependencies & vendoring

This is the **one** LeanHazmat family that is not zero-dependency: it
`require`s `LeanHazmatBls` to share its single compiled **blst** archive
(hazmat-docs/ARCHITECTURE.md §4). Two vendoring steps are needed before
`lake build`:

```bash
just vendor-bls    # blst v0.3.16 (the rev c-kzg v2.1.7 expects)
just vendor-kzg    # c-kzg-4844 v2.1.7 (no --recursive blst)
```

`just vendor-kzg` also refreshes `data/trusted_setup.txt`, which is
embedded into the archive at build time (no runtime file lookup).

## Trust boundary

KZG has no pure-Lean reference; each binding is an opaque `@[extern]`
boundary validated only against the spec KZG vectors. KAT gates live in
`LeanHazmatKzgTests` (`lake build LeanHazmatKzgTests`).
-/
