# packages/hazmat: the LeanHazmat FFI crypto family

Thirteen Lake packages, one per Ethereum-protocol crypto primitive,
grouped because they share one design, one vendor discipline, and one
trust model. This directory is a plain container: it holds no package
of its own.

- **Consensus**: `LeanHazmatSha256` (OpenSSL), `LeanHazmatBls` (blst),
  `LeanHazmatKzg` (c-kzg-4844).
- **Execution**: `LeanHazmatKeccak` (keccak-tiny),
  `LeanHazmatSecp256k1` (libsecp256k1), `LeanHazmatBn254` (mcl),
  `LeanHazmatBlake2f` (in-repo RFC 7693 shim), `LeanHazmatRipemd160`,
  `LeanHazmatModexp`, `LeanHazmatP256` (OpenSSL).
- **Aggregators**: `LeanHazmatConsensus`, `LeanHazmatExecution`, and
  the top `LeanHazmat` umbrella.

## Vector tests

Every family ships a `LeanHazmat<Family>Tests` gate, and each case is
one `native_decide` that runs the compiled FFI call at proof-check
time. The consensus families have pure-Lean or spec references behind
them; the seven execution families have none, so their embedded KAT is
the only validation of the FFI boundary
([`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §10). The table lists
each family's vectors and where they come from.

| Package | Vector tests | Source | Official? |
| --- | --- | --- | --- |
| `LeanHazmatSha256` | The full NIST CAVP suite (129 vectors, in the generated `Cavp.lean`), plus FIPS 180-4 and SSZ anchors | `SHA256ShortMsg.rsp` / `SHA256LongMsg.rsp` from NIST's CAVP, committed under `cavp/` | Yes. NIST's official test files |
| `LeanHazmatBls` | Sign and verify anchors, plus round-trips over `aggregate`, `aggregateVerify`, `fastAggregateVerify`, and `ethFastAggregateVerify` | Lifted verbatim from the `ethereum/consensus-spec-tests` `general/phase0/bls` suite, v1.5.0 | Yes. The Ethereum Foundation's official vector release |
| `LeanHazmatKzg` | EIP-4844 commit, prove, verify, and batch-verify round-trips; EIP-7594 cell proofs and erasure recovery; each with a negative | Self-generated round-trips over the embedded trusted setup | No. The `consensus-specs` `kzg` vectors are not consumed yet |
| `LeanHazmatKeccak` | EVM canonical constants, short / one-block / multi-block digests, EIP-155 address derivation | The Keccak reference definition plus the constants Ethereum clients hard-code | Yes. Canonical digests from the Keccak reference spec |
| `LeanHazmatSecp256k1` | The EIP-155 example transaction, a second deterministic signature, tamper and off-curve negatives | The example the EIP-155 text publishes | Yes. Ground truth straight from the EIP |
| `LeanHazmatBn254` | G1 / G2 arithmetic, pairing checks, EIP-196/197 negatives, scalar-reduction cases | Generated from `ethereum/py_ecc`; `scripts/gen_vectors.py` re-checks the committed bytes | No. py_ecc is the reference implementation EIP-197 links, and there is no frozen vector release |
| `LeanHazmatBlake2f` | Published EIP-152 vectors 4 through 8 (rounds 0, 1, 12, `0xffffffff`), plus wrong-length sentinels | The five vectors in the EIP-152 text; `scripts/gen_vectors.py` cross-checks the extras | Yes. The EIP's published set |
| `LeanHazmatRipemd160` | The nine published vectors, including the million-`a` megabyte case | The RIPEMD-160 consortium's vector set, cross-checked against `openssl dgst -rmd160` | Yes. The algorithm authors' published set |
| `LeanHazmatModexp` | The EIP-198 worked examples verbatim, even moduli, zero-modulus negatives | The examples in the EIP-198 text; filler cases cross-checked against Python `pow` | Partly. The EIP cases are official; the filler cases are self-generated |
| `LeanHazmatP256` | Valid cases, the `n - s` malleability complement, order-complement `r`, duplication-bug and fixed negatives | The official EIP-7951 vector set (Project Wycheproof), a subset embedded | Yes. The vector set the EIP adopts |

The cross-family design of record, the trust-boundary doctrine, and the
stage plan live in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and
[`docs/PLAN.md`](docs/PLAN.md). Each family's own trust boundary is in
its `docs/ARCHITECTURE.md`.

Build one family from the repo root (`lake build LeanHazmatKeccak`) or
the whole group (`lake build LeanHazmat`). The vendored families need
their `just hazmat-<family>-vendor` fetch first.
