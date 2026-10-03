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

The cross-family design of record, the trust-boundary doctrine, and the
stage plan live in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and
[`docs/PLAN.md`](docs/PLAN.md). Each family's own trust boundary is in
its `docs/ARCHITECTURE.md`.

Build one family from the repo root (`lake build LeanHazmatKeccak`) or
the whole group (`lake build LeanHazmat`). The vendored families need
their `just hazmat-<family>-vendor` fetch first.
