# LeanHazmatConsensus

The consensus-layer [LeanHazmat](../docs/ARCHITECTURE.md)
aggregator: one `require` that pulls in and re-exports the three
consensus crypto families. Pure `lakefile.toml`, no C.

```toml
[[require]]
name = "LeanHazmatConsensus"
path = "…/packages/hazmat/LeanHazmatConsensus"   # or a git source
```

`import LeanHazmatConsensus` brings into scope:

| Namespace | Family | Package |
| --- | --- | --- |
| `LeanHazmat.Sha256` | FFI SHA-256 (OpenSSL) | `LeanHazmatSha256` |
| `LeanHazmat.Bls` | BLS12-381 signatures (blst) | `LeanHazmatBls` |
| `LeanHazmat.Kzg` | KZG commitments / proofs (c-kzg-4844) | `LeanHazmatKzg` |

Families remain consumable on their own (`import LeanHazmatBls`). The
vendored families need their `just hazmat-bls-vendor` /
`hazmat-kzg-vendor` fetches before `lake build`.

For the execution-layer families see `LeanHazmatExecution`; for
everything at once, the top [`LeanHazmat`](../LeanHazmat/README.md)
umbrella.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
