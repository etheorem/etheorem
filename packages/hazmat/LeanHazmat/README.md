# LeanHazmat

The top [LeanHazmat](../docs/ARCHITECTURE.md) umbrella: every
Ethereum-protocol crypto family, consensus **and** execution layer,
in one `require`. Pure `lakefile.toml`, no C.

```toml
[[require]]
name = "LeanHazmat"
path = "…/packages/hazmat/LeanHazmat"   # or a git source
```

`import LeanHazmat` brings the whole `LeanHazmat.*` surface into scope:

* **Consensus** (via `LeanHazmatConsensus`): `LeanHazmat.Sha256`,
  `LeanHazmat.Bls`, `LeanHazmat.Kzg`.
* **Execution** (via `LeanHazmatExecution`): `LeanHazmat.Keccak`,
  `LeanHazmat.Secp256k1`, `LeanHazmat.Bn254`, `LeanHazmat.Blake2f`,
  `LeanHazmat.Ripemd160`, `LeanHazmat.Modexp`, `LeanHazmat.P256`.

This umbrella compiles and links every family. Consumers wanting a
subset should require a sub-aggregator (`LeanHazmatConsensus`,
`LeanHazmatExecution`) or the single family package instead. Consuming
one family on its own is the packaging model's whole point.

The vendored families need their `just hazmat-*-vendor` fetches before
`lake build` (or run `just build`, which fetches them first).

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
