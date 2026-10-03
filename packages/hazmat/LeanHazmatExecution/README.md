# LeanHazmatExecution

The execution-layer [LeanHazmat](../docs/ARCHITECTURE.md)
aggregator: one `require` that pulls in and re-exports the seven EL
crypto families. Pure `lakefile.toml`, no C.

```toml
[[require]]
name = "LeanHazmatExecution"
path = "…/packages/hazmat/LeanHazmatExecution"   # or a git source
```

`import LeanHazmatExecution` brings into scope:

| Namespace | Family | Package |
| --- | --- | --- |
| `LeanHazmat.Keccak` | Keccak-256 (keccak-tiny) | `LeanHazmatKeccak` |
| `LeanHazmat.Secp256k1` | ECDSA recovery / verify (libsecp256k1) | `LeanHazmatSecp256k1` |
| `LeanHazmat.Bn254` | alt_bn128 add/mul/pairing (mcl) | `LeanHazmatBn254` |
| `LeanHazmat.Blake2f` | BLAKE2b `F` compression (in-repo RFC 7693) | `LeanHazmatBlake2f` |
| `LeanHazmat.Ripemd160` | RIPEMD-160 (OpenSSL, default or legacy provider) | `LeanHazmatRipemd160` |
| `LeanHazmat.Modexp` | modular exponentiation (OpenSSL BIGNUM) | `LeanHazmatModexp` |
| `LeanHazmat.P256` | P256VERIFY (OpenSSL, NIST P-256) | `LeanHazmatP256` |

Three more EL precompiles reuse consensus packages at zero new
dependencies: SHA-256 (0x02) → `LeanHazmat.Sha256`, KZG point
evaluation (0x0a) → `LeanHazmat.Kzg`, EIP-2537 BLS → `LeanHazmat.Bls`
(require `LeanHazmatConsensus` or the top `LeanHazmat` umbrella for
those).

The vendored families need their `just hazmat-keccak-vendor` /
`hazmat-secp256k1-vendor` / `hazmat-bn254-vendor` fetches before
`lake build`. Each package exposes the **raw** primitive; precompile
composition (input parse, gas, output encoding) is the consumer's.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
