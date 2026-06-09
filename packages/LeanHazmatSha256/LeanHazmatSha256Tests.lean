import LeanHazmatSha256Tests.Vectors
import LeanHazmatSha256Tests.Cavp

/-!
# `LeanHazmatSha256Tests`: byte-level Known-Answer-Test gates

The self-contained KAT suite for the OpenSSL-backed SHA-256 FFI
shims. Build with:

```
lake build LeanHazmatSha256Tests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a hard-coded known answer, with *no* dependency on `LeanSha256`
or `SizzLean`, so this package validates standalone (the property
that lets it ship as a mirror, hazmat-docs/ARCHITECTURE.md §3.3/§11).

## What's here

* **`Vectors`**: anchor cases for all three primitives: FIPS 180-4
  §B digests for `sha256Hash`, the SSZ `ZERO_HASHES[1]` and a
  cross-check for `sha256Combine`, and empty/single/multi/order cases
  for `sha256BatchCombine`.
* **`Cavp`**: the full NIST CAVP byte-oriented suite (129 vectors:
  65 ShortMsg + 64 LongMsg) run against `sha256Hash`, auto-generated
  from `cavp/SHA256*Msg.rsp` by `scripts/gen_cavp.py`.

## What lives elsewhere

The FFI ≡ pure-Lean *equivalence* cross-checks (the empirical
evidence behind SizzLean's `sha256{Hash,Combine,BatchCombine}_eq_spec`
axioms) need both this package and `LeanSha256`, so they live in
`SizzLeanTests` (`Sha256Equivalence`, `Sha256BatchEquivalence`), the
one layer that imports both.
-/
