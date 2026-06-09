import LeanHazmatKzgTests.Vectors

/-!
# `LeanHazmatKzgTests`: KZG Known-Answer / round-trip gates

Self-contained validation of the c-kzg-4844 FFI surface. Build with:

```
lake build LeanHazmatKzgTests
```

Every gate is a `native_decide` running compiled c-kzg against a
self-contained round-trip (commit → prove → verify for EIP-4844; cells →
batch-verify and erasure-recovery for Fulu PeerDAS), including negatives.
Since KZG has no pure-Lean reference, these round-trips are the family's
entire trust-validation surface (hazmat-docs/ARCHITECTURE.md §10). They
also exercise loading the trusted setup embedded in the archive.

See `Vectors.lean` for the cases.
-/
