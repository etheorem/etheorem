import LeanHazmatBlsTests.Vectors

/-!
# `LeanHazmatBlsTests`: consensus BLS Known-Answer-Test gates

The self-contained KAT suite for the blst-backed BLS shims. Build with:

```
lake build LeanHazmatBlsTests
```

Every gate is a `native_decide` assertion that runs the compiled blst
FFI against either a published consensus-spec vector or a self-contained
round-trip, *no* dependency on any other package, so this validates
standalone (the property that lets the family ship as a mirror,
hazmat-docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since BLS has no pure-Lean reference,
these vectors are the family's entire trust-validation surface.
-/
