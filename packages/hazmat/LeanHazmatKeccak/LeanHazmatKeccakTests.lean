import LeanHazmatKeccakTests.Vectors

/-!
# `LeanHazmatKeccakTests`: Keccak-256 Known-Answer-Test gate

The self-contained KAT suite for the keccak-tiny-backed shim. Build with:

```
lake build LeanHazmatKeccakTests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a published Keccak-256 vector, *no* dependency on any other
package, so this validates standalone (the property that lets the
family ship as a mirror, packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since Keccak-256 has no pure-Lean
reference, these vectors are the family's entire trust-validation
surface.
-/
