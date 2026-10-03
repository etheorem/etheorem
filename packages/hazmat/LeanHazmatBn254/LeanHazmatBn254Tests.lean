import LeanHazmatBn254Tests.Vectors

/-!
# `LeanHazmatBn254Tests`: alt_bn128 Known-Answer-Test gate

The self-contained KAT suite for the mcl-backed shims. Build with:

```
lake build LeanHazmatBn254Tests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a py_ecc-generated ground-truth vector or a negative case, *no*
dependency on any other package, so this validates standalone (the
property that lets the family ship as a mirror,
packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since BN254 pairing computation has
no pure-Lean reference, these vectors are the family's entire
trust-validation surface.
-/
