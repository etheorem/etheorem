import LeanHazmatRipemd160Tests.Vectors

/-!
# `LeanHazmatRipemd160Tests`: RIPEMD-160 Known-Answer-Test gate

The self-contained KAT suite for the OpenSSL-backed shim. Build with:

```
lake build LeanHazmatRipemd160Tests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a published vector, *no* dependency on any other package, so
this validates standalone (the property that lets the family ship as a
mirror, packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since RIPEMD-160 has no pure-Lean
reference, these vectors are the family's entire trust-validation
surface.
-/
