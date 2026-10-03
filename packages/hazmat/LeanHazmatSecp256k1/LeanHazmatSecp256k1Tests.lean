import LeanHazmatSecp256k1Tests.Vectors

/-!
# `LeanHazmatSecp256k1Tests`: secp256k1 Known-Answer-Test gate

The self-contained KAT suite for the libsecp256k1-backed shims. Build
with:

```
lake build LeanHazmatSecp256k1Tests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a published vector or a self-contained round-trip, *no*
dependency on any other package, so this validates standalone (the
property that lets the family ship as a mirror,
packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since secp256k1 ECDSA has no
pure-Lean reference, these vectors are the family's entire
trust-validation surface.
-/
