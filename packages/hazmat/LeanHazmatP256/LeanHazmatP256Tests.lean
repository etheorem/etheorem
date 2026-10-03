import LeanHazmatP256Tests.Vectors

/-!
# `LeanHazmatP256Tests`: P256VERIFY Known-Answer-Test gate

The self-contained KAT suite for the OpenSSL-backed shim. Build with:

```
lake build LeanHazmatP256Tests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against an official EIP-7951 vector or a negative case, *no*
dependency on any other package, so this validates standalone (the
property that lets the family ship as a mirror,
packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since P-256 ECDSA has no pure-Lean
reference, these vectors are the family's entire trust-validation
surface.
-/
