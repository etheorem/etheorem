import LeanHazmatModexpTests.Vectors

/-!
# `LeanHazmatModexpTests`: modexp Known-Answer-Test gate

The self-contained KAT suite for the OpenSSL-BIGNUM-backed shim. Build
with:

```
lake build LeanHazmatModexpTests
```

Every gate is a `native_decide` assertion that runs the compiled FFI
against a published example or a fixed modular-arithmetic case, *no*
dependency on any other package, so this validates standalone (the
property that lets the family ship as a mirror,
packages/hazmat/docs/ARCHITECTURE.md §3.3/§11). The suite does not cover the
EIP-198 parse rules (excess data, right padding); the caller applies
those before the primitive runs. See the Ffi module docstring.

See `Vectors.lean` for the cases. Since modular exponentiation has no
pure-Lean reference at this size, these vectors are the family's
entire trust-validation surface.
-/
