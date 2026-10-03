import LeanHazmatBlake2fTests.Vectors

/-!
# `LeanHazmatBlake2fTests`: EIP-152 Known-Answer-Test gate

The self-contained KAT suite for the in-repo BLAKE2f shim. Build with:

```
lake build LeanHazmatBlake2fTests
```

Every gate is a `native_decide` assertion that runs the compiled shim
against a published EIP-152 vector or a length-sentinel case, *no*
dependency on any other package, so this validates standalone (the
property that lets the family ship as a mirror,
packages/hazmat/docs/ARCHITECTURE.md §3.3/§11).

See `Vectors.lean` for the cases. Since BLAKE2f has no vendored
library, these vectors are the family's entire trust-validation
surface.
-/
