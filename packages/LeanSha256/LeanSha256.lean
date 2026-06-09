import LeanSha256.Core

/-!
# `LeanSha256`: pure-Lean SHA-256 reference (library root)

A *kernel-reducible* SHA-256 implementation. No FFI, no
typeclasses, no SSZ coupling, just `hash : ByteArray → ByteArray`
and `combine : ByteArray → ByteArray → ByteArray` plus a handful
of structural conformance lemmas against FIPS 180-4.

Distributable as an independent Lake package (license
`LGPL-3.0-only`, no external dependencies); see the in-package
`README.md` for the `[[require]]` snippet downstream consumers
should use.

This root re-exports the implementation:

* `LeanSha256.Core`: FIPS 180-4 constants, round functions,
  message schedule, compression, padding, byte/word conversions,
  `hash`, `combine`, structural lemmas, and three in-file
  `native_decide` examples anchoring the spec against FIPS 180-4
  §B (empty input, `"abc"`, 56-byte §B.2). Building this library
  runs those three gates.

The heavy NIST CAVP suite (129 byte-oriented vectors, ~108s of
`native_decide` at compile time) lives in a separate test library
at `packages/LeanSha256/LeanSha256Tests/`, exposed under the
`LeanSha256Tests.*` module hierarchy (package-prefixed to avoid
collision with `SizzLean`'s `SizzLeanTests` lib in the umbrella
build). Build with `lake build LeanSha256Tests` or
`just test-sha256`. Splitting it out keeps `lake build LeanSha256`
fast for downstream consumers (e.g. `SizzLean`); the full NIST
gate is opt-in.
-/
