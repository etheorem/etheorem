import LeanSha256Tests.Nist

/-!
# `LeanSha256Tests`: LeanSha256 NIST CAVP gates

The full NIST CAVP byte-oriented test suite for SHA-256 (129
vectors: 65 ShortMsg + 64 LongMsg), auto-generated from
`cavp/SHA256*Msg.rsp` by `scripts/gen_sha256_cavp.py` (sibling of
the `cavp/` directory inside this package). Each vector is a
`native_decide` assertion that `LeanSha256.hash msg = md`.

Build with:

```
lake build LeanSha256Tests
```

The 3 anchor `native_decide` gates from FIPS 180-4 §B (empty
input, `"abc"`, 56-byte §B.2) stay inside `LeanSha256.Core` itself,
building the library proper validates them. The 129 CAVP vectors
live here because their `native_decide` batch is heavy (~108s) and
shouldn't run on every `lake build LeanSha256`.
-/
