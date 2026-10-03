import LeanHazmatP256.Ffi

/-!
# `LeanHazmatP256`: library root

FFI binding for **NIST P-256 (secp256r1) ECDSA verification**, the
primitive behind the execution-layer `P256VERIFY` precompile (EIP-7951,
Fusaka), wrapping the system OpenSSL `libcrypto` behind `@[extern]`
under the `LeanHazmat.P256` brand namespace. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatP256` brings the public surface into scope:

* `p256Verify`: `(msgHash, r, s, qx, qy)` → `Bool`, all fields 32-byte
  big-endian.

See [`LeanHazmatP256/Ffi.lean`](LeanHazmatP256/Ffi.lean) for the
binding and its trust assumption, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (library, encodings, validation vectors).

No vendoring and no C build beyond the shim: libcrypto is a system
library discovered with `pkg-config`, exactly as in
`LeanHazmatSha256`.

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary validated only against the official EIP-7951 vectors
(`LeanHazmatP256Tests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatP256Tests`); the default `lake build` skips them and they
fire via `lake build LeanHazmatP256Tests`.
-/
