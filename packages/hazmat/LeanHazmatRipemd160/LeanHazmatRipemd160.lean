import LeanHazmatRipemd160.Ffi

/-!
# `LeanHazmatRipemd160`: library root

FFI binding for **RIPEMD-160**, the execution-layer precompile at
address 0x03, wrapping the system OpenSSL `libcrypto` behind
`@[extern]` under the `LeanHazmat.Ripemd160` brand namespace. Part of
the [LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatRipemd160` brings the public surface into scope:

* `ripemd160`: 20-byte digest of an arbitrary-length input.

See
[`LeanHazmatRipemd160/Ffi.lean`](LeanHazmatRipemd160/Ffi.lean) for the
binding and its trust assumption, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (library, provider loading, validation vectors).

## The provider

Where RIPEMD-160 lives changed across OpenSSL 3.x: 3.0.0 through 3.0.6
ship the digest only in the **legacy provider**, from 3.0.7 the
**default** provider carries it. The shim asks the default provider
first and loads the legacy provider into a **private `OSSL_LIB_CTX`**
as a fallback, so the process's default context stays untouched. A
setup that cannot load `default` surfaces as the empty `ByteArray`. No
vendoring and no C build beyond the shim: libcrypto is a system
library discovered with `pkg-config`, exactly as in
`LeanHazmatSha256`.

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary validated only against the published vectors
(`LeanHazmatRipemd160Tests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatRipemd160Tests`); the default `lake build` skips them and
they fire via `lake build LeanHazmatRipemd160Tests`.
-/
