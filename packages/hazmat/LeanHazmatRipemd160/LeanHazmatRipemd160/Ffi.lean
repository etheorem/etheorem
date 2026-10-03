/-!
# `LeanHazmatRipemd160.Ffi`: RIPEMD-160 behind `@[extern]`

One `@[extern] opaque` declaration bridges Lean to the C shim in
`csrc/ripemd160_shim.c`: RIPEMD-160, the execution-layer precompile at
address 0x03.

This module deliberately holds **only** the FFI binding. The
precompile's output encoding (left-padding the 20-byte digest to 32
bytes) is the consumer's concern, per the LeanHazmat "raw primitives,
not assembled precompiles" rule (packages/hazmat/docs/ARCHITECTURE.md §4).

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatRipemd160`); the
declaration lives under the *brand* namespace `LeanHazmat.Ripemd160`.
The two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Providers

Where RIPEMD-160 lives changed across OpenSSL 3.x: 3.0.0-3.0.6 ship it
only in the **legacy provider**; from 3.0.7 the default provider
carries it. The shim creates a **private** `OSSL_LIB_CTX`, loads
`default` (required) and `legacy` (best-effort) into it, and lets the
digest fetch decide (loading into the process's default context would
disable the automatic default-provider load process-wide), via
`pthread_once`; a setup that cannot load `default` returns the empty
`ByteArray`.

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for RIPEMD-160; the binding is an opaque
`@[extern]` boundary. The empirical trust assumption, *that the linked
OpenSSL libcrypto implements RIPEMD-160 correctly (through whichever
provider supplies it)*, is validated only against the published vectors in
`LeanHazmatRipemd160Tests/`.

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*. Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these.
-/

set_option autoImplicit false

namespace LeanHazmat.Ripemd160

/-- 20-byte RIPEMD-160 digest of an arbitrary-length input. Runtime
implementation is `csrc/ripemd160_shim.c`'s
`lean_hazmat_ripemd160_hash`, which wraps OpenSSL's `EVP_Q_digest`
against a private context (the legacy provider loads best-effort; the
default provider carries RIPEMD-160 from OpenSSL 3.0.7 on).

This is the execution-layer precompile 0x03's primitive, **not** a
general-purpose recommendation (RIPEMD-160 is legacy everywhere else).

Empty `ByteArray` if no provider supplies RIPEMD-160 or the
digest fails.

**Trust assumption:** the linked OpenSSL `libcrypto` computes
RIPEMD-160 correctly. Validated by the published vectors in
`LeanHazmatRipemd160Tests/Vectors.lean`. -/
@[extern "lean_hazmat_ripemd160_hash"]
opaque ripemd160 (input : @& ByteArray) : ByteArray

end LeanHazmat.Ripemd160
