# LeanHazmatRipemd160

Lean 4 FFI binding for **RIPEMD-160**, the execution-layer precompile
at address 0x03. Wraps the system OpenSSL `libcrypto` (3.x **default
or legacy provider**). Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto family.

## Providers

Where RIPEMD-160 lives changed across OpenSSL 3.x: 3.0.0-3.0.6 ship it
only in the **legacy provider**; from 3.0.7 the default provider
carries it. The shim creates a **private `OSSL_LIB_CTX`**, loads
`default` (required) and `legacy` (best-effort) into it once per
process (under `pthread_once`), so the process's default context stays
untouched. The digest fetch then succeeds through whichever provider
supplies the algorithm. It surfaces a setup failure (no usable
context) as the empty `ByteArray`; the failed setup is not retried.

## Usage

```lean
import LeanHazmatRipemd160
open LeanHazmat.Ripemd160

def d20 : ByteArray := ripemd160 (String.toUTF8 "abc")
-- 8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

-- The precompile's 32-byte left-padded output encoding is the caller's step.
```

## API (namespace `LeanHazmat.Ripemd160`)

```lean
ripemd160 : ByteArray → ByteArray   -- 20-byte digest, any input length
```

## Trust boundary

No pure-Lean reference: the binding is an opaque `@[extern]` boundary
over OpenSSL, validated only against the published vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatRipemd160Tests    # the nine published vectors, incl. the million-`a` case
```

## Linking (for consumers)

libcrypto is a *system* library, and link arguments do not propagate
across `require` (packages/hazmat/docs/PLAN.md Stage 0). Any executable that
transitively links this family must supply the libcrypto flags itself
(`pkg-config --libs libcrypto`, or the hardcoded `-lcrypto` plus the
platform `-L` paths, as `EthCLSpecs` does). This package's own test
lib carries its own discovery. On a glibc older than 2.34 the shim's
`pthread_once` also needs `-lpthread` at link time (libc carries it on
2.34+, musl, and macOS); this package's own link adds the flag.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
