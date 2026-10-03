# LeanHazmatRipemd160: Architecture

The single-family trust-boundary record for `LeanHazmatRipemd160`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md).

## What this package is

RIPEMD-160 in namespace `LeanHazmat.Ripemd160`:

| Primitive | C symbol |
| --- | --- |
| `ripemd160` | `lean_hazmat_ripemd160_hash` |

20-byte digest of an arbitrary-length input. The precompile's 32-byte
left-padded output encoding is the caller's composition.

## Backend

The system OpenSSL `libcrypto`, no vendoring. Discovery via
`pkg-config` exactly as in `LeanHazmatSha256` (the helpers are
duplicated per §3.3, with the explicit `-L<libdir>` that Lean's `lld`
needs).

**The provider story is the one gotcha** (the plan's open item):
OpenSSL 3.0.0-3.0.6 keep RIPEMD-160 in the legacy provider only, and
loading `legacy` into the process's *default* context would disable the
automatic default-provider load for the whole process. The shim
therefore creates a **private `OSSL_LIB_CTX`**, loads `default`
(required) and `legacy` (best-effort, for the old releases) into it
once (`pthread_once`; a failed setup is not retried), and fetches
"RIPEMD-160" against that context with `EVP_Q_digest` (the OpenSSL 3
one-shot API), which succeeds through whichever provider supplies the
algorithm. Every entry point returns the empty
`ByteArray` when no provider supplies the algorithm.

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary. The empirical trust assumption is *that the linked OpenSSL
libcrypto implements RIPEMD-160 correctly, through whichever provider
supplies it*, every KAT exercises exactly that fetching path. Validated
by `LeanHazmatRipemd160Tests` against the nine published RIPEMD-160
vectors (empty, `"a"`, `"abc"`, `"message digest"`, the two standard
padded strings, the alphabet, `8 × "1234567890"`, and the million-`a`
case), cross-checked against `openssl dgst -rmd160` at authoring time
and hard-coded into `LeanHazmatRipemd160Tests/Vectors.lean`, keeping
the build hermetic.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT.
