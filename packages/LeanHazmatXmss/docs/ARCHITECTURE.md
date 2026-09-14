# LeanHazmatXmss: Architecture

The single-family trust-boundary record for `LeanHazmatXmss`. The cross-family
view is
[`../../../hazmat-docs/ARCHITECTURE.md`](../../../hazmat-docs/ARCHITECTURE.md);
this file records *this* family's library, version pin, validation vectors, and
build shape.

## What this package is

FFI bindings for **RFC 8391 XMSS-SHA2** one-time, hash-based signatures. XMSS
is a stateful scheme: each secret key signs a fixed number of messages (`2^h`),
and every signature consumes a leaf index that must never be reused. The
surface (all in namespace `LeanHazmat.Xmss`):

| Primitive | C symbol | Result |
| --- | --- | --- |
| `paramSizes` | `lean_hazmat_xmss_param_sizes` | `some (pk, sig, sk)` sizes, or `none` |
| `keygenFromSeed` | `lean_hazmat_xmss_keygen_from_seed` | `pk ++ sk` |
| `sign` | `lean_hazmat_xmss_sign` | `sig ++ new_sk` |
| `verify` | `lean_hazmat_xmss_verify` | `Bool` |

Three parameter sets are recognized, all with n = 32 and Winternitz w = 16:

| Name | OID | h | pk | sig |
| --- | --- | --- | --- | --- |
| XMSS-SHA2_10_256 | `0x00000001` | 10 | 68 B | 2500 B |
| XMSS-SHA2_16_256 | `0x00000002` | 16 | 68 B | 2692 B |
| XMSS-SHA2_20_256 | `0x00000003` | 20 | 68 B | 2820 B |

`keygenFromSeed` takes the key material as an explicit `3·n`-byte seed rather
than drawing it from an RNG. That makes key generation a pure function of
`(oid, seed)`, which is what the reproducible KAT below needs and what makes
the `opaque` FFI declarations sound. Statefulness stays the caller's concern:
`sign` returns the updated secret key in its `new_sk` tail, and the caller must
thread it forward and never sign twice under the same index.

## Backend & pin

**XMSS/xmss-reference**, the reference implementation that accompanies RFC 8391,
**vendored** at commit **`171ccbd26f098542a67eb5d2b128281c80bd71a6`**
(2021-03-16). The project publishes no release tags, so the pin is a bare commit
hash. `just hazmat-xmss-vendor` does a shallow (`--depth 1`) fetch of that
commit into a gitignored `vendor/xmss-reference/`; the build is offline
thereafter. Never a git submodule (cross-family ARCHITECTURE.md §6).

xmss-reference describes itself as "intended for research, cross-validation, and
experimenting", and warns specifically against deploying stateful signature
schemes without careful state management. This package inherits that caveat: it
exists to bring an RFC 8391 oracle into the monorepo for cross-validation and
experiments, not to key production signing.

## Build shape

The lakefile compiles the **simple (non-BDS) core** as Lake `buildO` objects:
`hash.c`, `fips202.c`, `hash_address.c`, `params.c`, `utils.c`, `wots.c`,
`xmss_core.c`, `xmss_commons.c`, and the OID wrapper `xmss.c`, plus the shim
`csrc/xmss_shim.c`. `randombytes.c` is excluded. `hash.c` calls OpenSSL's
`SHA256()`, so the package links **libcrypto**, discovered through `pkg-config`
(with a Debian/Ubuntu fallback), the same pattern as `LeanHazmatSha256`. The ten
objects archive into one `extern_lib` (`libleanhazmat_xmss`).

The shim reaches keygen through `xmssmt_core_seed_keypair`, the seeded core
entry point, so it never calls `randombytes`. A **weak** `randombytes` stub
(reading `/dev/urandom`) remains only to satisfy the linker, since the compiled
`xmss_core.o` still references the symbol from the non-seeded path we do not
use. Weak linkage means a co-linked archive that defines `randombytes` wins,
avoiding a symbol collision.

## Trust boundary

XMSS has **no** kernel-reducible pure-Lean reference here: each binding is an
opaque `@[extern]` boundary. The single empirical trust assumption is **that
xmss-reference correctly implements RFC 8391 XMSS-SHA2**. It is validated only
by `LeanHazmatXmssTests`, and every case is a `native_decide` (one
`Lean.ofReduceBool` axiom per case), the acceptable regime for an FFI KAT.

## Validation vectors: pin

RFC 8391 ships **no official test vectors**, and there is no consensus-spec
suite to lift from (unlike `LeanHazmatBls`). The closest ground truth is
xmss-reference's own reference-vector generator, `test/vectors.c`, which runs a
fixed seed (`0x00, 0x01, …`) and prints `shake128(pk_core, 10)` and
`shake128(sig, 10)`. `LeanHazmatXmssTests/Vectors.lean` uses that same seed and
checks:

* the two upstream digests for oid 1, `7de72d192121f414d4bb` (public key) and
  `8b6cb278d50a3694ca38` (a signature at leaf index `2^(h-1) = 512` over the
  one-byte message `0x25`, upstream's exact setup),
* the buffer sizes `(68, 2500, 136)` from `paramSizes`,
* the full 68-byte public key and a signature prefix, in raw bytes,
* plus round-trip acceptance and tampered-input rejection.

Matching the two `test/vectors.c` digests is the key point: those values come
from upstream's own driver, a different top-level path than this FFI shim, so
agreement cross-validates keygen and sign (OID handling, seed threading, buffer
slicing), not merely that the shim is self-consistent.

The remaining caveat is honest: this cross-checks against *xmss-reference's
own* reference vectors, not an independent third party. It does not, on its
own, prove xmss-reference matches RFC 8391; that rests on the upstream
implementation's reputation and review. Any future access to official or
third-party KATs should be added here and this caveat narrowed further.
