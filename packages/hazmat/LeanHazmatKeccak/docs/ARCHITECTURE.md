# LeanHazmatKeccak: Architecture

The single-family trust-boundary record for `LeanHazmatKeccak`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md);
this file records *this* family's library, rev pin, build shape, and
validation vectors.

## What this package is

Keccak-256 (rate 136, original `0x01` padding) in namespace
`LeanHazmat.Keccak`:

| Primitive | C symbol |
| --- | --- |
| `keccak256` | `lean_hazmat_keccak256_hash` |

The raw digest only; address derivation (`keccak256(pk)[12:32]`) and
every other composition stay with the caller.

## Backend & pin

**coruus/keccak-tiny**, the plan's "small single-file vetted keccak"
branch (David Leon Gil, CC0, ~160 lines, widely reused). Upstream tags
no releases, so the pin is the commit **rev
`64b6647514212b76ae7bca0dea9b7b197d1d8186`**: `just
hazmat-keccak-vendor` fetches exactly that rev (GitHub fetch-by-SHA)
and checks it back. Bumping the pin means re-checking the KAT.

## Build shape

One object. The vendored file's sponge is `static`, so the shim
translation unit `#include`s `keccak-tiny.c` **unmodified** and calls
its generic `hash(out, outlen, in, inlen, rate, delim)` with rate 136
and delimiter `0x01`. Two details recorded in the shim:

* The vendored file's *content* is folded into the target's trace
  explicitly (a `#include` is invisible to a single-input trace), so a
  re-vendor rebuilds.
* keccak-tiny calls C11 Annex K `memset_s`, which glibc does not
  provide; the shim maps it to `memset` by macro before the include
  (semantically sufficient for the scratch-state clear).

The result archives into `libleanhazmat_keccak` (shim + implementation
in one object), which propagates to dependents like every family.

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary. The empirical trust assumption is *that the vendored
keccak-tiny implements Keccak-f[1600] and the sponge correctly, and
that the shim selects the 0x01 padding*. Validated only by
`LeanHazmatKeccakTests`:

* **EVM canonical constants**: `keccak256 ""` = `c5d246…a470` and the
  empty trie root `keccak256 0x80` = `56e81f…b421`. A wrong padding
  byte fails these immediately.
* **Published vectors**: short strings, the 136-byte one-block
  boundary, a multi-block input, 36 zero bytes.
* **Consumer-side composition**: the EIP-155 example's address
  derivation, documented as the caller's composition.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT.

## Validation vectors: pin

The Keccak-256 constants above are stable published values
(cross-checked at authoring time against an independent pure-Python
Keccak implementation, which also reproduced the EIP-155 sender
address from the EIP's published private key).
