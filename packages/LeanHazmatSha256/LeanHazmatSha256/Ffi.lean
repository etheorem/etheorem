/-!
# `LeanHazmatSha256.Ffi`: OpenSSL SHA-256 behind `@[extern]`

Three `@[extern] opaque` declarations bridge Lean's `ByteArray` to
the C shims in `csrc/sha256_shim.c` and `csrc/sha256_batch.c`, which
wrap OpenSSL's `EVP_*` API. They are the *raw primitive* surface of
the LeanHazmat SHA-256 family: a single-input digest, a two-input
concatenation digest (the inner SSZ Merkle step), and a level-batched
form of the latter.

This module deliberately holds **only** the FFI bindings. The
abstract `Hasher` typeclass, the `Sha256` tag, the `Hasher Sha256`
instance, and the FFI ≡ pure-Lean *equivalence axioms* all live in
`SizzLean`, the one layer entitled to import both this package and
the pure-Lean spec `LeanSha256` (see hazmat-docs/ARCHITECTURE.md §9).
Keeping the bindings free of any spec reference is what lets this
package ship standalone as a mirror, validated only by its own
byte-level KAT.

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatSha256`); the
declaration names live under the *brand* namespace `LeanHazmat.Sha256`
(`LeanHazmat.Sha256.sha256Hash`, …). The two are decoupled exactly as
SizzLean decouples the file path `SizzLean/Hasher/Sha256.lean` from
its `SizzLean.Hasher` namespace (ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

`opaque` keeps the kernel from attempting to reduce hash
computations during proof checking; `@[extern]` instructs the
compiler to emit a direct call to the named C symbol at runtime. The
trust assumption, *that the linked OpenSSL implements NIST FIPS
180-4 SHA-256*, is validated empirically by the CAVP byte-level KAT
in `LeanHazmatSha256Tests/`, and is the single line item this family
contributes to the TCB. Unlike every other LeanHazmat family,
SHA-256 *also* has a kernel-reducible pure-Lean reference
(`LeanSha256`); SizzLean ties the two together with named, auditable
equivalence axioms so a future `@[csimp]`-proved equality can retire
the empirical assertion in one place.

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*, Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these.
-/

set_option autoImplicit false

namespace LeanHazmat.Sha256

/-- 32-byte SHA-256 digest of an arbitrary-length input. Runtime
implementation is `csrc/sha256_shim.c`'s `lean_hazmat_sha256_hash`,
which wraps OpenSSL's `EVP_*` digest API.

The result is *always* 32 bytes (NIST FIPS 180-4 SHA-256 output
length); callers may rely on this as a documentation contract
enforced by the C shim, not by Lean's type system.

**Trust assumption:** the linked OpenSSL `libcrypto` computes NIST
FIPS 180-4 SHA-256. Validated by the byte-level CAVP KAT in
`LeanHazmatSha256Tests/Cavp.lean`. -/
@[extern "lean_hazmat_sha256_hash"]
opaque sha256Hash (input : @& ByteArray) : ByteArray

/-- 32-byte SHA-256 digest of `left ++ right` (concatenation),
without materialising the concatenation. Runtime implementation is
`csrc/sha256_shim.c`'s `lean_hazmat_sha256_combine`.

Pulled out as its own primitive (rather than
`sha256Hash (left ++ right)`) so production instances can dispatch
directly to a SHA-NI / AVX-512 two-block hashing primitive without a
redundant copy at every interior Merkle node. The OpenSSL backend
just calls `EVP_DigestUpdate` twice, but the abstraction is shaped
for the eventual `gohashtree`-style upgrade.

**Trust assumption:** same as `sha256Hash`. Validated by the
`combine` cases in `LeanHazmatSha256Tests/Vectors.lean`. -/
@[extern "lean_hazmat_sha256_combine"]
opaque sha256Combine (left right : @& ByteArray) : ByteArray

/-- Batched FFI SHA-256 sibling combine. Inputs are parallel arrays,
`lefts[i]` and `rights[i]` are the i-th sibling pair, and the output
array has the same length, with `output[i] = SHA-256(lefts[i] ++
rights[i])`. The C shim panics if the input lengths disagree.

Runtime implementation is `csrc/sha256_batch.c`'s
`lean_hazmat_sha256_batch_combine`, currently a scalar loop sharing
one `EVP_MD_CTX` across the pairs, swappable for SHA-NI / AVX-512
later without changing the FFI surface. Amortising the context
allocation across the whole pair array is the win over calling
`sha256Combine` in a Lean-level loop.

**Trust assumption:** same as `sha256Combine`. Pointwise agreement
with the pure-Lean reference is asserted by SizzLean's
`sha256BatchCombine_eq_spec` axiom and validated by
`SizzLeanTests/Sha256BatchEquivalence.lean`; the self-contained
known-answer cases live in `LeanHazmatSha256Tests/Vectors.lean`. -/
@[extern "lean_hazmat_sha256_batch_combine"]
opaque sha256BatchCombine
    (lefts : @& Array ByteArray) (rights : @& Array ByteArray) :
    Array ByteArray

end LeanHazmat.Sha256
