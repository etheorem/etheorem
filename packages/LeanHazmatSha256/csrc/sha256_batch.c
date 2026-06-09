// LeanHazmatSha256: C shim for batched SHA-256 sibling-pair hashing.
//
// Exposes one symbol that the Lean side declares as `@[extern]`
// (see `LeanHazmatSha256/Ffi.lean`):
//
//   * lean_hazmat_sha256_batch_combine(lefts, rights): given two
//     equal-length arrays of 32-byte `ByteArray`s, return an
//     equal-length array of 32-byte digests where output[i] =
//     SHA-256(left[i] ++ right[i]).
//
// This is the level-batched form of `lean_hazmat_sha256_combine`:
// the user collects every sibling pair at one Merkle-tree level,
// passes them all in one call, gets the hashes back. The first-
// cut implementation is a plain loop over `EVP_DigestUpdate`-twice
// (no SIMD); the SHA-NI / AVX-512 hand-tuned path is a documented
// follow-up that swaps the inner loop without changing the FFI
// surface.
//
// Trust assumption: same as `sha256_shim.c`, the linked OpenSSL
// implements NIST FIPS 180-4 SHA-256 correctly. Pointwise
// agreement with the pure-Lean reference (`LeanSha256.combine`) is
// asserted by the `sha256BatchCombine_eq_spec` axiom in SizzLean and
// validated empirically by `SizzLeanTests/Sha256BatchEquivalence.lean`
// (the one cross-check that needs both this package and LeanSha256).
//
// Input contract: `lefts` and `rights` are equal-length arrays of
// `ByteArray`. Each individual `ByteArray` is treated as a byte
// run (no required size); the caller is responsible for ensuring
// 32-byte siblings if SSZ Merkle semantics are intended.
//
// Output contract: the returned array has the same length as the
// inputs; element [i] is a freshly-allocated 32-byte `ByteArray`.

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <openssl/evp.h>
#include <lean/lean.h>

// Mirrors the digest-length constant in `sha256_shim.c`.
#define LEAN_HAZMAT_SHA256_DIGEST_LEN 32

// One scalar pair-combine, sharing the EVP context across the
// per-pair calls so we don't pay context allocation per pair.
// Returns 1 on success, 0 on failure.
static int lean_hazmat_sha256_combine_into(
    EVP_MD_CTX *ctx,
    const uint8_t *lp, size_t ln,
    const uint8_t *rp, size_t rn,
    uint8_t out[LEAN_HAZMAT_SHA256_DIGEST_LEN])
{
    return EVP_DigestInit_ex(ctx, EVP_sha256(), NULL)
        && EVP_DigestUpdate(ctx, lp, ln)
        && EVP_DigestUpdate(ctx, rp, rn)
        && EVP_DigestFinal_ex(ctx, out, NULL);
}

// Batched two-input combine. Iterates over the parallel `lefts` /
// `rights` arrays, producing a freshly-allocated output array of
// 32-byte digests in matching order.
LEAN_EXPORT lean_obj_res lean_hazmat_sha256_batch_combine(
    b_lean_obj_arg lefts, b_lean_obj_arg rights)
{
    const size_t n_left  = lean_array_size(lefts);
    const size_t n_right = lean_array_size(rights);

    if (n_left != n_right) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: lefts/rights length mismatch");
    }

    // Allocate output array of length `n_left`. `lean_alloc_array`
    // initialises every slot to a boxed `0` placeholder; we
    // overwrite each before returning.
    lean_object *out = lean_alloc_array(n_left, n_left);

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    if (!ctx) {
        lean_internal_panic("LeanHazmatSha256: EVP_MD_CTX_new failed");
    }

    for (size_t i = 0; i < n_left; i++) {
        // Borrow the i-th element of each input, no refcount bump.
        // The arrays own these for the duration of this call.
        lean_object *left  = lean_array_get_core(lefts,  i);
        lean_object *right = lean_array_get_core(rights, i);

        const size_t ln = lean_sarray_size(left);
        const size_t rn = lean_sarray_size(right);
        const uint8_t *lp = (const uint8_t *)lean_sarray_cptr(left);
        const uint8_t *rp = (const uint8_t *)lean_sarray_cptr(right);

        lean_object *digest = lean_alloc_sarray(
            1, LEAN_HAZMAT_SHA256_DIGEST_LEN, LEAN_HAZMAT_SHA256_DIGEST_LEN);

        if (!lean_hazmat_sha256_combine_into(
                ctx, lp, ln, rp, rn,
                (uint8_t *)lean_sarray_cptr(digest))) {
            EVP_MD_CTX_free(ctx);
            lean_internal_panic(
                "LeanHazmatSha256: sha256BatchCombine: EVP combine failed");
        }

        // Write into the output array. `lean_array_set_core`
        // does not bump the refcount of `digest`; we own it
        // (fresh allocation just above) and transfer ownership
        // to the array slot.
        lean_array_set_core(out, i, digest);
    }

    EVP_MD_CTX_free(ctx);
    return out;
}
