// LeanHazmatSha256: C shim for batched SHA-256 sibling-pair hashing.
//
// Exposes one symbol that the Lean side declares as `@[extern]`
// (see `LeanHazmatSha256/Ffi.lean`):
//
//   * lean_hazmat_sha256_batch_combine(lefts, rights): given two
//     equal-length arrays of `ByteArray`s, return an equal-length
//     array of 32-byte digests where output[i] =
//     SHA-256(left[i] ++ right[i]).
//
// This is the level-batched form of `lean_hazmat_sha256_combine`:
// the caller collects every sibling pair at one Merkle-tree level,
// passes them all in one call, and gets the digests back in order.
//
// Two backends sit behind the one symbol. `lakefile.lean` decides per
// build host whether the second one is compiled in and tells this
// file through a single define, so the C side and the archive
// contents cannot disagree:
//
//   * The OpenSSL EVP loop, always compiled: two `EVP_DigestUpdate`
//     calls per pair on one shared context. On ARMv8 CPUs with the
//     SHA extensions OpenSSL already uses the hardware instructions,
//     so this loop is hardware-accelerated single-stream; the batch
//     amortises the per-call overhead. It is the only backend on
//     ARM64, macOS, and every other host.
//   * With `LEAN_HAZMAT_SHA256_ISAL` defined (x86_64 Linux): Intel
//     ISA-L crypto's `sha256_mb` multi-buffer engine. It hashes
//     4 (SSE) / 8 (AVX2) / 16 (AVX-512) buffers in lock-step, or two
//     streams on SHA-NI parts, and picks the widest path the CPU
//     supports at run time through CPUID. ISA-L is vendored and
//     compiled into this package's archive, so no system library is
//     added. It takes every non-empty batch: with the manager's
//     scratch kept per thread, even a single pair runs faster through
//     ISA-L than through a fresh EVP context.
//
// Trust assumption: the linked backend implements NIST FIPS 180-4
// SHA-256 correctly. Pointwise agreement with the pure-Lean reference
// (`LeanSha256.combine`) is asserted by the `sha256BatchCombine_eq_spec`
// axiom in SizzLean and validated empirically by
// `SizzLeanTests/Sha256BatchEquivalence.lean` on whichever backend the
// build host compiled in.
//
// Input contract: `lefts` and `rights` are equal-length arrays of
// `ByteArray`. Each `ByteArray` is a byte run of any size; the caller
// supplies 32-byte siblings when SSZ Merkle semantics are intended.
//
// Output contract: the returned array has the same length as the
// inputs; element [i] is a freshly-allocated 32-byte `ByteArray`.

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/evp.h>
#include <lean/lean.h>

// Mirrors the digest-length constant in `sha256_shim.c`.
#define LEAN_HAZMAT_SHA256_DIGEST_LEN 32

// ---------------------------------------------------------------------
// OpenSSL EVP backend.
// ---------------------------------------------------------------------

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

// Hash all `n` pairs one after another and fill `out`.
static void lean_hazmat_sha256_batch_evp(
    b_lean_obj_arg lefts, b_lean_obj_arg rights, size_t n, lean_object *out)
{
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    if (!ctx) {
        lean_internal_panic("LeanHazmatSha256: EVP_MD_CTX_new failed");
    }

    for (size_t i = 0; i < n; i++) {
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

        // `lean_array_set_core` does not bump the refcount of `digest`;
        // we own it (fresh allocation just above) and transfer
        // ownership to the array slot.
        lean_array_set_core(out, i, digest);
    }

    EVP_MD_CTX_free(ctx);
}

#ifdef LEAN_HAZMAT_SHA256_ISAL

// ---------------------------------------------------------------------
// ISA-L multi-buffer backend (x86_64 Linux).
//
// ISA-L's `sha256_mb` is a job manager, not init/update/final. Each
// job hashes one contiguous buffer, so a pair is first copied into a
// lane buffer as `left ++ right`. Jobs are submitted with
// `ISAL_HASH_ENTIRE`, which makes ISA-L do the padding and the final
// block itself. `submit` hands back a finished job whenever a lane
// group completes; `flush` drains the rest. Each finished job carries
// the pair index in `user_data`, which is how a digest finds its
// output slot.
//
// Pairs are processed in chunks of `LEAN_HAZMAT_SHA256_ISAL_CHUNK`
// jobs so the scratch memory (one context plus one lane buffer per
// in-flight job) stays bounded no matter how long the input is. The
// only cost is one drain per chunk, and 256 jobs fill the widest
// (16-lane) engine sixteen times over before each drain.
//
// The scratch is allocated once per thread and kept. Lean runs tasks
// on a pool of threads, and a `_Thread_local` pointer gives each of
// them its own manager without a lock and without per-call
// allocation. Every error path ends in `lean_internal_panic`, which
// does not return, so nothing is freed on those paths.
// ---------------------------------------------------------------------

#include <isa-l_crypto/sha256_mb.h>

#define LEAN_HAZMAT_SHA256_ISAL_CHUNK 256
// A 32-byte sibling pair concatenates into one 64-byte SHA-256 block;
// the fixed lane buffer covers that case without a heap allocation.
#define LEAN_HAZMAT_SHA256_ISAL_LANE_BYTES 64
// ISA-L asks for 16-byte aligned contexts and uses 64-byte aligned
// digest storage inside them; 64 satisfies every field.
#define LEAN_HAZMAT_SHA256_ISAL_ALIGN 64

typedef struct {
    ISAL_SHA256_HASH_CTX_MGR *mgr;
    ISAL_SHA256_HASH_CTX *ctxs;                           // CHUNK contexts
    uint8_t (*lanes)[LEAN_HAZMAT_SHA256_ISAL_LANE_BYTES]; // CHUNK lane buffers
    uint8_t *heap[LEAN_HAZMAT_SHA256_ISAL_CHUNK];         // over-long pairs, else NULL
} lean_hazmat_isal_scratch;

static _Thread_local lean_hazmat_isal_scratch *lean_hazmat_isal_tls = NULL;

// `aligned_alloc` requires the size to be a multiple of the alignment.
static void *lean_hazmat_isal_alloc(size_t size)
{
    const size_t a = LEAN_HAZMAT_SHA256_ISAL_ALIGN;
    void *p = aligned_alloc(a, (size + a - 1) / a * a);
    if (!p) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: out of memory (ISA-L scratch)");
    }
    return p;
}

// This thread's scratch, allocated on first use.
static lean_hazmat_isal_scratch *lean_hazmat_isal_scratch_get(void)
{
    lean_hazmat_isal_scratch *s = lean_hazmat_isal_tls;
    if (s) return s;

    s = malloc(sizeof(*s));
    if (!s) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: out of memory (ISA-L scratch)");
    }
    s->mgr   = lean_hazmat_isal_alloc(sizeof(*s->mgr));
    s->ctxs  = lean_hazmat_isal_alloc(
        sizeof(*s->ctxs) * LEAN_HAZMAT_SHA256_ISAL_CHUNK);
    s->lanes = lean_hazmat_isal_alloc(
        LEAN_HAZMAT_SHA256_ISAL_LANE_BYTES * LEAN_HAZMAT_SHA256_ISAL_CHUNK);
    memset(s->heap, 0, sizeof(s->heap));

    lean_hazmat_isal_tls = s;
    return s;
}

// SHA-256 output bytes are the big-endian serialisation of the eight
// state words. ISA-L leaves the words in host order in
// `result_digest`, so each word is stored byte by byte here.
static void lean_hazmat_store_be32(uint8_t *out, uint32_t w)
{
    out[0] = (uint8_t)(w >> 24);
    out[1] = (uint8_t)(w >> 16);
    out[2] = (uint8_t)(w >> 8);
    out[3] = (uint8_t)(w);
}

// A job came back from `submit` or `flush`: check it, serialise its
// digest into a fresh `ByteArray`, and drop that into the output slot
// the job's `user_data` names.
static void lean_hazmat_isal_collect(ISAL_SHA256_HASH_CTX *done, lean_object *out)
{
    if (done->status != ISAL_HASH_CTX_STS_COMPLETE
        || done->error != ISAL_HASH_CTX_ERROR_NONE) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: ISA-L job did not complete");
    }

    const size_t i = (size_t)(uintptr_t)done->user_data;
    lean_object *digest = lean_alloc_sarray(
        1, LEAN_HAZMAT_SHA256_DIGEST_LEN, LEAN_HAZMAT_SHA256_DIGEST_LEN);
    uint8_t *dp = (uint8_t *)lean_sarray_cptr(digest);
    for (int w = 0; w < ISAL_SHA256_DIGEST_NWORDS; w++) {
        lean_hazmat_store_be32(dp + 4 * w, done->job.result_digest[w]);
    }

    // `lean_array_set_core` does not bump the refcount of `digest`; we
    // own it (fresh allocation just above) and transfer ownership to
    // the array slot.
    lean_array_set_core(out, i, digest);
}

// Hash pairs [start, start + count) through the manager and collect
// every digest into `out`.
static void lean_hazmat_isal_chunk(
    lean_hazmat_isal_scratch *s,
    b_lean_obj_arg lefts, b_lean_obj_arg rights,
    size_t start, size_t count, lean_object *out)
{
    ISAL_SHA256_HASH_CTX *done = NULL;

    if (isal_sha256_ctx_mgr_init(s->mgr) != 0) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: isal_sha256_ctx_mgr_init failed");
    }

    for (size_t j = 0; j < count; j++) {
        const size_t i = start + j;

        // Borrow the i-th element of each input, no refcount bump.
        // The arrays own these for the duration of this call.
        lean_object *left  = lean_array_get_core(lefts,  i);
        lean_object *right = lean_array_get_core(rights, i);

        const size_t ln = lean_sarray_size(left);
        const size_t rn = lean_sarray_size(right);
        const size_t total = ln + rn;
        if (total > UINT32_MAX) {
            lean_internal_panic(
                "LeanHazmatSha256: sha256BatchCombine: pair exceeds 4 GiB");
        }

        // Concatenate `left ++ right` into one contiguous buffer. The
        // fixed lane buffer covers 32-byte siblings; anything longer
        // takes a heap buffer that lives until the chunk is drained.
        uint8_t *buf = s->lanes[j];
        if (total > LEAN_HAZMAT_SHA256_ISAL_LANE_BYTES) {
            buf = malloc(total);
            if (!buf) {
                lean_internal_panic(
                    "LeanHazmatSha256: sha256BatchCombine: out of memory (pair buffer)");
            }
            s->heap[j] = buf;
        }
        memcpy(buf,      lean_sarray_cptr(left),  ln);
        memcpy(buf + ln, lean_sarray_cptr(right), rn);

        ISAL_SHA256_HASH_CTX *ctx = &s->ctxs[j];
        isal_hash_ctx_init(ctx);
        ctx->user_data = (void *)(uintptr_t)i;

        // ISA-L keeps the buffer pointer, not a copy: `buf` stays
        // alive until the drain below.
        if (isal_sha256_ctx_mgr_submit(
                s->mgr, ctx, &done, buf, (uint32_t)total, ISAL_HASH_ENTIRE) != 0) {
            lean_internal_panic(
                "LeanHazmatSha256: sha256BatchCombine: isal_sha256_ctx_mgr_submit failed");
        }
        if (done) {
            lean_hazmat_isal_collect(done, out);
        }
    }

    // Drain: `flush` returns one finished job per call and NULL once
    // the manager is empty.
    for (;;) {
        if (isal_sha256_ctx_mgr_flush(s->mgr, &done) != 0) {
            lean_internal_panic(
                "LeanHazmatSha256: sha256BatchCombine: isal_sha256_ctx_mgr_flush failed");
        }
        if (!done) break;
        lean_hazmat_isal_collect(done, out);
    }

    for (size_t j = 0; j < count; j++) {
        free(s->heap[j]);
        s->heap[j] = NULL;
    }
}

static void lean_hazmat_sha256_batch_isal(
    b_lean_obj_arg lefts, b_lean_obj_arg rights, size_t n, lean_object *out)
{
    lean_hazmat_isal_scratch *s = lean_hazmat_isal_scratch_get();

    for (size_t start = 0; start < n; start += LEAN_HAZMAT_SHA256_ISAL_CHUNK) {
        const size_t rest  = n - start;
        const size_t count = rest < LEAN_HAZMAT_SHA256_ISAL_CHUNK
                               ? rest : LEAN_HAZMAT_SHA256_ISAL_CHUNK;
        lean_hazmat_isal_chunk(s, lefts, rights, start, count, out);
    }
}

#endif /* LEAN_HAZMAT_SHA256_ISAL */

// ---------------------------------------------------------------------
// The exported entry point: shape check, output allocation, dispatch.
// ---------------------------------------------------------------------

LEAN_EXPORT lean_obj_res lean_hazmat_sha256_batch_combine(
    b_lean_obj_arg lefts, b_lean_obj_arg rights)
{
    const size_t n_left  = lean_array_size(lefts);
    const size_t n_right = lean_array_size(rights);

    if (n_left != n_right) {
        lean_internal_panic(
            "LeanHazmatSha256: sha256BatchCombine: lefts/rights length mismatch");
    }

    // `lean_alloc_array` fills every slot with a boxed `0` placeholder;
    // the backend overwrites each slot before returning.
    lean_object *out = lean_alloc_array(n_left, n_left);

#ifdef LEAN_HAZMAT_SHA256_ISAL
    lean_hazmat_sha256_batch_isal(lefts, rights, n_left, out);
#else
    lean_hazmat_sha256_batch_evp(lefts, rights, n_left, out);
#endif
    return out;
}
