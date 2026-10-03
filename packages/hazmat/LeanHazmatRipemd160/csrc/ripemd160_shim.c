// LeanHazmatRipemd160: C shim wrapping the system OpenSSL libcrypto
// for the execution-layer RIPEMD-160 precompile primitive (0x03).
//
// Where RIPEMD-160 lives changed across OpenSSL 3.x: 3.0.0-3.0.6 ship
// it only in the **legacy provider**; from 3.0.7 the **default**
// provider carries it. OpenSSL does not load the legacy provider by
// default, and an explicit provider load disables the automatic
// default-provider load for that context. Loading `legacy` into the
// *default* library context would break unrelated OpenSSL consumers
// in the same process. This shim therefore creates a **private**
// `OSSL_LIB_CTX`, loads `default` into it (required) and `legacy`
// best-effort (for the old 3.x releases), leaving the process's
// default context untouched; the digest fetch runs against the
// private context and answers whether any provider in it can supply
// the algorithm. The setup runs once (`pthread_once`, safe from
// any thread) and a failed setup is not retried; every entry point
// reports the empty ByteArray when no provider supplies RIPEMD-160.
//
// Digest path: `EVP_Q_digest` (the OpenSSL 3 one-shot API), fetching
// "RIPEMD-160" by name. Each call fetches the algorithm, negligible
// next to the digest itself.
//
// Every entry point the Lean side declares `@[extern]` lives here
// (LeanHazmatRipemd160/Ffi.lean). The input is borrowed
// (`b_lean_obj_arg` = `@&`); the digest is a freshly-allocated 20-byte
// `ByteArray`; an *empty* `ByteArray` is the error sentinel.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): the linked
// OpenSSL libcrypto implements RIPEMD-160 correctly. There is no
// pure-Lean reference; validated only against the published RIPEMD-160
// vectors (LeanHazmatRipemd160Tests), which exercise exactly this
// provider-loading path.

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <lean/lean.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/provider.h>
#include <pthread.h>

#define DIGEST_LEN 20  // RIPEMD-160 output

// The private library context, `default` required and `legacy`
// best-effort. Set up once from any thread by `ripemd_ctx_init` (under
// the pthread_once; a failed setup is not retried) and read-only
// afterwards. `NULL` means no usable context.
static OSSL_LIB_CTX *ctx_instance = NULL;

static void ripemd_ctx_init(void) {
    // Every OpenSSL call below queues errors on the *thread's* error
    // queue when it fails. Mark
    // before the first call and pop on every exit path, so the shim
    // removes exactly what it added; unlike a blanket ERR_clear_error,
    // any earlier unread errors on the queue survive.
    ERR_set_mark();
    ctx_instance = OSSL_LIB_CTX_new();
    if (ctx_instance == NULL ||
        OSSL_PROVIDER_load(ctx_instance, "default") == NULL) {
        // Without the default provider this context cannot fetch
        // anything reliably; leave the error sentinel in place.
        if (ctx_instance) {
            OSSL_LIB_CTX_free(ctx_instance);
            ctx_instance = NULL;
        }
        ERR_pop_to_mark();
        return;
    }
    // Best-effort: OpenSSL 3.0.0-3.0.6 keep RIPEMD-160 only in the
    // legacy provider; 3.0.7+ moved it into the default provider, so
    // a host without the legacy module still computes the digest.
    OSSL_PROVIDER_load(ctx_instance, "legacy");
    ERR_pop_to_mark();
}

static OSSL_LIB_CTX *ripemd_ctx(void) {
    // `pthread_once` resolves from libc on glibc 2.34 and later (and
    // on musl and macOS); on older glibc it lives in libpthread, so
    // the package's lakefile adds `-lpthread` to this package's own
    // test-lib link.
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, ripemd_ctx_init);
    return ctx_instance;
}

// Fresh Lean `ByteArray` of length `n` with `src` copied in.
static inline lean_obj_res mk_bytearray(const uint8_t *src, size_t n) {
    lean_object *arr = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(arr), src, n);
    return arr;
}

// The empty-ByteArray error sentinel.
static inline lean_obj_res mk_error(void) {
    return lean_alloc_sarray(1, 0, 0);
}

// ─────────────────────────────────────────────────────────────────────
// ripemd160 : ByteArray → ByteArray (20)
//   @[extern "lean_hazmat_ripemd160_hash"]
// 20-byte RIPEMD-160 digest of an arbitrary-length input. Returns the
// empty ByteArray if no provider supplies RIPEMD-160 or the digest
// fails.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_ripemd160_hash(
    b_lean_obj_arg in_arr)
{
    OSSL_LIB_CTX *ctx = ripemd_ctx();
    if (!ctx) return mk_error();

    const uint8_t *in = lean_sarray_cptr(in_arr);
    size_t in_len = lean_sarray_size(in_arr);

    // A failed digest fetch queues errors on the thread's error queue,
    // and precompile input reaches the failure path at will. A later
    // libcrypto consumer on this thread must not read our stale
    // entries. Mark / pop removes exactly what
    // this call added, leaving any earlier unread errors alone. The
    // context lookup queues nothing, so it stays before the mark.
    ERR_set_mark();
    uint8_t out[DIGEST_LEN];
    size_t out_len = sizeof(out);
    int ok = EVP_Q_digest(ctx, "RIPEMD-160", NULL, in, in_len,
                          out, &out_len) == 1 && out_len == DIGEST_LEN;
    ERR_pop_to_mark();
    if (!ok) return mk_error();
    return mk_bytearray(out, DIGEST_LEN);
}
