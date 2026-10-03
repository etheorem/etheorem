// LeanHazmatP256: C shim wrapping the system OpenSSL libcrypto for
// the execution-layer P256VERIFY precompile primitive (EIP-7951,
// NIST P-256 / secp256r1 ECDSA verification).
//
// The primitive is raw verification over fixed-width big-endian
// fields:
//   p256Verify(msgHash(32), r(32), s(32), qx(32), qy(32)) → Bool
// OpenSSL 3.x provider API, no deprecated `EC_KEY` / `ECDSA_*` calls:
//   * the public key is imported with `EVP_PKEY_fromdata` from the
//     group name plus the uncompressed `0x04 ‖ x ‖ y` point; the
//     import is the validator (coordinates ≥ p and points off the
//     curve fail there, which is the EIP's key-admissibility rule).
//   * the raw `(r, s)` pair is DER-encoded by hand as an
//     ECDSA-Sig-Value (RFC 5480) and verified with `EVP_PKEY_verify`:
//     the data is the already-computed hash. This is the documented
//     EVP equivalent of the legacy `ECDSA_verify`, so the semantics
//     match: high-s signatures verify (no
//     anti-malleability policy; EIP-7951 verifies exactly the ECDSA
//     equation and its own test suite includes a malleability case
//     marked valid), and r or s = 0 fails.
//
// Per packages/hazmat/docs/ARCHITECTURE.md §4, everything around the
// verification is the caller's job: the 160-byte input layout
// (hash ‖ r ‖ s ‖ x ‖ y), the gas schedule, and the `0x…01` success
// encoding. The primitive answers `Bool`.
//
// Library context: like `ripemd160_shim.c`, this shim fetches against
// a **private** `OSSL_LIB_CTX` with `default` loaded, set up once
// (`pthread_once`, safe from any thread). An explicit provider load
// elsewhere in the process disables the automatic default-provider
// load for the process's default context. Against that context, every
// fetch (key import, verify) would fail and every signature would
// read as invalid, with no error channel on a `Bool`. The private
// context pins our providers and leaves the process's default
// context untouched. A context-setup failure (allocation failure
// only) is reported as `false`, like every other failure; it is not
// retried, matching `ripemd160_shim.c`.
//
// All failures collapse to `false`, never a panic.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): the linked
// OpenSSL libcrypto implements NIST P-256 ECDSA verification
// correctly. There is no pure-Lean reference; validated only against
// the official EIP-7951 vectors (Project Wycheproof, via the EIP's
// test-vectors.json) in LeanHazmatP256Tests.

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <lean/lean.h>
#include <openssl/core_names.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <openssl/provider.h>
#include <pthread.h>

#define FIELD_LEN 32  // hash, r, s, x, y: all 32-byte big-endian

// The private library context. Set up once from any thread by
// `p256_ctx_init` (under the pthread_once; a failed setup is not
// retried) and read-only afterwards. `NULL` means no usable context.
static OSSL_LIB_CTX *ctx_instance = NULL;

static void p256_ctx_init(void) {
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
    ERR_pop_to_mark();
}

static OSSL_LIB_CTX *p256_ctx(void) {
    // `pthread_once` resolves from libc on glibc 2.34 and later (and
    // on musl and macOS); the package's lakefile adds `-lpthread` to
    // its own test-lib link so an older glibc links standalone too.
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, p256_ctx_init);
    return ctx_instance;
}

// One DER INTEGER from a big-endian string: strip leading zeros, add
// a 0x00 sign byte when the top bit of the first byte is set, and
// collapse a value that strips to nothing to the single byte 0x00.
// Writes at most `n + 1` bytes into `out`; returns the length.
static size_t der_int(const uint8_t *in, size_t n, uint8_t *out) {
    size_t start = 0;
    while (start < n && in[start] == 0) start++;
    size_t len = n - start;
    size_t off = 0;
    if (len == 0) {
        out[off++] = 0x00;
    } else {
        if (in[start] & 0x80) out[off++] = 0x00;
        memcpy(out + off, in + start, len);
        off += len;
    }
    return off;
}

// DER-encode the two 32-byte big-endian scalars as an ECDSA-Sig-Value
// (RFC 5480): SEQUENCE { INTEGER r, INTEGER s }. Short-form lengths
// throughout (the body is at most 72 bytes). Writes at most 72 bytes
// into `der`; returns the total length.
static size_t der_sig(const uint8_t *r, const uint8_t *s, uint8_t *der) {
    uint8_t ri[FIELD_LEN + 1], si[FIELD_LEN + 1];
    size_t rn = der_int(r, FIELD_LEN, ri);
    size_t sn = der_int(s, FIELD_LEN, si);
    size_t off = 0;
    der[off++] = 0x30;
    der[off++] = (uint8_t)(4 + rn + sn);
    der[off++] = 0x02;
    der[off++] = (uint8_t)rn;
    memcpy(der + off, ri, rn);
    off += rn;
    der[off++] = 0x02;
    der[off++] = (uint8_t)sn;
    memcpy(der + off, si, sn);
    off += sn;
    return off;
}

// ─────────────────────────────────────────────────────────────────────
// p256Verify : msgHash(32) → r(32) → s(32) → qx(32) → qy(32) → Bool
//   @[extern "lean_hazmat_p256_verify"]
// Verify a P-256 ECDSA signature over a 32-byte hash. Any malformed
// input or failed verification is `false`.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_p256_verify(
    b_lean_obj_arg msg_arr, b_lean_obj_arg r_arr, b_lean_obj_arg s_arr,
    b_lean_obj_arg qx_arr, b_lean_obj_arg qy_arr)
{
    if (lean_sarray_size(msg_arr) != FIELD_LEN) return 0;
    if (lean_sarray_size(r_arr)   != FIELD_LEN) return 0;
    if (lean_sarray_size(s_arr)   != FIELD_LEN) return 0;
    if (lean_sarray_size(qx_arr)  != FIELD_LEN) return 0;
    if (lean_sarray_size(qy_arr)  != FIELD_LEN) return 0;

    // Every OpenSSL call below can queue an error on the *thread's*
    // error queue when it fails: a key that fails the
    // `EVP_PKEY_fromdata` import, a failed verification, an allocation
    // failure. Precompile input reaches those paths at will, and a
    // later libcrypto consumer on this thread must not read our stale
    // entries. Mark / pop removes exactly what this call added,
    // leaving any earlier unread errors alone. The length guards
    // above and the context lookup queue nothing on this thread's
    // queue, so they stay before the mark.
    OSSL_LIB_CTX *ctx = p256_ctx();
    if (!ctx) return 0;
    ERR_set_mark();

    uint8_t ok = 0;

    // Rebuild the uncompressed point the provider's importer wants.
    uint8_t pub65[65];
    pub65[0] = 0x04;
    memcpy(pub65 + 1, lean_sarray_cptr(qx_arr), FIELD_LEN);
    memcpy(pub65 + 1 + FIELD_LEN, lean_sarray_cptr(qy_arr), FIELD_LEN);

    // Import the key through the provider API: the named group plus
    // the encoded point. The import validates; an out-of-range or
    // off-curve point fails here and everything below is skipped.
    // The fetch runs against the private context (see the header
    // note), never the process's default context.
    char group[] = "prime256v1";
    OSSL_PARAM params[3];
    params[0] = OSSL_PARAM_construct_utf8_string(
        OSSL_PKEY_PARAM_GROUP_NAME, group, 0);
    params[1] = OSSL_PARAM_construct_octet_string(
        OSSL_PKEY_PARAM_PUB_KEY, pub65, sizeof(pub65));
    params[2] = OSSL_PARAM_construct_end();

    EVP_PKEY_CTX *kctx = EVP_PKEY_CTX_new_from_name(ctx, "EC", NULL);
    EVP_PKEY *pkey = NULL;
    if (kctx &&
        EVP_PKEY_fromdata_init(kctx) == 1 &&
        EVP_PKEY_fromdata(kctx, &pkey, EVP_PKEY_PUBLIC_KEY, params) == 1) {
        // The provider verifies a DER ECDSA-Sig-Value, so the raw
        // `(r, s)` pair becomes one here.
        uint8_t der[72];
        size_t der_len =
            der_sig(lean_sarray_cptr(r_arr), lean_sarray_cptr(s_arr), der);

        // `EVP_PKEY_verify` takes the already-computed 32-byte digest.
        // The verify context inherits the key's private library
        // context (created from the key, the OpenSSL 3 form).
        EVP_PKEY_CTX *vctx = EVP_PKEY_CTX_new_from_pkey(ctx, pkey, NULL);
        if (vctx && EVP_PKEY_verify_init(vctx) == 1) {
            ok = EVP_PKEY_verify(vctx, der, der_len,
                                 lean_sarray_cptr(msg_arr),
                                 FIELD_LEN) == 1;
        }
        EVP_PKEY_CTX_free(vctx);
    }

    EVP_PKEY_free(pkey);
    EVP_PKEY_CTX_free(kctx);
    ERR_pop_to_mark();
    return ok;
}
