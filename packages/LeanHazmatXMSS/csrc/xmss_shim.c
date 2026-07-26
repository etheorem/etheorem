// LeanHazmatXMSS: C shim wrapping xmss-reference for RFC 8391 XMSS-SHA2.
//
// Exposes three symbols declared `@[extern]` in LeanHazmatXMSS/Ffi.lean:
//   lean_hazmat_xmss_keygen_seeded  deterministic keygen (for KATs)
//   lean_hazmat_xmss_sign           sign, returning sig ++ updated SK
//   lean_hazmat_xmss_verify         verify a signature
//
// --- Size conventions ---
//
// xmss.c (the public wrapper) prepends a 4-byte big-endian OID to BOTH pk
// and sk on output, using XMSS_OID_LEN = 4. The `xmss_params` struct fields
// `pk_bytes` and `sk_bytes` are the CORE sizes (without the OID prefix):
//
//   actual pk size = XMSS_OID_LEN + params.pk_bytes
//   actual sk size = XMSS_OID_LEN + params.sk_bytes
//
// For XMSS-SHA2_10_256 (OID 0x00000001, n=32, h=10, simple core):
//   params.pk_bytes  = 2*32         = 64  → actual pk = 68 bytes
//   params.sk_bytes  = 4 + 4*32     = 132 → actual sk = 136 bytes
//   params.sig_bytes = 4+32+67*32+10*32 = 2500 (no OID in sig)
//
// xmss_sign() expects the FULL sk (with OID prefix) and handles the offset
// internally. xmss_sign_open() expects the FULL pk (with OID prefix).
// The sig output (sm = sig || msg) contains no OID; params.sig_bytes is exact.
//
// --- randombytes ---
//
// xmss-reference calls randombytes() during xmss_keypair to fill sk_seed,
// sk_prf, and pub_seed (3*n bytes total). We provide our own implementation:
// in deterministic mode (g_use_det_seed), a counter fills bytes 0,1,2,...
// lean_hazmat_xmss_keygen_seeded resets the counter to 0 before each call,
// making keygen idempotent for KAT testing. The normal mode reads /dev/urandom.
//
// Trust assumption: xmss-reference correctly implements RFC 8391 XMSS-SHA2.
// Validated by LeanHazmatXMSSTests/Vectors.lean.

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include <lean/lean.h>
#include "xmss.h"
#include "params.h"

// Weak __libc_csu_* stubs: glibc 2.34+ removed these symbols but Lean's
// Scrt1.o still references them. Declared weak so an exe linking multiple
// hazmat archives gets exactly one definition (strong copy is in sha256_shim.c).
__attribute__((weak)) void __libc_csu_init(int argc, char **argv, char **envp) {
    (void)argc; (void)argv; (void)envp;
}
__attribute__((weak)) void __libc_csu_fini(void) {}

// randombytes: our replacement for xmss-reference's randombytes.c.
static int g_use_det_seed = 0;
static uint8_t g_det_counter = 0;

int randombytes(unsigned char *x, unsigned long long xlen) {
    if (g_use_det_seed) {
        for (unsigned long long i = 0; i < xlen; i++) {
            x[i] = g_det_counter++;
        }
        return 0;
    }
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) return -1;
    size_t r = fread(x, 1, (size_t)xlen, f);
    fclose(f);
    return (r == (size_t)xlen) ? 0 : -1;
}

static uint32_t parse_oid(b_lean_obj_arg arr) {
    const uint8_t *b = (const uint8_t *)lean_sarray_cptr(arr);
    return ((uint32_t)b[0] << 24) | ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] << 8)  |  (uint32_t)b[3];
}

// Empty ByteArray error sentinel (consistent with other hazmat families).
static inline lean_obj_res mk_error(void) {
    return lean_alloc_sarray(1, 0, 0);
}

// lean_hazmat_xmss_keygen_seeded
//
//   oid_arr : 4-byte big-endian OID (e.g. {0,0,0,1} for XMSS-SHA2_10_256).
//   returns : pk ++ sk, or empty ByteArray on invalid OID or allocation failure.
//
// pk is (XMSS_OID_LEN + params.pk_bytes) bytes; sk follows immediately.
// The counter resets to 0 on each call → repeated calls with the same OID
// always produce the same pk and sk.
LEAN_EXPORT lean_obj_res lean_hazmat_xmss_keygen_seeded(b_lean_obj_arg oid_arr) {
    if (lean_sarray_size(oid_arr) != 4) return mk_error();

    uint32_t oid = parse_oid(oid_arr);
    xmss_params params;
    if (xmss_parse_oid(&params, oid) != 0) return mk_error();

    // xmss_keypair writes (XMSS_OID_LEN + params.pk_bytes) bytes into pk
    // and (XMSS_OID_LEN + params.sk_bytes) bytes into sk.
    size_t pk_total = XMSS_OID_LEN + params.pk_bytes;
    size_t sk_total = XMSS_OID_LEN + (size_t)params.sk_bytes;

    uint8_t *pk = (uint8_t *)malloc(pk_total);
    uint8_t *sk = (uint8_t *)malloc(sk_total);
    if (!pk || !sk) { free(pk); free(sk); return mk_error(); }

    g_use_det_seed = 1;
    g_det_counter  = 0;
    int ret = xmss_keypair(pk, sk, oid);
    g_use_det_seed = 0;

    lean_obj_res out = mk_error();
    if (ret == 0) {
        size_t total = pk_total + sk_total;
        out = lean_alloc_sarray(1, total, total);
        uint8_t *ptr = (uint8_t *)lean_sarray_cptr(out);
        memcpy(ptr,           pk, pk_total);
        memcpy(ptr + pk_total, sk, sk_total);
    }
    free(pk);
    free(sk);
    return out;
}

// lean_hazmat_xmss_sign
//
//   sk_arr  : current SK (XMSS_OID_LEN + params.sk_bytes bytes).
//   msg_arr : message to sign (arbitrary length).
//   returns : sig ++ new_sk, or empty ByteArray on invalid SK / OID.
//
// sig is params.sig_bytes bytes; new_sk is the updated full SK (same size as
// the input sk). The caller must thread new_sk through for subsequent signs.
LEAN_EXPORT lean_obj_res lean_hazmat_xmss_sign(
    b_lean_obj_arg sk_arr, b_lean_obj_arg msg_arr)
{
    if (lean_sarray_size(sk_arr) < 4) return mk_error();

    // OID from first 4 bytes of sk (big-endian, written by xmss_keypair).
    uint32_t oid = parse_oid(sk_arr);
    xmss_params params;
    if (xmss_parse_oid(&params, oid) != 0) return mk_error();

    size_t sk_total = XMSS_OID_LEN + (size_t)params.sk_bytes;
    if (lean_sarray_size(sk_arr) != sk_total) return mk_error();

    // Copy the full sk (with OID prefix): xmss_sign mutates it internally.
    uint8_t *sk_copy = (uint8_t *)malloc(sk_total);
    if (!sk_copy) return mk_error();
    memcpy(sk_copy, lean_sarray_cptr(sk_arr), sk_total);

    size_t msglen     = lean_sarray_size(msg_arr);
    const uint8_t *msg = (const uint8_t *)lean_sarray_cptr(msg_arr);

    // xmss_sign writes sm = sig || msg (params.sig_bytes + msglen bytes).
    unsigned long long smlen = 0;
    uint8_t *sm = (uint8_t *)malloc(params.sig_bytes + msglen);
    if (!sm) { free(sk_copy); return mk_error(); }

    int ret = xmss_sign(sk_copy, sm, &smlen, msg, (unsigned long long)msglen);

    lean_obj_res out = mk_error();
    if (ret == 0) {
        // Return sig (first sig_bytes of sm) ++ updated full sk.
        size_t total = params.sig_bytes + sk_total;
        out = lean_alloc_sarray(1, total, total);
        uint8_t *ptr = (uint8_t *)lean_sarray_cptr(out);
        memcpy(ptr,                    sm,       params.sig_bytes);
        memcpy(ptr + params.sig_bytes, sk_copy, sk_total);
    }
    free(sm);
    free(sk_copy);
    return out;
}


// lean_hazmat_xmss_verify
//
//   pk_arr  : public key (XMSS_OID_LEN + params.pk_bytes bytes).
//   sig_arr : signature (params.sig_bytes bytes for the given OID).
//   msg_arr : the message that was signed.
//   returns : 1 (Lean true) if valid, 0 otherwise.
//
// Reconstructs sm = sig || msg internally (what xmss_sign_open expects) and
// discards the recovered message; only the validity result matters here.
LEAN_EXPORT uint8_t lean_hazmat_xmss_verify(
    b_lean_obj_arg pk_arr, b_lean_obj_arg sig_arr, b_lean_obj_arg msg_arr)
{
    if (lean_sarray_size(pk_arr) < 4) return 0;

    // OID from first 4 bytes of pk (big-endian, written by xmss_keypair).
    uint32_t oid = parse_oid(pk_arr);
    xmss_params params;
    if (xmss_parse_oid(&params, oid) != 0) return 0;

    size_t pk_total = XMSS_OID_LEN + params.pk_bytes;
    if (lean_sarray_size(pk_arr)  != pk_total)         return 0;
    if (lean_sarray_size(sig_arr) != params.sig_bytes) return 0;

    size_t msglen      = lean_sarray_size(msg_arr);
    const uint8_t *msg = (const uint8_t *)lean_sarray_cptr(msg_arr);
    const uint8_t *pk  = (const uint8_t *)lean_sarray_cptr(pk_arr);
    const uint8_t *sig = (const uint8_t *)lean_sarray_cptr(sig_arr);

    // Reconstruct sm = sig || msg for xmss_sign_open.
    unsigned long long smlen = (unsigned long long)(params.sig_bytes + msglen);
    uint8_t *sm = (uint8_t *)malloc((size_t)smlen);
    if (!sm) return 0;
    memcpy(sm,                    sig, params.sig_bytes);
    memcpy(sm + params.sig_bytes, msg, msglen);

    // m_out receives the recovered message on success (we discard it).
    uint8_t *m_out = (uint8_t *)malloc((size_t)smlen);
    if (!m_out) { free(sm); return 0; }
    unsigned long long mlen_out = 0;

    // xmss_sign_open takes the full pk (with OID prefix) and handles internally.
    // Returns 0 on valid signature, non-zero on invalid.
    int ret = xmss_sign_open(m_out, &mlen_out, sm, smlen, pk);

    free(sm);
    free(m_out);
    return (ret == 0) ? 1 : 0;
}
