// LeanHazmatXmss: C shim wrapping xmss-reference for RFC 8391 XMSS-SHA2.
//
// Exposes four symbols declared `@[extern]` in LeanHazmatXmss/Ffi.lean:
//   lean_hazmat_xmss_param_sizes      (pk_bytes, sig_bytes, sk_bytes) for an OID
//   lean_hazmat_xmss_keygen_from_seed keygen from a caller-supplied 3*n seed
//   lean_hazmat_xmss_sign             sign, returning sig ++ updated SK
//   lean_hazmat_xmss_verify           verify a signature
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
// For XMSS-SHA2_10_256 (OID 0x00000001, n=32, h=10, w=16):
//   params.pk_bytes  = 2*32                = 64   -> actual pk = 68 bytes
//   params.sk_bytes  = 4 + 4*32            = 132  -> actual sk = 136 bytes
//   params.sig_bytes = 4 + 32 + 67*32 + 10*32 = 2500 (no OID in sig)
//
// The signature layout is `sig_bytes = index_bytes + n + wots_sig_bytes
// + full_height*n` (params.c). For n=32, w=16 the WOTS length is 67, so
// sig_bytes = 4 + 32 + 67*32 + h*32 = 2180 + 32*h:
//   h=10 -> 2500,  h=16 -> 2692,  h=20 -> 2820.
//
// xmss_sign() expects the FULL sk (with OID prefix) and handles the offset
// internally. xmss_sign_open() expects the FULL pk (with OID prefix).
// The sig output (sm = sig || msg) contains no OID; params.sig_bytes is exact.
//
// --- randombytes ---
//
// xmss-reference's non-seeded keygen (xmssmt_core_keypair) calls randombytes()
// to fill sk_seed || sk_prf || pub_seed. We never enter that path: keygen goes
// through xmssmt_core_seed_keypair() with a caller-supplied seed, so key
// material is a pure function of (oid, seed) with no process state. The
// randombytes() below exists only to satisfy the linker (xmss_core.o still
// references it) and reads /dev/urandom, the honest source if some future path
// ever reaches it. It is declared weak so linking a second archive that also
// defines randombytes does not collide (the same treatment the __libc_csu_*
// stubs get below).
//
// Trust assumption: xmss-reference correctly implements RFC 8391 XMSS-SHA2.
// Validated by LeanHazmatXmssTests/Vectors.lean.

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include <lean/lean.h>
#include "xmss.h"
#include "xmss_core.h"
#include "params.h"
#include "fips202.h"

// Weak __libc_csu_* stubs: glibc 2.34+ removed these symbols but Lean's
// Scrt1.o still references them. Declared weak so an exe linking multiple
// hazmat archives gets exactly one definition (strong copy is in sha256_shim.c).
__attribute__((weak)) void __libc_csu_init(int argc, char **argv, char **envp) {
    (void)argc; (void)argv; (void)envp;
}
__attribute__((weak)) void __libc_csu_fini(void) {}

// randombytes: weak fallback so the archive links even though our exposed API
// never calls it (keygen is seeded). Reads /dev/urandom. Matches the `void`
// signature in randombytes.h. Weak, so a co-linked archive's randombytes wins.
__attribute__((weak)) void randombytes(unsigned char *x, unsigned long long xlen) {
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) { memset(x, 0, (size_t)xlen); return; }
    size_t r = fread(x, 1, (size_t)xlen, f);
    fclose(f);
    if (r != (size_t)xlen) memset(x, 0, (size_t)xlen);
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

// lean_hazmat_xmss_shake128
//
//   data    : input bytes.
//   out_len : requested digest length in bytes.
//   returns : the first out_len bytes of SHAKE128(data).
//
// KAT support only: the test suite hashes keygen/sign output with this and
// compares against the digests xmss-reference's own `test/vectors.c` prints
// (`shake128(pk_core, 10)`, `shake128(sig, 10)`), so the anchors are checked
// against upstream's reference vectors, not against our own extraction. Wraps
// the fips202.c SHAKE already in the archive; not part of the XMSS API and
// deliberately not re-exported from LeanHazmatXmss.lean.
LEAN_EXPORT lean_obj_res lean_hazmat_xmss_shake128(
    b_lean_obj_arg data, size_t out_len)
{
    lean_obj_res out = lean_alloc_sarray(1, out_len, out_len);
    shake128((uint8_t *)lean_sarray_cptr(out), (unsigned long long)out_len,
             (const uint8_t *)lean_sarray_cptr(data),
             (unsigned long long)lean_sarray_size(data));
    return out;
}

// lean_hazmat_xmss_param_sizes
//
//   oid_arr : 4-byte big-endian OID.
//   returns : some (pk_bytes, sig_bytes, sk_bytes) with the OID-prefixed pk/sk
//             sizes and the exact sig size, or none on an unrecognized OID.
//
// This is the single source of truth for the buffer sizes; Lean callers slice
// keygen/sign output by these numbers instead of hard-coding constants.
LEAN_EXPORT lean_obj_res lean_hazmat_xmss_param_sizes(b_lean_obj_arg oid_arr) {
    if (lean_sarray_size(oid_arr) != 4) return lean_box(0);  // none

    xmss_params params;
    if (xmss_parse_oid(&params, parse_oid(oid_arr)) != 0) return lean_box(0);

    size_t pk_total = XMSS_OID_LEN + params.pk_bytes;
    size_t sk_total = XMSS_OID_LEN + (size_t)params.sk_bytes;

    // Build `some (pk, sig, sk)` : Option (Nat × Nat × Nat).
    // `Nat × Nat × Nat` is `Prod Nat (Prod Nat Nat)`: an outer 2-field ctor
    // whose second field is an inner 2-field ctor. `some` is ctor tag 1.
    lean_object *inner = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inner, 0, lean_usize_to_nat((size_t)params.sig_bytes));
    lean_ctor_set(inner, 1, lean_usize_to_nat(sk_total));
    lean_object *outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, lean_usize_to_nat(pk_total));
    lean_ctor_set(outer, 1, inner);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, outer);
    return some;
}

// lean_hazmat_xmss_keygen_from_seed
//
//   oid_arr  : 4-byte big-endian OID (e.g. {0,0,0,1} for XMSS-SHA2_10_256).
//   seed_arr : exactly 3*n bytes (sk_seed || sk_prf || pub_seed).
//   returns  : pk ++ sk, or empty ByteArray on invalid OID / seed length /
//              allocation failure.
//
// Key material is a pure function of (oid, seed): no randombytes, no process
// state, so two calls with the same inputs always agree. This is what makes
// the `opaque` Lean declaration sound and the KAT reproducible.
LEAN_EXPORT lean_obj_res lean_hazmat_xmss_keygen_from_seed(
    b_lean_obj_arg oid_arr, b_lean_obj_arg seed_arr)
{
    if (lean_sarray_size(oid_arr) != 4) return mk_error();

    uint32_t oid = parse_oid(oid_arr);
    xmss_params params;
    if (xmss_parse_oid(&params, oid) != 0) return mk_error();

    size_t seed_len = 3 * (size_t)params.n;
    if (lean_sarray_size(seed_arr) != seed_len) return mk_error();

    size_t pk_total = XMSS_OID_LEN + params.pk_bytes;
    size_t sk_total = XMSS_OID_LEN + (size_t)params.sk_bytes;

    uint8_t *pk = (uint8_t *)malloc(pk_total);
    uint8_t *sk = (uint8_t *)malloc(sk_total);
    // xmssmt_core_seed_keypair takes a non-const seed; copy the borrowed input.
    uint8_t *seed = (uint8_t *)malloc(seed_len);
    if (!pk || !sk || !seed) { free(pk); free(sk); free(seed); return mk_error(); }
    memcpy(seed, lean_sarray_cptr(seed_arr), seed_len);

    // Prepend the 4-byte big-endian OID to pk and sk (what xmss.c's
    // xmss_keypair does), then fill the core key bytes from the seed.
    for (unsigned i = 0; i < XMSS_OID_LEN; i++) {
        pk[XMSS_OID_LEN - i - 1] = (oid >> (8 * i)) & 0xFF;
        sk[XMSS_OID_LEN - i - 1] = (oid >> (8 * i)) & 0xFF;
    }
    int ret = xmssmt_core_seed_keypair(&params, pk + XMSS_OID_LEN,
                                       sk + XMSS_OID_LEN, seed);

    lean_obj_res out = mk_error();
    if (ret == 0) {
        size_t total = pk_total + sk_total;
        out = lean_alloc_sarray(1, total, total);
        uint8_t *ptr = (uint8_t *)lean_sarray_cptr(out);
        memcpy(ptr,            pk, pk_total);
        memcpy(ptr + pk_total, sk, sk_total);
    }
    free(pk);
    free(sk);
    free(seed);
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

    // OID from first 4 bytes of sk (big-endian, written by keygen).
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

    // Guard the layout we are about to slice: xmss_sign must have written
    // exactly sig_bytes of signature ahead of the msg copy.
    unsigned long long expected = (unsigned long long)params.sig_bytes + msglen;

    lean_obj_res out = mk_error();
    if (ret == 0 && smlen == expected) {
        // Return sig (first sig_bytes of sm) ++ updated full sk.
        size_t total = params.sig_bytes + sk_total;
        out = lean_alloc_sarray(1, total, total);
        uint8_t *ptr = (uint8_t *)lean_sarray_cptr(out);
        memcpy(ptr,                    sm,      params.sig_bytes);
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

    // OID from first 4 bytes of pk (big-endian, written by keygen).
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
