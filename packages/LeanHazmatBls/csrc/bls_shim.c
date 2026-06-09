// LeanHazmatBls: C shim wrapping supranational/blst for Ethereum
// consensus-layer BLS signatures.
//
// Scheme: minimal-pubkey-size (pubkeys in G1, 48-byte compressed;
// signatures in G2, 96-byte compressed), ciphersuite
//   BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_
// (the proof-of-possession suite used by eth2). This maps to blst's
// `*_pk_in_g1` function family. See hazmat-docs/ARCHITECTURE.md §5/§7
// and the consensus-specs BLS test suite.
//
// Every entry point the Lean side declares `@[extern]` lives here
// (LeanHazmatBls/Ffi.lean). Byte inputs are borrowed
// (`b_lean_obj_arg` = `@&`); we do not touch their refcounts. Point
// results are returned as freshly-allocated `ByteArray`s; an *empty*
// `ByteArray` is the error sentinel (invalid input / bad encoding /
// empty aggregation list). Boolean results are returned as `uint8_t`
// (Lean `Bool`): 0 = false, 1 = true. Verification failure is a
// legitimate `false`, never a panic.
//
// Trust assumption (hazmat-docs/ARCHITECTURE.md §10): blst correctly
// implements BLS12-381 and the named ciphersuite. There is no
// pure-Lean reference for this primitive, it is an opaque FFI
// boundary, validated only against the official consensus-spec BLS
// vectors (LeanHazmatBlsTests).

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#include <lean/lean.h>
#include "blst.h"

// Weak `__libc_csu_*` stubs: glibc 2.34+ dropped these, but Lean's
// bundled `Scrt1.o` still references them when linking a `lake exe`
// that pulls this archive. Declared *weak* (unlike LeanHazmatSha256's
// strong copy) so that an executable linking both the SHA-256 and the
// BLS archives gets exactly one definition with no duplicate-symbol
// error. `native_decide` links a shared object (no `Scrt1.o`), so the
// test lib never needs these; they exist for a future standalone BLS
// executable. Never called at runtime.
__attribute__((weak)) void __libc_csu_init(int argc, char **argv, char **envp) {
    (void)argc; (void)argv; (void)envp;
}
__attribute__((weak)) void __libc_csu_fini(void) {}

// Consensus signature ciphersuite (proof-of-possession variant).
// 43 bytes, the trailing NUL is excluded via `sizeof - 1`.
static const byte CONSENSUS_DST[] =
    "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
#define DST_LEN  (sizeof(CONSENSUS_DST) - 1)

#define SK_LEN   32   // secret key, big-endian scalar
#define PK_LEN   48   // public key,  G1 compressed
#define SIG_LEN  96   // signature,   G2 compressed

// Fresh Lean `ByteArray` of length `n` with `src` copied in.
static inline lean_obj_res mk_bytearray(const byte *src, size_t n) {
    lean_object *arr = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(arr), src, n);
    return arr;
}

// The empty-ByteArray error sentinel.
static inline lean_obj_res mk_error(void) {
    return lean_alloc_sarray(1, 0, 0);
}

// ─────────────────────────────────────────────────────────────────────
// Sign : ByteArray (sk, 32) → ByteArray (msg) → ByteArray (sig, 96)
//   @[extern "lean_hazmat_bls_sign"]
// Returns the empty ByteArray if `sk` is not 32 bytes.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_sign(
    b_lean_obj_arg sk_arr, b_lean_obj_arg msg_arr)
{
    if (lean_sarray_size(sk_arr) != SK_LEN) return mk_error();

    const byte *sk_bytes = lean_sarray_cptr(sk_arr);
    const byte *msg      = lean_sarray_cptr(msg_arr);
    size_t      msg_len  = lean_sarray_size(msg_arr);

    blst_scalar sk;
    blst_scalar_from_bendian(&sk, sk_bytes);

    blst_p2 hash, sig_point;
    blst_hash_to_g2(&hash, msg, msg_len, CONSENSUS_DST, DST_LEN, NULL, 0);
    blst_sign_pk_in_g1(&sig_point, &hash, &sk);

    byte sig[SIG_LEN];
    blst_p2_compress(sig, &sig_point);
    return mk_bytearray(sig, SIG_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// SkToPk : ByteArray (sk, 32) → ByteArray (pk, 48)
//   @[extern "lean_hazmat_bls_sk_to_pk"]
// Derive the G1 public key for a secret key (validator key → pubkey).
// Returns the empty ByteArray if `sk` is not 32 bytes.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_sk_to_pk(b_lean_obj_arg sk_arr)
{
    if (lean_sarray_size(sk_arr) != SK_LEN) return mk_error();

    blst_scalar sk;
    blst_scalar_from_bendian(&sk, lean_sarray_cptr(sk_arr));

    blst_p1 pk_point;
    blst_sk_to_pk_in_g1(&pk_point, &sk);

    byte pk[PK_LEN];
    blst_p1_compress(pk, &pk_point);
    return mk_bytearray(pk, PK_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// Verify : pk(48) → msg → sig(96) → Bool
//   @[extern "lean_hazmat_bls_verify"]
// Includes the consensus `KeyValidate(pubkey)` reject of the identity
// point; `blst_core_verify_pk_in_g1` does the subgroup checks on both
// pk and sig internally.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_bls_verify(
    b_lean_obj_arg pk_arr, b_lean_obj_arg msg_arr, b_lean_obj_arg sig_arr)
{
    if (lean_sarray_size(pk_arr)  != PK_LEN)  return 0;
    if (lean_sarray_size(sig_arr) != SIG_LEN) return 0;

    const byte *pk_bytes  = lean_sarray_cptr(pk_arr);
    const byte *sig_bytes = lean_sarray_cptr(sig_arr);
    const byte *msg       = lean_sarray_cptr(msg_arr);
    size_t      msg_len   = lean_sarray_size(msg_arr);

    blst_p1_affine pk;
    if (blst_p1_uncompress(&pk, pk_bytes) != BLST_SUCCESS) return 0;
    if (blst_p1_affine_is_inf(&pk))                        return 0;  // KeyValidate

    blst_p2_affine sig;
    if (blst_p2_uncompress(&sig, sig_bytes) != BLST_SUCCESS) return 0;

    BLST_ERROR err = blst_core_verify_pk_in_g1(
        &pk, &sig, /*hash_or_encode=*/1,
        msg, msg_len, CONSENSUS_DST, DST_LEN, /*aug=*/NULL, 0);
    return (err == BLST_SUCCESS) ? 1 : 0;
}

// ─────────────────────────────────────────────────────────────────────
// KeyValidate : pk(48) → Bool
//   @[extern "lean_hazmat_bls_key_validate"]
// Valid encoding + on curve (uncompress), not the identity, in the
// prime-order G1 subgroup.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_bls_key_validate(b_lean_obj_arg pk_arr)
{
    if (lean_sarray_size(pk_arr) != PK_LEN) return 0;
    const byte *pk_bytes = lean_sarray_cptr(pk_arr);

    blst_p1_affine pk;
    if (blst_p1_uncompress(&pk, pk_bytes) != BLST_SUCCESS) return 0;
    if (blst_p1_affine_is_inf(&pk))                        return 0;
    if (!blst_p1_affine_in_g1(&pk))                        return 0;
    return 1;
}

// ─────────────────────────────────────────────────────────────────────
// Aggregate : Array ByteArray (sigs, each 96) → ByteArray (sig, 96)
//   @[extern "lean_hazmat_bls_aggregate"]
// G2 point addition. Empty list or any bad/wrong-length signature →
// empty ByteArray. Subgroup membership is NOT checked here (matches the
// spec `Aggregate`, which assumes valid inputs); callers validate via
// Verify.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_aggregate(b_lean_obj_arg sigs_arr)
{
    const size_t n = lean_array_size(sigs_arr);
    if (n == 0) return mk_error();

    blst_p2 agg;
    for (size_t i = 0; i < n; i++) {
        lean_object *s = lean_array_get_core(sigs_arr, i);
        if (lean_sarray_size(s) != SIG_LEN) return mk_error();
        blst_p2_affine s_aff;
        if (blst_p2_uncompress(&s_aff, lean_sarray_cptr(s)) != BLST_SUCCESS)
            return mk_error();
        if (i == 0)
            blst_p2_from_affine(&agg, &s_aff);
        else
            blst_p2_add_or_double_affine(&agg, &agg, &s_aff);
    }

    byte out[SIG_LEN];
    blst_p2_compress(out, &agg);
    return mk_bytearray(out, SIG_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// eth_aggregate_pubkeys : Array ByteArray (pks, each 48) → ByteArray (pk, 48)
//   @[extern "lean_hazmat_bls_eth_aggregate_pubkeys"]
// G1 point addition. Empty list or any bad pubkey → empty ByteArray.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_eth_aggregate_pubkeys(
    b_lean_obj_arg pks_arr)
{
    const size_t n = lean_array_size(pks_arr);
    if (n == 0) return mk_error();

    blst_p1 agg;
    for (size_t i = 0; i < n; i++) {
        lean_object *p = lean_array_get_core(pks_arr, i);
        if (lean_sarray_size(p) != PK_LEN) return mk_error();
        blst_p1_affine p_aff;
        if (blst_p1_uncompress(&p_aff, lean_sarray_cptr(p)) != BLST_SUCCESS)
            return mk_error();
        if (i == 0)
            blst_p1_from_affine(&agg, &p_aff);
        else
            blst_p1_add_or_double_affine(&agg, &agg, &p_aff);
    }

    byte out[PK_LEN];
    blst_p1_compress(out, &agg);
    return mk_bytearray(out, PK_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// g1_add : pk(48) → pk(48) → pk(48)
//   @[extern "lean_hazmat_bls_g1_add"]
// Raw G1 point addition of two compressed points (`bls.add` composed
// with `bytes48_to_G1` / `G1_to_bytes48`). Empty ByteArray on a bad
// length or encoding. No subgroup / identity rejection, this is a raw
// point op, matching `Aggregate`'s "assumes valid inputs" convention;
// callers establish validity via Verify. The sum may be the point at
// infinity (compressed `0xc0‖0×47`), e.g. `g1_add(p, g1_neg(p))`.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_g1_add(
    b_lean_obj_arg a_arr, b_lean_obj_arg b_arr)
{
    if (lean_sarray_size(a_arr) != PK_LEN) return mk_error();
    if (lean_sarray_size(b_arr) != PK_LEN) return mk_error();

    blst_p1_affine a_aff, b_aff;
    if (blst_p1_uncompress(&a_aff, lean_sarray_cptr(a_arr)) != BLST_SUCCESS)
        return mk_error();
    if (blst_p1_uncompress(&b_aff, lean_sarray_cptr(b_arr)) != BLST_SUCCESS)
        return mk_error();

    blst_p1 a, sum;
    blst_p1_from_affine(&a, &a_aff);
    blst_p1_add_or_double_affine(&sum, &a, &b_aff);

    byte out[PK_LEN];
    blst_p1_compress(out, &sum);
    return mk_bytearray(out, PK_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// g1_neg : pk(48) → pk(48)
//   @[extern "lean_hazmat_bls_g1_neg"]
// Negate a compressed G1 point (`G1_to_bytes48(neg(bytes48_to_G1(p)))`).
// Empty ByteArray on a bad length or encoding.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_bls_g1_neg(b_lean_obj_arg a_arr)
{
    if (lean_sarray_size(a_arr) != PK_LEN) return mk_error();

    blst_p1_affine a_aff;
    if (blst_p1_uncompress(&a_aff, lean_sarray_cptr(a_arr)) != BLST_SUCCESS)
        return mk_error();

    blst_p1 a;
    blst_p1_from_affine(&a, &a_aff);
    blst_p1_cneg(&a, /*cbit=*/true);

    byte out[PK_LEN];
    blst_p1_compress(out, &a);
    return mk_bytearray(out, PK_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// AggregateVerify : Array pk(48) → Array msg → sig(96) → Bool
//   @[extern "lean_hazmat_bls_aggregate_verify"]
// Distinct-message pairing check. `pks` and `msgs` must be the same
// non-zero length. Any bad pubkey/sig encoding → false.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_bls_aggregate_verify(
    b_lean_obj_arg pks_arr, b_lean_obj_arg msgs_arr, b_lean_obj_arg sig_arr)
{
    const size_t n = lean_array_size(pks_arr);
    if (n == 0) return 0;
    if (lean_array_size(msgs_arr) != n) return 0;
    if (lean_sarray_size(sig_arr) != SIG_LEN) return 0;

    blst_p2_affine sig;
    if (blst_p2_uncompress(&sig, lean_sarray_cptr(sig_arr)) != BLST_SUCCESS)
        return 0;

    blst_pairing *ctx = malloc(blst_pairing_sizeof());
    if (!ctx) return 0;
    blst_pairing_init(ctx, /*hash_or_encode=*/1, CONSENSUS_DST, DST_LEN);

    uint8_t result = 0;
    for (size_t i = 0; i < n; i++) {
        lean_object *p = lean_array_get_core(pks_arr,  i);
        lean_object *m = lean_array_get_core(msgs_arr, i);
        if (lean_sarray_size(p) != PK_LEN) goto done;
        blst_p1_affine pk;
        if (blst_p1_uncompress(&pk, lean_sarray_cptr(p)) != BLST_SUCCESS)
            goto done;
        if (blst_p1_affine_is_inf(&pk)) goto done;  // KeyValidate per message

        // Pass the (one) signature only on the first aggregate call.
        BLST_ERROR e = blst_pairing_aggregate_pk_in_g1(
            ctx, &pk, (i == 0) ? &sig : NULL,
            lean_sarray_cptr(m), lean_sarray_size(m), NULL, 0);
        if (e != BLST_SUCCESS) goto done;
    }
    blst_pairing_commit(ctx);
    result = blst_pairing_finalverify(ctx, NULL) ? 1 : 0;

done:
    free(ctx);
    return result;
}

// Shared core for FastAggregateVerify / eth_fast_aggregate_verify:
// aggregate `pks` (each 48) in G1, then a single CoreVerify against the
// one `msg`. Returns 0/1. Assumes n >= 1 (the empty-list policy differs
// between the two callers and is handled there).
static uint8_t fast_aggregate_verify_core(
    b_lean_obj_arg pks_arr, b_lean_obj_arg msg_arr, b_lean_obj_arg sig_arr)
{
    const size_t n = lean_array_size(pks_arr);
    if (lean_sarray_size(sig_arr) != SIG_LEN) return 0;

    blst_p1 agg;
    for (size_t i = 0; i < n; i++) {
        lean_object *p = lean_array_get_core(pks_arr, i);
        if (lean_sarray_size(p) != PK_LEN) return 0;
        blst_p1_affine p_aff;
        if (blst_p1_uncompress(&p_aff, lean_sarray_cptr(p)) != BLST_SUCCESS)
            return 0;
        if (blst_p1_affine_is_inf(&p_aff)) return 0;  // KeyValidate per pubkey
        if (i == 0)
            blst_p1_from_affine(&agg, &p_aff);
        else
            blst_p1_add_or_double_affine(&agg, &agg, &p_aff);
    }
    blst_p1_affine agg_aff;
    blst_p1_to_affine(&agg_aff, &agg);

    blst_p2_affine sig;
    if (blst_p2_uncompress(&sig, lean_sarray_cptr(sig_arr)) != BLST_SUCCESS)
        return 0;

    BLST_ERROR err = blst_core_verify_pk_in_g1(
        &agg_aff, &sig, /*hash_or_encode=*/1,
        lean_sarray_cptr(msg_arr), lean_sarray_size(msg_arr),
        CONSENSUS_DST, DST_LEN, NULL, 0);
    return (err == BLST_SUCCESS) ? 1 : 0;
}

// ─────────────────────────────────────────────────────────────────────
// FastAggregateVerify : Array pk(48) → msg → sig(96) → Bool
//   @[extern "lean_hazmat_bls_fast_aggregate_verify"]
// Same-message aggregate verify. Empty pubkey list → false (the IETF
// FastAggregateVerify is undefined for an empty list).
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_bls_fast_aggregate_verify(
    b_lean_obj_arg pks_arr, b_lean_obj_arg msg_arr, b_lean_obj_arg sig_arr)
{
    if (lean_array_size(pks_arr) == 0) return 0;
    return fast_aggregate_verify_core(pks_arr, msg_arr, sig_arr);
}

// The canonical G2 point-at-infinity compressed encoding: 0xc0 then 95
// zero bytes. The consensus `eth_fast_aggregate_verify` empty-list case
// accepts exactly this signature.
static int is_infinity_sig(const byte *sig) {
    if (sig[0] != 0xc0) return 0;
    for (size_t i = 1; i < SIG_LEN; i++) if (sig[i] != 0x00) return 0;
    return 1;
}

// ─────────────────────────────────────────────────────────────────────
// eth_fast_aggregate_verify : Array pk(48) → msg → sig(96) → Bool
//   @[extern "lean_hazmat_bls_eth_fast_aggregate_verify"]
// Consensus variant: an empty pubkey list verifies iff the signature is
// the G2 point at infinity (per the spec); otherwise FastAggregateVerify.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_bls_eth_fast_aggregate_verify(
    b_lean_obj_arg pks_arr, b_lean_obj_arg msg_arr, b_lean_obj_arg sig_arr)
{
    if (lean_sarray_size(sig_arr) != SIG_LEN) return 0;
    if (lean_array_size(pks_arr) == 0)
        return is_infinity_sig(lean_sarray_cptr(sig_arr)) ? 1 : 0;
    return fast_aggregate_verify_core(pks_arr, msg_arr, sig_arr);
}
