// LeanHazmatBn254: C++ shim wrapping the vendored herumi/mcl for the
// Ethereum execution-layer alt_bn128 (BN254) precompile primitives
// (EIP-196 add/mul, EIP-197/1108 pairing).
//
// Surface (raw primitives, per packages/hazmat/docs/ARCHITECTURE.md §4):
//   * g1Add / g1Mul       : EIP-196 ECADD / ECMUL on G1
//   * g2Add / g2Mul       : the EIP-197 G2 counterparts
//   * millerLoopVec       : prod_i e(g1_i, g2_i) as one miller loop
//                           product (GT)
//   * finalExp            : the pairing's final exponentiation (GT → GT)
//   * gtIsOne             : the pairing-check predicate on GT
// The EIP-197 pairing check composes these in the caller:
// `gtIsOne (finalExp (millerLoopVec pairs))`; the input parse, gas,
// and `0x…01` output encoding are all consumer concerns.
//
// Encodings at this boundary (the EIPs' own, so the test vectors read
// verbatim):
//   * Field elements: 32-byte big-endian, must be < p (setStr in
//     serialize | big-endian mode range-checks).
//   * G1 point: 64 bytes, `x ‖ y`; the point at infinity is all
//     zeros (EIP-196).
//   * G2 point: 128 bytes, `(x_a ‖ x_b) ‖ (y_a ‖ y_b)` where
//     x = x_b + x_a * i (EIP-197: "elements a*i + b are encoded as
//     (a, b)", the imaginary part comes first; mcl's own order is
//     (real, imag), so the shim swaps).
//   * Scalars: 32-byte big-endian, reduced mod the group order r
//     (EIP-196: "the scalar can be any number between 0 and 2^256-1";
//     mclBnFr_setBigEndianMod does the reduction).
//   * GT: 384 bytes, mcl's GT serialization (twelve 32-byte
//     big-endian Fp coefficients); the encoding round-trips through
//     this family's own functions, which is all a pairing-check
//     consumer needs (finalExp / gtIsOne are the only GT consumers).
//
// Validation: point deserialization checks coordinates < p and the
// curve equation (mclBnG1_isValid / mclBnG2_isValid); G2 additionally
// checks the order-r subgroup (`mclBn_verifyOrderG2(1)`, pinned by
// `bn254_init_once`), which is EIP-197's membership rule. G1 skips the
// order check (cofactor 1, so on-curve implies in-group; see the
// initializer comment). Any failure yields the empty
// ByteArray (or `false` for gtIsOne), never a panic.
//
// Build shape: mcl's whole C API comes out of ONE translation unit,
// `src/fp.cpp`, compiled by the system C++ compiler with
// `-DMCL_FP_BIT=256 -DMCL_FR_BIT=256 -DMCL_BINT_ASM=0` (the portable C
// bignum primitives) plus the no-runtime defines
// `-fno-exceptions -fno-rtti -fno-threadsafe-statics`,
// `-DCYBOZU_DONT_USE_EXCEPTION`, `-DCYBOZU_DONT_USE_STRING`,
// `-DMCL_DONT_USE_CSPRNG`, and `-DMCL_DONT_USE_XBYAK` (the `src/bn_c256.cpp`
// in the tree is an empty placeholder). Under those flags the compiled
// code references ONLY libc and libgcc: no operator new, no iostream,
// no exception machinery, no libstdc++ / libc++ at all. The archive is
// therefore as self-contained as the C families, with no `-lstdc++`
// anywhere and nothing for a consumer's link to trip over (link args
// do not propagate across `require`, packages/hazmat/docs/PLAN.md Stage 0).
// mcl's error paths, which would throw, become aborts through the
// CYBOZU_DONT_USE_EXCEPTION mapping; they fire only on internal errors
// (allocation failure, malformed internal state), never on the inputs
// this surface accepts.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): the vendored
// mcl (v4.10) implements the alt_bn128 curve and its optimal ate
// pairing correctly. There is no pure-Lean reference; validated only
// against the published EIP-196/197 vectors (generated from
// ethereum/py_ecc, the EIP-197-referenced reference implementation)
// in LeanHazmatBn254Tests.

#include <stddef.h>
#include <stdint.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>
#include <mcl/bn.h>

static const int kIoMode = MCLBN_IO_SERIALIZE | MCLBN_IO_BIG_ENDIAN;

#define G1_LEN   64   // x ‖ y
#define G2_LEN  128   // (x_a ‖ x_b) ‖ (y_a ‖ y_b), a = imaginary
#define FP_LEN   32
#define GT_LEN  384   // twelve 32-byte Fp coefficients
#define SCALAR_LEN 32

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

// Set once by `bn254_init_once` under its pthread_once; read-only
// afterwards.
static bool bn254_ready_flag = false;

// The one-time initializer `pthread_once` hands to. `mclBn_init` is
// not thread-safe, so the guard is `pthread_once`: exactly one caller
// initializes, every other one waits for it. After init, the subgroup
// policies are pinned, never left to mcl's defaults:
// `mclBn_verifyOrderG1(0)` (BN254 G1 has cofactor 1, so the on-curve
// check inside `isValid` already proves membership; the order check
// would add a scalar multiplication by r to every G1 read and can
// never fail) and `mclBn_verifyOrderG2(1)` (EIP-197 requires G2
// subgroup membership).
// A named function with C linkage: `pthread_once` expects a function
// with C language linkage, and an explicit name keeps that guarantee
// obvious.
extern "C" {
static void bn254_init_once(void) {
    if (mclBn_init(MCL_BN_SNARK1, MCLBN_COMPILED_TIME_VAR) == 0) {
        mclBn_verifyOrderG1(0);
        mclBn_verifyOrderG2(1);
        bn254_ready_flag = true;
    }
}
}

// The readiness check every shim entry point calls first. Runs
// `bn254_init_once` at most once, then reports whether that run
// pinned the subgroup checks.
// `pthread_once` resolves from libc on glibc 2.34 and later (and on
// musl and macOS); on older glibc it lives in libpthread, so the
// package's lakefile adds `-lpthread` to this package's own test-lib
// link.
static bool bn254_ready(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, bn254_init_once);
    return bn254_ready_flag;
}

static bool fp_from_bytes(mclBnFp *out, const uint8_t *b) {
    return mclBnFp_setStr(out, (const char *)b, FP_LEN, kIoMode) == 0;
}

// `getStr` NUL-terminates at buf[n] even when the serialization fills
// maxBufSize exactly (mcl/operator.hpp), so the scratch must hold one
// byte more than the value copied out. maxBufSize itself stays at
// FP_LEN: mcl rejects a full-length serialization when maxBufSize is
// FP_LEN + 1 (`n == maxBufSize - 1` is a failure there).
static bool fp_to_bytes(uint8_t *out, const mclBnFp &x) {
    char buf[FP_LEN + 1];
    if (mclBnFp_getStr(buf, FP_LEN, &x, kIoMode) != FP_LEN) return false;
    memcpy(out, buf, FP_LEN);
    return true;
}

static bool g1_from_bytes(mclBnG1 *P, const uint8_t *b) {
    bool zero = true;
    for (size_t i = 0; i < G1_LEN; i++)
        if (b[i]) { zero = false; break; }
    if (zero) {
        mclBnG1_clear(P);
        return true;
    }
    if (!fp_from_bytes(&P->x, b) || !fp_from_bytes(&P->y, b + FP_LEN))
        return false;
    mclBnFp_setInt32(&P->z, 1);
    return mclBnG1_isValid(P);
}

static bool g1_to_bytes(uint8_t *out, const mclBnG1 &P) {
    mclBnG1 n;
    mclBnG1_normalize(&n, &P);
    if (mclBnG1_isZero(&n)) {
        memset(out, 0, G1_LEN);
        return true;
    }
    return fp_to_bytes(out, n.x) && fp_to_bytes(out + FP_LEN, n.y);
}

// EIP-197 encodes `a*i + b` as the pair `(a, b)`: the imaginary
// half first. mcl stores an Fp2 as `d[0] + d[1]*i` (real first), so
// the halves swap here.
static bool fp2_from_bytes(mclBnFp2 *out, const uint8_t *b) {
    return fp_from_bytes(&out->d[1], b) &&
           fp_from_bytes(&out->d[0], b + FP_LEN);
}

static bool fp2_to_bytes(uint8_t *out, const mclBnFp2 &x) {
    return fp_to_bytes(out, x.d[1]) && fp_to_bytes(out + FP_LEN, x.d[0]);
}

static bool g2_from_bytes(mclBnG2 *P, const uint8_t *b) {
    bool zero = true;
    for (size_t i = 0; i < G2_LEN; i++)
        if (b[i]) { zero = false; break; }
    if (zero) {
        mclBnG2_clear(P);
        return true;
    }
    if (!fp2_from_bytes(&P->x, b) || !fp2_from_bytes(&P->y, b + 2 * FP_LEN))
        return false;
    mclBnFp_setInt32(&P->z.d[0], 1);
    mclBnFp_clear(&P->z.d[1]);
    // Includes the order-r subgroup check (`mclBn_verifyOrderG2(1)`,
    // pinned by `bn254_init_once`), which is EIP-197's membership rule.
    return mclBnG2_isValid(P);
}

static bool g2_to_bytes(uint8_t *out, const mclBnG2 &P) {
    mclBnG2 n;
    mclBnG2_normalize(&n, &P);
    if (mclBnG2_isZero(&n)) {
        memset(out, 0, G2_LEN);
        return true;
    }
    return fp2_to_bytes(out, n.x) && fp2_to_bytes(out + 2 * FP_LEN, n.y);
}

static bool gt_from_bytes(mclBnGT *out, const uint8_t *b) {
    return mclBnGT_setStr(out, (const char *)b, GT_LEN, kIoMode) == 0;
}

static bool gt_to_bytes(uint8_t *out, const mclBnGT &x) {
    // Same getStr contract as fp_to_bytes: maxBufSize GT_LEN, scratch
    // GT_LEN + 1.
    char buf[GT_LEN + 1];
    if (mclBnGT_getStr(buf, GT_LEN, &x, kIoMode) != GT_LEN) return false;
    memcpy(out, buf, GT_LEN);
    return true;
}

// ─────────────────────────────────────────────────────────────────────
// g1Add : 64 → 64 → 64   @[extern "lean_hazmat_bn254_g1_add"]
// The EIP-196 ECADD primitive. Empty ByteArray on a bad length or an
// invalid point.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_g1_add(
    b_lean_obj_arg a_arr, b_lean_obj_arg b_arr)
{
    if (!bn254_ready()) return mk_error();
    if (lean_sarray_size(a_arr) != G1_LEN) return mk_error();
    if (lean_sarray_size(b_arr) != G1_LEN) return mk_error();

    mclBnG1 a, b, r;
    if (!g1_from_bytes(&a, lean_sarray_cptr(a_arr))) return mk_error();
    if (!g1_from_bytes(&b, lean_sarray_cptr(b_arr))) return mk_error();
    mclBnG1_add(&r, &a, &b);

    uint8_t out[G1_LEN];
    if (!g1_to_bytes(out, r)) return mk_error();
    return mk_bytearray(out, G1_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// g1Mul : 64 → 32 → 64   @[extern "lean_hazmat_bn254_g1_mul"]
// The EIP-196 ECMUL primitive. The scalar is reduced mod the group
// order (EIP-196 allows any 256-bit value).
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_g1_mul(
    b_lean_obj_arg a_arr, b_lean_obj_arg k_arr)
{
    if (!bn254_ready()) return mk_error();
    if (lean_sarray_size(a_arr) != G1_LEN) return mk_error();
    if (lean_sarray_size(k_arr) != SCALAR_LEN) return mk_error();

    mclBnG1 a, r;
    mclBnFr k;
    if (!g1_from_bytes(&a, lean_sarray_cptr(a_arr))) return mk_error();
    if (mclBnFr_setBigEndianMod(&k, lean_sarray_cptr(k_arr),
                                SCALAR_LEN) != 0)
        return mk_error();
    mclBnG1_mul(&r, &a, &k);

    uint8_t out[G1_LEN];
    if (!g1_to_bytes(out, r)) return mk_error();
    return mk_bytearray(out, G1_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// g2Add : 128 → 128 → 128   @[extern "lean_hazmat_bn254_g2_add"]
// The EIP-197 G2 addition primitive.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_g2_add(
    b_lean_obj_arg a_arr, b_lean_obj_arg b_arr)
{
    if (!bn254_ready()) return mk_error();
    if (lean_sarray_size(a_arr) != G2_LEN) return mk_error();
    if (lean_sarray_size(b_arr) != G2_LEN) return mk_error();

    mclBnG2 a, b, r;
    if (!g2_from_bytes(&a, lean_sarray_cptr(a_arr))) return mk_error();
    if (!g2_from_bytes(&b, lean_sarray_cptr(b_arr))) return mk_error();
    mclBnG2_add(&r, &a, &b);

    uint8_t out[G2_LEN];
    if (!g2_to_bytes(out, r)) return mk_error();
    return mk_bytearray(out, G2_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// g2Mul : 128 → 32 → 128   @[extern "lean_hazmat_bn254_g2_mul"]
// The EIP-197 G2 scalar-multiplication primitive.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_g2_mul(
    b_lean_obj_arg a_arr, b_lean_obj_arg k_arr)
{
    if (!bn254_ready()) return mk_error();
    if (lean_sarray_size(a_arr) != G2_LEN) return mk_error();
    if (lean_sarray_size(k_arr) != SCALAR_LEN) return mk_error();

    mclBnG2 a, r;
    mclBnFr k;
    if (!g2_from_bytes(&a, lean_sarray_cptr(a_arr))) return mk_error();
    if (mclBnFr_setBigEndianMod(&k, lean_sarray_cptr(k_arr),
                                SCALAR_LEN) != 0)
        return mk_error();
    mclBnG2_mul(&r, &a, &k);

    uint8_t out[G2_LEN];
    if (!g2_to_bytes(out, r)) return mk_error();
    return mk_bytearray(out, G2_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// millerLoopVec : Array ByteArray(64) → Array ByteArray(128) → 384
//   @[extern "lean_hazmat_bn254_miller_loop_vec"]
// `prod_i millerLoop(g1s[i], g2s[i])` in GT, mcl's own batched form.
// The two arrays must share one length; an empty pair set answers the
// GT identity (so the EIP-197 empty-input rule, pairing of zero
// pairs is one, composes naturally). Empty ByteArray on any bad
// length or invalid point.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_miller_loop_vec(
    b_lean_obj_arg g1s_arr, b_lean_obj_arg g2s_arr)
{
    if (!bn254_ready()) return mk_error();
    const size_t n = lean_array_size(g1s_arr);
    if (lean_array_size(g2s_arr) != n) return mk_error();

    mclBnG1 *g1s = NULL;
    mclBnG2 *g2s = NULL;
    bool ok = false;
    uint8_t buf[GT_LEN];
    if (n > 0) {
        g1s = (mclBnG1 *)calloc(n, sizeof(mclBnG1));
        g2s = (mclBnG2 *)calloc(n, sizeof(mclBnG2));
        if (!g1s || !g2s) goto done;
        for (size_t i = 0; i < n; i++) {
            lean_object *a = lean_array_get_core(g1s_arr, i);
            lean_object *b = lean_array_get_core(g2s_arr, i);
            if (lean_sarray_size(a) != G1_LEN) goto done;
            if (lean_sarray_size(b) != G2_LEN) goto done;
            if (!g1_from_bytes(&g1s[i], lean_sarray_cptr(a))) goto done;
            if (!g2_from_bytes(&g2s[i], lean_sarray_cptr(b))) goto done;
        }
    }

    {
        mclBnGT z;
        mclBn_millerLoopVec(&z, g1s, g2s, n);
        ok = gt_to_bytes(buf, z);
    }

done:
    free(g1s);
    free(g2s);
    // The result is allocated exactly once, on the success path; no
    // Lean object is ever dropped or double-released on an error path.
    if (!ok) return mk_error();
    return mk_bytearray(buf, GT_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// finalExp : 384 → 384   @[extern "lean_hazmat_bn254_final_exp"]
// The pairing's final exponentiation. Empty ByteArray on a bad length.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT lean_obj_res lean_hazmat_bn254_final_exp(
    b_lean_obj_arg gt_arr)
{
    if (!bn254_ready()) return mk_error();
    if (lean_sarray_size(gt_arr) != GT_LEN) return mk_error();

    mclBnGT x, y;
    if (!gt_from_bytes(&x, lean_sarray_cptr(gt_arr))) return mk_error();
    mclBn_finalExp(&y, &x);

    uint8_t out[GT_LEN];
    if (!gt_to_bytes(out, y)) return mk_error();
    return mk_bytearray(out, GT_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// gtIsOne : 384 → Bool   @[extern "lean_hazmat_bn254_gt_is_one"]
// The pairing-check predicate: the EIP-197 check is
// `gtIsOne (finalExp (millerLoopVec …))`. `false` covers every
// malformed input.
// ─────────────────────────────────────────────────────────────────────
extern "C" LEAN_EXPORT uint8_t lean_hazmat_bn254_gt_is_one(
    b_lean_obj_arg gt_arr)
{
    if (!bn254_ready()) return 0;
    if (lean_sarray_size(gt_arr) != GT_LEN) return 0;

    mclBnGT x;
    if (!gt_from_bytes(&x, lean_sarray_cptr(gt_arr))) return 0;
    return mclBnGT_isOne(&x) ? 1 : 0;
}
