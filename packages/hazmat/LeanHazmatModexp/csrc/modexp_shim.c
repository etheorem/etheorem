// LeanHazmatModexp: C shim wrapping the system OpenSSL libcrypto
// (BIGNUM) for the execution-layer modexp primitive (precompile 0x05,
// EIP-198, gas via EIP-2565/7883).
//
// The primitive is raw modular exponentiation over big-endian byte
// strings:
//   modExp(base, exponent, modulus) → (base ** exponent) mod modulus
// OpenSSL's `BN_mod_exp` does the arithmetic; `BN_bin2bn` /
// `BN_bn2bin` convert at the boundary. Per packages/hazmat/docs/ARCHITECTURE.md
// §4, everything around the exponentiation is the caller's job: the
// EIP-198 length-prefixed input parse, the right-padding / truncation
// rules, the gas schedule, and left-padding the result to the
// modulus's length. The output here is `BN_bn2bin`'s minimal
// big-endian form (no leading zero bytes); a zero result is the single
// zero byte `00`.
//
// Special cases, following the arithmetic (the EIP's own parse rules
// are above this layer):
//   * modulus 0 → failure (the empty ByteArray): a reduction mod 0 is
//     undefined, and BN_mod_exp reports an error.
//   * exponent 0 → 1 mod modulus (BN_mod_exp's answer; for modulus 1
//     that is the single zero byte `00`).
//   * zero result → the single zero byte `00` (the minimal big-endian
//     form; an *empty* output stays reserved for the error sentinel).
//
// Note the inputs here are *exact* byte strings: `BN_bin2bn` converts
// every byte it is given, so the EIP-198 "excess data is ignored" and
// right-padding rules are the caller's parse, not this primitive's.
//
// Every entry point the Lean side declares `@[extern]` lives here
// (LeanHazmatModexp/Ffi.lean). Inputs are borrowed (`b_lean_obj_arg`
// = `@&`); the result is a freshly-allocated `ByteArray`; an *empty*
// `ByteArray` is the error sentinel.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): the linked
// OpenSSL libcrypto implements modular exponentiation correctly.
// There is no pure-Lean reference; validated only against the
// EIP-198 worked examples plus fixed modular-arithmetic cases
// (LeanHazmatModexpTests), the latter cross-checked against Python's
// `pow` at authoring time.

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <limits.h>
#include <stdlib.h>

#include <lean/lean.h>
#include <openssl/bn.h>
#include <openssl/err.h>

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
// modExp : base → exponent → modulus → ByteArray
//   @[extern "lean_hazmat_modexp"]
// The inputs are exact big-endian byte strings, leading zeros included
// (`BN_bin2bn` converts every byte it is given). The result is minimal
// big-endian (`BN_bn2bin` never emits leading zeros). Empty ByteArray
// on failure: an input above INT_MAX bytes, a zero modulus, or a
// BIGNUM allocation / exponentiation error.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_modexp(
    b_lean_obj_arg base_arr, b_lean_obj_arg exp_arr,
    b_lean_obj_arg mod_arr)
{
    // `BN_bin2bn` takes an `int` length, and `lean_sarray_size` is
    // `size_t`. Reject lengths above `INT_MAX` instead of truncating
    // (a wrapped length would produce a wrong answer, not an error).
    size_t nb = lean_sarray_size(base_arr);
    size_t ne = lean_sarray_size(exp_arr);
    size_t nm = lean_sarray_size(mod_arr);
    if (nb > (size_t)INT_MAX ||
        ne > (size_t)INT_MAX ||
        nm > (size_t)INT_MAX) return mk_error();

    // Every OpenSSL call below can queue an error on the *thread's*
    // error queue when it fails (the queue is per-thread, not
    // per-anything-else), and precompile input reaches the failure
    // paths at will; a later libcrypto consumer on this thread must
    // not read our stale entries. Mark / pop removes exactly what
    // this call added, leaving any earlier unread errors alone. The
    // length guards above queue nothing, so they stay before the mark.
    ERR_set_mark();

    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *b = ctx ? BN_bin2bn(lean_sarray_cptr(base_arr), (int)nb, NULL) : NULL;
    BIGNUM *e = ctx ? BN_bin2bn(lean_sarray_cptr(exp_arr), (int)ne, NULL) : NULL;
    BIGNUM *m = ctx ? BN_bin2bn(lean_sarray_cptr(mod_arr), (int)nm, NULL) : NULL;
    BIGNUM *r = BN_new();

    lean_obj_res out = NULL;
    int n = 0;
    if (b && e && m && r &&
        !BN_is_zero(m) &&
        BN_mod_exp(r, b, e, m, ctx)) {
        n = BN_num_bytes(r);
        if (n == 0) {
            // Minimal big-endian zero is the single byte 0x00
            // (BN_bn2bin writes nothing for zero, and an empty output
            // must stay reserved for the error sentinel).
            uint8_t zero = 0;
            out = mk_bytearray(&zero, 1);
        } else {
            uint8_t *buf = (uint8_t *)malloc((size_t)n);
            if (buf) {
                int written = BN_bn2bin(r, buf);  // exactly n bytes
                if (written == n)
                    out = mk_bytearray(buf, (size_t)n);
                free(buf);
            }
        }
    }

    BN_free(b); BN_free(e); BN_free(m); BN_free(r);
    BN_CTX_free(ctx);
    ERR_pop_to_mark();
    // The result is allocated exactly once, on the success path; no
    // Lean object is ever dropped or double-released on an error path.
    if (!out) return mk_error();
    return out;
}
