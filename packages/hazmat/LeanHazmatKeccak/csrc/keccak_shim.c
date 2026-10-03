// LeanHazmatKeccak: C shim wrapping the vendored coruus/keccak-tiny
// for the Ethereum execution-layer Keccak-256 primitive.
//
// Ethereum's Keccak-256 is **not** SHA3-256: the padding byte is 0x01
// (the original Keccak padding), not FIPS 202's 0x06, so OpenSSL's
// SHA3 functions and keccak-tiny's `sha3_256` both compute the wrong
// function for the EVM. keccak-tiny's generic sponge, the static
//   hash(out, outlen, in, inlen, rate, delim)
// in the vendored file, takes the delimiter as a parameter, which is
// exactly what Keccak-256 needs: rate 136 (200 - 2*32), delim 0x01.
//
// That sponge is `static`, so this translation unit **#includes the
// vendored keccak-tiny.c unmodified** to reach it, then adds the
// Keccak-256 wrapper. The lakefile compiles this one file (and traces
// the vendored source's content), so the vendored code stays
// byte-identical to the pin and the archive still carries a single
// object.
//
// One portability patch, applied here rather than by editing the
// vendored file: keccak-tiny calls C11 Annex K `memset_s`, which glibc
// does not provide. `memset` is semantically sufficient here (the
// buffer is the scratch state, always fully overwritten, and the
// lengths match), so `memset_s` is macro-mapped to it before the
// include.
//
// Symbol hygiene: the vendored file also defines non-static FIPS
// functions (`sha3_256`, `shake128`, ...) this family never uses. Left
// alone they would collide with a consumer's other libraries at link
// time, so they are macro-renamed into this package's namespace before
// the include.
//
// Endianness: the vendored code and the shim read and write the
// sponge state as little-endian 64-bit words; a big-endian host is
// rejected at compile time rather than miscomputed.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): the vendored
// keccak-tiny (rev 64b6647514212b76ae7bca0dea9b7b197d1d8186) correctly
// implements the Keccak-f[1600] permutation and the sponge, and that
// Keccak-256 (0x01 padding, rate 136) is what this file asks it for.
// No pure-Lean reference exists; validated only against published
// Keccak-256 vectors (LeanHazmatKeccakTests), including the EVM's
// canonical constants (the empty-input digest and the empty trie
// root).

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <lean/lean.h>

// glibc has no C11 Annex K `memset_s`; `memset` is sufficient for this
// scratch-state clear (see the header comment).
#define memset_s(s, smax, c, n) memset((s), (c), (n))

// The endianness guard must sit before the include (the header
// comment's Endianness paragraph says why).
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && \
    (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#error "LeanHazmatKeccak: little-endian hosts only"
#endif

// The FIPS entry points rename out of the way before the include (the
// header comment's symbol-hygiene paragraph says why).
#define sha3_224 lean_hazmat_keccak_unused_sha3_224
#define sha3_256 lean_hazmat_keccak_unused_sha3_256
#define sha3_384 lean_hazmat_keccak_unused_sha3_384
#define sha3_512 lean_hazmat_keccak_unused_sha3_512
#define shake128 lean_hazmat_keccak_unused_shake128
#define shake256 lean_hazmat_keccak_unused_shake256

// The vendored single-file implementation (unmodified). Brings the
// static Keccak-f[1600] permutation `keccakf` and the static sponge
// `hash` into this translation unit.
#include "keccak-tiny.c"

// Fresh Lean `ByteArray` of length `n` with `src` copied in.
static inline lean_obj_res mk_bytearray(const uint8_t *src, size_t n) {
    lean_object *arr = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(arr), src, n);
    return arr;
}

// The empty-ByteArray error sentinel (same helper the sibling shims use).
static inline lean_obj_res mk_error(void) {
    return lean_alloc_sarray(1, 0, 0);
}

// ─────────────────────────────────────────────────────────────────────
// keccak256 : ByteArray → ByteArray (32)
//   @[extern "lean_hazmat_keccak256_hash"]
// The execution-layer Keccak-256: rate 136, original Keccak padding
// (delim 0x01), 32-byte digest. Returns the empty ByteArray if the
// sponge reports an error (only possible for a NULL input, which a
// Lean ByteArray never is).
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_keccak256_hash(
    b_lean_obj_arg in_arr)
{
    const uint8_t *in = lean_sarray_cptr(in_arr);
    size_t in_len = lean_sarray_size(in_arr);

    uint8_t out[32];
    if (hash(out, sizeof(out), in, in_len,
             /*rate=*/136, /*delim=*/0x01) != 0) {
        return mk_error();
    }
    return mk_bytearray(out, sizeof(out));
}
