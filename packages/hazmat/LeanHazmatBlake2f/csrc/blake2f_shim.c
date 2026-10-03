// LeanHazmatBlake2f: in-repo C shim implementing the BLAKE2b `F`
// compression function for the Ethereum execution-layer BLAKE2f
// precompile (EIP-152).
//
// This family has **no vendored library** behind it: EIP-152 needs the
// rounds-parametrized `F(h, m, t0, t1, f, rounds)` primitive itself
// (arbitrary `rounds`, the final-block flag), which no standard BLAKE2
// library exposes (libb2 / OpenSSL surface a blake2b *hash API*, never
// raw `F`). The function is small (~60 lines of RFC 7693 sections
// 3.1-3.2), so it is written here, in this file, and validated
// against the official EIP-152 test vectors (LeanHazmatBlake2fTests).
//
// `F` operates on the BLAKE2b state:
//   * `h` : 64 bytes, the 8-word chaining state (little-endian u64s),
//   * `m` : 128 bytes, the message block (little-endian u64s),
//   * `t0`, `t1` : the 128-bit offset counter,
//   * `f` : the final-block flag,
//   * `rounds` : the number of rounds (0 .. 0xffffffff; the sigma
//     schedule cycles with period 10).
// It returns the updated 64-byte state `h` in place (copied into a
// fresh Lean `ByteArray`).
//
// Every entry point the Lean side declares `@[extern]` lives here
// (LeanHazmatBlake2f/Ffi.lean). Byte inputs are borrowed
// (`b_lean_obj_arg` = `@&`); we do not touch their refcounts. An
// *empty* `ByteArray` is the error sentinel (wrong `h` / `m` length).
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): this file
// implements RFC 7693's `F` correctly. There is no pure-Lean reference
// and no third-party library; the EIP-152 vectors are the *entire*
// validation surface (LeanHazmatBlake2fTests), which is exactly why
// the function is kept this small.

#include <stddef.h>
#include <stdint.h>
#include <string.h>

// The shim decodes and encodes the state and message words with
// little-endian `memcpy`s; a big-endian host is rejected at compile
// time rather than miscomputed.
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && \
    (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#error "LeanHazmatBlake2f: little-endian hosts only"
#endif

#include <lean/lean.h>

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
// RFC 7693 section 3.1: the `G` mixing function; the schedule is the
// SIGMA table in section 2.7.
// ─────────────────────────────────────────────────────────────────────

// The BLAKE2b initialization vector (RFC 7693 section 2.6, the first
// 512 bits of the SHA-512 IV, in BLAKE2's little-endian word order).
static const uint64_t blake2b_iv[8] = {
    0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL,
    0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
    0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
    0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL,
};

// The ten-round permutation schedule (RFC 7693 section 2.7). `F`
// indexes it `sigma[r % 10]`, so any `rounds` count is covered.
static const uint8_t blake2b_sigma[10][16] = {
    { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
    { 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
    { 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
    { 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
    { 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
    { 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
    { 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
    { 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
    { 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
    { 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
};

#define ROTR64(x, n) (((x) >> (n)) | ((x) << (64 - (n))))

// One `G` mixing round over working-vector words `a b c d` with message
// words `x y` (RFC 7693 section 3.1, in the 8-quarter-round shape the
// BLAKE2 reference code uses).
#define B2B_G(a, b, c, d, x, y)                                  \
    do {                                                         \
        v[a] = v[a] + v[b] + (x);                                \
        v[d] = ROTR64(v[d] ^ v[a], 32);                          \
        v[c] = v[c] + v[d];                                      \
        v[b] = ROTR64(v[b] ^ v[c], 24);                          \
        v[a] = v[a] + v[b] + (y);                                \
        v[d] = ROTR64(v[d] ^ v[a], 16);                          \
        v[c] = v[c] + v[d];                                      \
        v[b] = ROTR64(v[b] ^ v[c], 63);                          \
    } while (0)

// The `F` compression: 16-word working vector, `rounds` rounds over the
// sigma schedule, XOR feed-forward into `h`. Writes the new state to
// `out` (64 bytes). `h` and `m` must be 64 / 128 bytes (checked by the
// caller); both are read as little-endian u64 words.
static void blake2f_compress(uint8_t out[64], const uint8_t h64[64],
                             const uint8_t m128[128], uint64_t t0,
                             uint64_t t1, uint8_t last, uint32_t rounds) {
    uint64_t v[16];
    uint64_t m[16];

    for (size_t i = 0; i < 16; i++)
        memcpy(&m[i], m128 + 8 * i, 8);  // little-endian host decode
    for (size_t i = 0; i < 8; i++)
        memcpy(&v[i], h64 + 8 * i, 8);
    for (size_t i = 0; i < 8; i++)
        v[8 + i] = blake2b_iv[i];
    v[12] ^= t0;
    v[13] ^= t1;
    if (last) v[14] = ~v[14];

    for (uint32_t r = 0; r < rounds; r++) {
        const uint8_t *s = blake2b_sigma[r % 10];
        B2B_G(0, 4, 8, 12, m[s[0]],  m[s[1]]);
        B2B_G(1, 5, 9, 13, m[s[2]],  m[s[3]]);
        B2B_G(2, 6, 10, 14, m[s[4]], m[s[5]]);
        B2B_G(3, 7, 11, 15, m[s[6]], m[s[7]]);
        B2B_G(0, 5, 10, 15, m[s[8]], m[s[9]]);
        B2B_G(1, 6, 11, 12, m[s[10]], m[s[11]]);
        B2B_G(2, 7, 8, 13, m[s[12]], m[s[13]]);
        B2B_G(3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    for (size_t i = 0; i < 8; i++) {
        uint64_t hi;
        memcpy(&hi, h64 + 8 * i, 8);
        hi ^= v[i] ^ v[8 + i];
        memcpy(out + 8 * i, &hi, 8);  // little-endian host encode
    }
}

#define H_LEN 64   // chaining state: 8 u64 words
#define M_LEN 128  // message block: 16 u64 words

// ─────────────────────────────────────────────────────────────────────
// blake2fCompress : rounds(u32) → h(64) → m(128) → t0(u64) → t1(u64)
//                   → f(Bool) → ByteArray(64)
//   @[extern "lean_hazmat_blake2f_compress"]
// The raw EIP-152 `F` primitive. Returns the empty ByteArray if `h` or
// `m` has the wrong length (the caller's parsing is its own concern).
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_blake2f_compress(
    uint32_t rounds, b_lean_obj_arg h_arr, b_lean_obj_arg m_arr,
    uint64_t t0, uint64_t t1, uint8_t last)
{
    if (lean_sarray_size(h_arr) != H_LEN) return mk_error();
    if (lean_sarray_size(m_arr) != M_LEN) return mk_error();

    uint8_t out[H_LEN];
    blake2f_compress(out, lean_sarray_cptr(h_arr), lean_sarray_cptr(m_arr),
                     t0, t1, last ? 1 : 0, rounds);
    return mk_bytearray(out, H_LEN);
}
