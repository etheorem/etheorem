// LeanHazmatSecp256k1: C shim wrapping the vendored bitcoin-core
// libsecp256k1 for the Ethereum execution-layer ECDSA primitives.
//
// Surface (raw primitives, per packages/hazmat/docs/ARCHITECTURE.md §4):
//   * ecdsaRecover : (msgHash, r, s, recId) → 64-byte public key
//     (uncompressed x ‖ y, big-endian), the primitive behind the
//     ecRecover precompile (0x01) and transaction sender recovery.
//     The precompile *output* (keccak256(pubkey)[12:32]) stays with
//     the caller: address derivation is the caller's composition, and
//     this package deliberately does not depend on LeanHazmatKeccak.
//   * ecdsaVerify : (msgHash, r, s, pubkey) → Bool, plain ECDSA
//     verification against a 64-byte uncompressed public key.
//
// The library is vendored (`just hazmat-secp256k1-vendor`, pinned tag
// v0.8.0, gitignored `vendor/secp256k1/`); the build stays offline.
// The lakefile compiles the library's own amalgamation
// (`src/secp256k1.c`, which #includes every other `.c`) with
// `-DENABLE_MODULE_RECOVERY` (the recovery module is a compile-time
// module gate in v0.8.0). It deliberately passes NO
// `-DSECP256K1_BUILD`: the amalgamation defines that itself before
// including the public header, and a command-line copy only produces
// a `"SECP256K1_BUILD" redefined` warning.
//
// Context handling: `secp256k1_context_static`, recover and verify
// need no precomputed signing tables and no randomization, and the
// static context is thread-safe and free to obtain. The library asks
// callers of the static context to run `secp256k1_selftest` first;
// both entry points do so once per process (under `pthread_once`: the
// check is pure, so the first caller's result serves all later ones).
//
// Every entry point the Lean side declares `@[extern]` lives here
// (LeanHazmatSecp256k1/Ffi.lean). Byte inputs are borrowed
// (`b_lean_obj_arg` = `@&`); we do not touch their refcounts. The
// point result is returned as a freshly-allocated 64-byte `ByteArray`;
// an *empty* `ByteArray` is the error sentinel (wrong length, signature
// not parseable, recovery failure, e.g. an invalid signature). Boolean
// results are returned as `uint8_t` (Lean `Bool`): 0 = false, 1 = true.
// Verification failure is a legitimate `false`, never a panic.
//
// Trust assumption (packages/hazmat/docs/ARCHITECTURE.md §10): libsecp256k1
// correctly implements secp256k1 ECDSA public-key recovery and
// verification. There is no pure-Lean reference for this primitive, it
// is an opaque FFI boundary, validated only against the published
// vectors in LeanHazmatSecp256k1Tests (the EIP-155 example transaction
// and a deterministic second signature).

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <lean/lean.h>
#include <pthread.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>

#define HASH_LEN  32  // message hash
#define SCALAR_LEN 32  // r and s, big-endian
#define PK_LEN    64  // uncompressed public key, x ‖ y

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

// Run the library self-test once, from any thread (`pthread_once`).
// `pthread_once` resolves from libc on glibc 2.34 and later (and on
// musl and macOS); on older glibc it lives in libpthread, so the
// package's lakefile adds `-lpthread` to this package's own test-lib
// link.
// The self-test calls the error callback and aborts on failure, so
// returning normally means the run passed. Recovery and verification
// run on `secp256k1_context_static` (no signing tables, no
// randomization needed).
static void secp_selftest_once(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, secp256k1_selftest);
}

// Parse `r ‖ s` (two big-endian 32-byte scalars) into a compact
// recoverable signature. The callers check the ByteArray lengths and
// the `rec_id <= 3` guard first: inside the library a bad `rec_id` is
// an `ARG_CHECK`, which fires the illegal-argument callback and aborts
// the process, and an out-of-range scalar zero-fills `sig` and returns
// 0. The entry-point guard is what keeps the abort path unreachable,
// so do not remove it as redundant.
static int parse_sig(secp256k1_ecdsa_recoverable_signature *sig,
                     const uint8_t *r, const uint8_t *s, uint32_t rec_id) {
    uint8_t compact[2 * SCALAR_LEN];
    memcpy(compact, r, SCALAR_LEN);
    memcpy(compact + SCALAR_LEN, s, SCALAR_LEN);
    return secp256k1_ecdsa_recoverable_signature_parse_compact(
        secp256k1_context_static, sig, compact, (int)rec_id);
}

// ─────────────────────────────────────────────────────────────────────
// ecdsaRecover : msgHash(32) → r(32) → s(32) → recId(u32) → ByteArray(64)
//   @[extern "lean_hazmat_secp256k1_ecdsa_recover"]
// Recover the public key from a compact ECDSA signature. `recId` is
// the recovery id, 0-3: bit 0 is the y-coordinate parity of `R`, bit 1
// flags an r-overflow (never occurs for a valid signature, since
// r < curve order). The EL transaction `v` maps to `recId` in the
// caller: legacy `v ∈ {27, 28}` → `recId = v - 27`; EIP-155
// `v = chain_id * 2 + 35 + parity` → `recId = (v - 35) mod 2`.
// Returns the empty ByteArray on any failure.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT lean_obj_res lean_hazmat_secp256k1_ecdsa_recover(
    b_lean_obj_arg msg_arr, b_lean_obj_arg r_arr, b_lean_obj_arg s_arr,
    uint32_t rec_id)
{
    secp_selftest_once();
    if (lean_sarray_size(msg_arr) != HASH_LEN)   return mk_error();
    if (lean_sarray_size(r_arr) != SCALAR_LEN)   return mk_error();
    if (lean_sarray_size(s_arr) != SCALAR_LEN)   return mk_error();
    if (rec_id > 3)                              return mk_error();

    secp256k1_ecdsa_recoverable_signature sig;
    if (!parse_sig(&sig, lean_sarray_cptr(r_arr), lean_sarray_cptr(s_arr),
                   rec_id))
        return mk_error();

    secp256k1_pubkey pubkey;
    if (!secp256k1_ecdsa_recover(secp256k1_context_static, &pubkey,
                                 &sig, lean_sarray_cptr(msg_arr)))
        return mk_error();

    // Serialize uncompressed (0x04 ‖ x ‖ y, big-endian) and drop the
    // 0x04 prefix: the raw primitive is the 64-byte x ‖ y key.
    uint8_t out65[65];
    size_t out_len = sizeof(out65);
    if (!secp256k1_ec_pubkey_serialize(secp256k1_context_static, out65,
                                       &out_len, &pubkey,
                                       SECP256K1_EC_UNCOMPRESSED) ||
        out_len != 65)
        return mk_error();
    return mk_bytearray(out65 + 1, PK_LEN);
}

// ─────────────────────────────────────────────────────────────────────
// ecdsaVerify : msgHash(32) → r(32) → s(32) → pk(64) → Bool
//   @[extern "lean_hazmat_secp256k1_ecdsa_verify"]
// Verify a compact ECDSA signature against a 64-byte uncompressed
// public key. Any malformed input or failed verification is `false`.
// ─────────────────────────────────────────────────────────────────────
LEAN_EXPORT uint8_t lean_hazmat_secp256k1_ecdsa_verify(
    b_lean_obj_arg msg_arr, b_lean_obj_arg r_arr, b_lean_obj_arg s_arr,
    b_lean_obj_arg pk_arr)
{
    secp_selftest_once();
    if (lean_sarray_size(msg_arr) != HASH_LEN) return 0;
    if (lean_sarray_size(r_arr) != SCALAR_LEN) return 0;
    if (lean_sarray_size(s_arr) != SCALAR_LEN) return 0;
    if (lean_sarray_size(pk_arr) != PK_LEN)    return 0;

    // libsecp256k1's `secp256k1_ecdsa_verify` rejects signatures with
    // s > n/2 (Bitcoin's anti-malleability policy). The execution layer
    // has no such policy for the raw primitive: (r, s) and (r, n - s)
    // have identical validity. `secp256k1_ecdsa_signature_normalize`
    // maps a high s to its low form in place, so the library's own
    // normalization replaces any policy here.
    secp256k1_ecdsa_signature sig, sig_low;
    uint8_t compact[2 * SCALAR_LEN];
    memcpy(compact, lean_sarray_cptr(r_arr), SCALAR_LEN);
    memcpy(compact + SCALAR_LEN, lean_sarray_cptr(s_arr), SCALAR_LEN);
    if (!secp256k1_ecdsa_signature_parse_compact(
            secp256k1_context_static, &sig, compact))
        return 0;
    secp256k1_ecdsa_signature_normalize(secp256k1_context_static,
                                        &sig_low, &sig);

    // Rebuild the 0x04-prefixed encoding the parser expects.
    uint8_t pk65[65];
    pk65[0] = 0x04;
    memcpy(pk65 + 1, lean_sarray_cptr(pk_arr), PK_LEN);
    secp256k1_pubkey pubkey;
    if (!secp256k1_ec_pubkey_parse(secp256k1_context_static, &pubkey,
                                   pk65, sizeof(pk65)))
        return 0;

    return secp256k1_ecdsa_verify(secp256k1_context_static, &sig_low,
                                  lean_sarray_cptr(msg_arr),
                                  &pubkey) ? 1 : 0;
}
